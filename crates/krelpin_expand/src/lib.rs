mod cfg;
mod invoke;
mod item;
mod proc_macro;
mod server;
mod table;

#[cfg(test)]
mod tests;

use std::cell::RefCell;

use krelpin_ast::ast::{Annotation, CompilationUnit, Ident, Item, ItemKind, Member, MemberKind};
use krelpin_errors::{DiagCtxt, Diagnostic};
use krelpin_parse::parser::Container;
use krelpin_span::{SourceMap, Span};

pub use crate::cfg::{CfgSet, WELL_KNOWN};
pub use crate::proc_macro::{CallError, ProcMacroCrate, WireKind, WireToken};
use crate::table::{MacroKind, MacroScope, MacroTable};

const BUILTIN_ATTRIBUTES: &[&str] = &["Intrinsic", "Override", "Test"];
const RECURSION_LIMIT: usize = 64;

pub struct ExpandOptions<'a> {
    pub cfg: &'a CfgSet,
    pub proc_macro: Option<&'a str>,
    pub externs: &'a [ProcMacroCrate],
    /// The index of the first unit of the crate being built; the units
    /// before it are the standard library and the source libraries.
    pub first_user: usize,
}

pub fn expand(units: &mut [CompilationUnit], source_map: &SourceMap, dcx: &DiagCtxt) {
    let options = ExpandOptions {
        cfg: &CfgSet::default(),
        proc_macro: None,
        externs: &[],
        first_user: 0,
    };
    expand_crate(units, source_map, dcx, &options);
}

pub fn expand_crate(
    units: &mut [CompilationUnit],
    source_map: &SourceMap,
    dcx: &DiagCtxt,
    options: &ExpandOptions<'_>,
) {
    let config = Configure {
        cfg: options.cfg,
        dcx,
        removed: RefCell::default(),
    };
    for unit in units.iter_mut() {
        config.items(&mut unit.items);
    }
    let table = MacroTable::collect(units, options.externs, options.proc_macro.is_some(), dcx);
    for unit in units.iter_mut() {
        let scope = MacroScope::new(&table, unit);
        unit.imports.retain(|import| !scope.is_macro_import(import));
        let cx = ExpandCtxt {
            scope,
            source_map,
            dcx,
            config: &config,
            externs: options.externs,
        };
        let items = std::mem::take(&mut unit.items);
        unit.items = cx.expand_items(items, 0);
        for def in &mut unit.macros {
            cx.reject_macros(&mut def.annotations, "macros");
        }
    }
    server::define_macros(
        units,
        source_map,
        dcx,
        options.proc_macro,
        options.first_user,
    );
}

pub(crate) struct Invocation {
    kind: MacroKind,
    annotation: Annotation,
}

impl Invocation {
    fn usage(&self) -> &'static str {
        "macros can be used on classes, records, enums, interfaces and their members"
    }
}

pub(crate) struct ExpandCtxt<'a> {
    scope: MacroScope<'a>,
    source_map: &'a SourceMap,
    dcx: &'a DiagCtxt,
    config: &'a Configure<'a>,
    externs: &'a [ProcMacroCrate],
}

impl ExpandCtxt<'_> {
    fn expand_items(&self, items: Vec<Item>, depth: usize) -> Vec<Item> {
        let mut out = Vec::new();
        for item in items {
            self.expand_item(item, depth, &mut out);
        }
        out
    }

    fn expand_item(&self, mut item: Item, depth: usize, out: &mut Vec<Item>) {
        if let Some(invocation) = self.next_user_macro(&mut item.annotations) {
            let Some(tokens) = self.invoke(&invocation, &item.tokens, item.name, depth) else {
                return;
            };
            let mut items = krelpin_parse::parser::parse_items(tokens, self.dcx);
            self.config.items(&mut items);
            for item in items {
                self.expand_item(item, depth + 1, out);
            }
            return;
        }
        self.expand_in_place(&mut item, depth);
        out.push(item);
    }

    fn expand_in_place(&self, item: &mut Item, depth: usize) {
        let owner = item.name;
        let (container, members): (Container, &mut Vec<Member>) = match &mut item.kind {
            ItemKind::Class(class) => (Container::Class, &mut class.members),
            ItemKind::Record(def) => (Container::Record, &mut def.members),
            ItemKind::Interface(interface) => (Container::Interface, &mut interface.members),
            ItemKind::Enum(def) => {
                for variant in &mut def.variants {
                    self.reject_macros(&mut variant.annotations, "enum variants");
                }
                (Container::Enum, &mut def.members)
            }
        };
        let taken = std::mem::take(members);
        *members = self.expand_members(taken, container, owner, depth);
    }

    fn expand_members(
        &self,
        members: Vec<Member>,
        container: Container,
        owner: Ident,
        depth: usize,
    ) -> Vec<Member> {
        let mut out = Vec::new();
        for member in members {
            self.expand_member(member, container, owner, depth, &mut out);
        }
        out
    }

    fn expand_member(
        &self,
        mut member: Member,
        container: Container,
        owner: Ident,
        depth: usize,
        out: &mut Vec<Member>,
    ) {
        let invocation = match &mut member.kind {
            MemberKind::Type(item) => self.next_user_macro(&mut item.annotations),
            _ => self.next_user_macro(&mut member.annotations),
        };
        if let Some(invocation) = invocation {
            let (tokens, name) = match &member.kind {
                MemberKind::Type(item) => (&item.tokens, item.name),
                _ => (&member.tokens, owner),
            };
            let Some(tokens) = self.invoke(&invocation, tokens, name, depth) else {
                return;
            };
            let mut members =
                krelpin_parse::parser::parse_members_of(tokens, container, owner, self.dcx);
            self.config.members(&mut members);
            for member in members {
                self.expand_member(member, container, owner, depth + 1, out);
            }
            return;
        }
        match &mut member.kind {
            MemberKind::Type(item) => self.expand_in_place(item, depth),
            _ => self.reject_macros(&mut member.annotations, "members"),
        }
        out.push(member);
    }

    fn next_user_macro(&self, annotations: &mut Vec<Annotation>) -> Option<Invocation> {
        let mut found = None;
        let mut index = 0;
        while index < annotations.len() {
            let annotation = &annotations[index];
            if is_builtin_attribute(annotation) {
                index += 1;
                continue;
            }
            match self.scope.resolve(&annotation.path) {
                Some(kind @ MacroKind::Extern { .. }) => {
                    found = Some(Invocation {
                        kind,
                        annotation: annotations.remove(index),
                    });
                    break;
                }
                Some(MacroKind::Local { name }) => {
                    self.emit(
                        Diagnostic::error(format!(
                            "the macro `{name}` cannot be used in the crate that defines it"
                        ))
                        .with_span(annotation.path.span)
                        .with_note("macros run while the crate that uses them is compiled")
                        .with_help("use it from another crate with `--extern`"),
                    );
                    annotations.remove(index);
                }
                None => {
                    self.not_found(annotation);
                    annotations.remove(index);
                }
            }
        }
        found
    }

    fn reject_macros(&self, annotations: &mut Vec<Annotation>, target: &str) {
        for invocation in self.take_invocations(annotations) {
            self.misplaced(&invocation, target);
        }
    }

    fn take_invocations(&self, annotations: &mut Vec<Annotation>) -> Vec<Invocation> {
        let mut invocations = Vec::new();
        annotations.retain(|annotation| {
            if is_builtin_attribute(annotation) {
                return true;
            }
            match self.scope.resolve(&annotation.path) {
                Some(kind) => invocations.push(Invocation {
                    kind,
                    annotation: annotation.clone(),
                }),
                None => self.not_found(annotation),
            }
            false
        });
        invocations
    }

    fn not_found(&self, annotation: &Annotation) {
        self.emit(
            Diagnostic::error(format!(
                "cannot find macro `{}` in this scope",
                annotation.path
            ))
            .with_span(annotation.path.span)
            .with_label("not found in this scope"),
        );
    }

    fn emit(&self, diagnostic: Diagnostic) {
        self.dcx.emit(diagnostic);
    }
}

pub(crate) struct Configure<'a> {
    cfg: &'a CfgSet,
    dcx: &'a DiagCtxt,
    removed: RefCell<Removed>,
}

#[derive(Default)]
pub(crate) struct Removed {
    pub(crate) annotations: Vec<Span>,
    pub(crate) members: Vec<Span>,
}

impl Configure<'_> {
    fn annotations(&self, annotations: &mut Vec<Annotation>) -> bool {
        let mut keep = true;
        annotations.retain(|annotation| {
            if !annotation.is("Cfg") {
                return true;
            }
            keep &= self.cfg.evaluate(annotation, self.dcx);
            self.removed.borrow_mut().annotations.push(annotation.span);
            false
        });
        keep
    }

    fn items(&self, items: &mut Vec<Item>) {
        items.retain_mut(|item| {
            let keep = self.annotations(&mut item.annotations);
            if !keep {
                self.removed.borrow_mut().members.push(item.span);
            }
            keep
        });
        for item in items {
            self.item(item);
        }
    }

    fn item(&self, item: &mut Item) {
        let members: &mut Vec<Member> = match &mut item.kind {
            ItemKind::Class(class) => &mut class.members,
            ItemKind::Record(def) => &mut def.members,
            ItemKind::Interface(interface) => &mut interface.members,
            ItemKind::Enum(def) => &mut def.members,
        };
        self.members(members);
    }

    fn members(&self, members: &mut Vec<Member>) {
        members.retain_mut(|member| {
            let annotations = match &mut member.kind {
                MemberKind::Type(item) => &mut item.annotations,
                _ => &mut member.annotations,
            };
            let keep = self.annotations(annotations);
            if !keep {
                self.removed.borrow_mut().members.push(member.span);
            }
            keep
        });
        for member in members {
            if let MemberKind::Type(nested) = &mut member.kind {
                self.item(nested);
            }
        }
    }
}

fn is_builtin_attribute(annotation: &Annotation) -> bool {
    BUILTIN_ATTRIBUTES.iter().any(|&name| annotation.is(name))
}
