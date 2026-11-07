use krelpin_ast::ast::{self, Item, ItemKind, ReceiverKind, Visibility};
use krelpin_errors::Diagnostic;
use krelpin_span::def_id::DefId;

use crate::closure::{FnSig, instantiate};
use crate::param_env::ParamEnv;
use crate::sig::{AdtKind, MethodSig, Tcx};
use crate::ty::{Subst, Ty};

impl Tcx<'_> {
    pub(crate) fn check_inheritance(&self, def: DefId, item: &Item) {
        self.check_duplicate_methods(def);
        if !self.check_parents(def, item) {
            return;
        }
        self.check_overrides(def);
        self.check_abstract_methods_implemented(def);
        self.check_closeable_kind(def, item);
    }

    fn check_closeable_kind(&self, def: DefId, item: &Item) {
        let kind = match self.sig(def).kind {
            AdtKind::Record => "record",
            AdtKind::Enum => "enum",
            AdtKind::Class | AdtKind::Interface => return,
        };
        if !self.closes_itself(def) {
            return;
        }
        self.dcx.emit(
            Diagnostic::error(format!("a {kind} cannot be `AutoCloseable`"))
                .with_span(item.name.span)
                .with_note(format!(
                    "a {kind} is a value that is copied or moved, so it has no single owner to close it"
                ))
                .with_help("make it a class, or keep the resource in a class field"),
        );
    }

    /// Two methods or constructors of one type with the same name and
    /// parameter types can't be told apart by a call, whether or not one of
    /// them is static.
    fn check_duplicate_methods(&self, def: DefId) {
        let sig = self.sig(def);
        let mut groups: Vec<&[MethodSig]> = sig.methods.values().map(Vec::as_slice).collect();
        groups.push(&sig.ctors);
        for methods in groups {
            let own: Vec<&MethodSig> = methods.iter().filter(|m| m.owner == def).collect();
            for (index, later) in own.iter().enumerate() {
                let Some(earlier) = own[..index].iter().find(|m| same_signature(m, later)) else {
                    continue;
                };
                self.dcx.emit(
                    Diagnostic::error(format!(
                        "duplicate definitions of `{}` with the same parameter types",
                        later.name.name
                    ))
                    .with_span(later.name.span)
                    .with_label("redefined here")
                    .with_secondary(earlier.name.span, "first defined here")
                    .with_help("rename one of them or change its parameters"),
                );
            }
        }
    }

    fn check_parents(&self, def: DefId, item: &Item) -> bool {
        let (extends, implements): (Vec<&ast::Ty>, Vec<&ast::Ty>) = match &item.kind {
            ItemKind::Class(class) => (
                class.extends.iter().collect(),
                class.implements.iter().collect(),
            ),
            ItemKind::Record(def) => (Vec::new(), def.implements.iter().collect()),
            ItemKind::Interface(interface) => (interface.extends.iter().collect(), Vec::new()),
            ItemKind::Enum(def) => (Vec::new(), def.implements.iter().collect()),
        };
        let kind = self.sig(def).kind;
        let mut valid = true;

        for ty in extends {
            let Ty::Adt {
                def: parent, name, ..
            } = self.lower_ty(ty)
            else {
                continue;
            };
            let parent = self.sig(parent);
            let diagnostic = match (kind, parent.kind) {
                (AdtKind::Class, AdtKind::Class) if parent.is_final => {
                    Diagnostic::error(format!("cannot extend `{name}` because it is `final`"))
                }
                (AdtKind::Class, AdtKind::Class) | (AdtKind::Interface, AdtKind::Interface) => {
                    continue;
                }
                (AdtKind::Class, AdtKind::Interface) => {
                    Diagnostic::error("a class cannot extend an interface")
                        .with_label(format!("`{name}` is an interface"))
                        .with_help(format!("use `implements {name}` instead"))
                }
                (AdtKind::Interface, other) => {
                    Diagnostic::error("an interface can only extend interfaces")
                        .with_label(format!("`{name}` is {}", article(other)))
                }
                (_, other) => Diagnostic::error("a class can only extend another class")
                    .with_label(format!("`{name}` is {}", article(other))),
            };
            self.dcx.emit(diagnostic.with_span(ty.span));
            valid = false;
        }

        for ty in implements {
            let Ty::Adt {
                def: parent, name, ..
            } = self.lower_ty(ty)
            else {
                continue;
            };
            let parent = self.sig(parent).kind;
            if parent == AdtKind::Interface {
                continue;
            }
            let diagnostic = Diagnostic::error(format!("`{name}` is not an interface"))
                .with_span(ty.span)
                .with_label(format!("`{name}` is {}", article(parent)));
            let diagnostic = if (kind, parent) == (AdtKind::Class, AdtKind::Class) {
                diagnostic.with_help(format!("use `extends {name}` instead"))
            } else {
                diagnostic
            };
            self.dcx.emit(diagnostic);
            valid = false;
        }
        valid
    }

    fn check_overrides(&self, def: DefId) {
        let supertypes = self.supertypes(def);
        let mut methods: Vec<&MethodSig> = self.sig(def).methods.values().flatten().collect();
        methods.sort_by_key(|method| method.name.span.lo);

        for method in methods {
            for (parent, subst) in &supertypes {
                let overridden = self.sig(*parent).methods.get(&method.name.name);
                for theirs in overridden.into_iter().flatten() {
                    if matches!(theirs.vis, Visibility::Private(_))
                        || theirs.generics.len() != method.generics.len()
                    {
                        continue;
                    }
                    let theirs_sig = instantiate(theirs, &override_subst(subst, theirs, method));
                    if same_params(&theirs_sig.params, &method.params) {
                        self.check_override(method, theirs, &theirs_sig);
                    }
                }
            }
        }
    }

    fn check_override(&self, method: &MethodSig, theirs: &MethodSig, theirs_sig: &FnSig) {
        let name = method.name;
        let owner = self.sig(theirs.owner).name.name;

        if method.receiver != theirs.receiver {
            self.dcx.emit(
                Diagnostic::error(format!(
                    "`{}` {} but `{owner}.{}` {}",
                    name.name,
                    describe_receiver(method.receiver),
                    name.name,
                    describe_receiver(theirs.receiver)
                ))
                .with_span(name.span),
            );
            return;
        }
        if method.receiver.is_none() {
            return;
        }

        if theirs.is_final {
            self.dcx.emit(
                Diagnostic::error(format!(
                    "cannot override `{owner}.{}` because it is `final`",
                    name.name
                ))
                .with_span(name.span),
            );
        }

        // Callers of an `async` method rely on its `throws` for what
        // `await` raises, so an override must be `async` too. An `async`
        // override of a method that returns a future is fine: callers of
        // that method already expect any exception from `poll`, and an
        // `async` method throws nothing when it is called.
        if theirs.output.is_some() && method.output.is_none() {
            self.dcx.emit(
                Diagnostic::error(format!(
                    "`{}` must be `async` because `{owner}.{}` is",
                    name.name, name.name
                ))
                .with_span(name.span)
                .with_note(format!(
                    "`await` relies on the `throws` of `{owner}.{}`, which a future returned \
                     any other way doesn't follow",
                    name.name
                ))
                .with_help("make the override `async`"),
            );
            return;
        }
        let checks_throws = method.output.is_none() || theirs.output.is_some();

        let env = ParamEnv::default()
            .with_generics(&self.sig(method.owner).generics)
            .with_generics(&method.generics);
        for thrown in method.throws.iter().filter(|_| checks_throws) {
            let allowed = theirs_sig
                .throws
                .iter()
                .any(|theirs| self.is_assignable(&env, thrown, theirs));
            if self.is_checked(&env, thrown) && !allowed {
                self.dcx.emit(
                    Diagnostic::error(format!(
                        "`{}` cannot throw `{thrown}` because `{owner}.{}` does not",
                        name.name, name.name
                    ))
                    .with_span(name.span)
                    .with_help(
                        "an overriding method can only throw the checked exceptions \
                         of the method it overrides",
                    ),
                );
            }
        }
        if !self.is_assignable(&env, &method.ret, &theirs_sig.ret) {
            self.dcx.emit(
                Diagnostic::error(format!(
                    "`{}` returns `{}` but `{owner}.{}` returns `{}`",
                    name.name, method.ret, name.name, theirs_sig.ret
                ))
                .with_span(name.span)
                .with_help("an overriding method must return the same type or a subtype"),
            );
        }

        if visibility_rank(method.vis) < visibility_rank(theirs.vis) {
            self.dcx.emit(
                Diagnostic::error(format!(
                    "`{}` cannot be less visible than `{owner}.{}`",
                    name.name, name.name
                ))
                .with_span(name.span)
                .with_label(format!(
                    "`{owner}.{}` is {}",
                    name.name,
                    describe_visibility(theirs.vis)
                )),
            );
        }
    }

    fn check_abstract_methods_implemented(&self, def: DefId) {
        let sig = self.sig(def);
        if sig.is_abstract {
            return;
        }
        let self_args: Vec<Ty> = sig
            .generics
            .iter()
            .map(|param| Ty::Param(param.name))
            .collect();

        let mut missing: Vec<(DefId, Vec<String>)> = Vec::new();
        for (method, fn_sig) in self.abstract_methods(def, &self_args) {
            if self.is_implemented(def, &fn_sig) {
                continue;
            }
            let description = describe_method(&method, &fn_sig);
            match missing.iter_mut().find(|(owner, _)| *owner == method.owner) {
                Some((_, methods)) => methods.push(description),
                None => missing.push((method.owner, vec![description])),
            }
        }

        let name = sig.name.name;
        for (owner, methods) in missing {
            let methods = methods.join(", ");
            let diagnostic = if owner == def {
                Diagnostic::error(format!(
                    "`{name}` is not abstract but declares abstract methods"
                ))
                .with_note(format!("abstract: {methods}"))
                .with_help(format!(
                    "give the methods a body, or mark `{name}` as `abstract`"
                ))
            } else {
                let help = if sig.kind == AdtKind::Class {
                    format!("implement the missing methods, or mark `{name}` as `abstract`")
                } else {
                    "implement the missing methods".to_owned()
                };
                Diagnostic::error(format!(
                    "`{name}` does not implement every method of `{}`",
                    self.sig(owner).name.name
                ))
                .with_note(format!("missing: {methods}"))
                .with_help(help)
            };
            self.dcx.emit(diagnostic.with_span(sig.name.span));
        }
    }

    fn is_implemented(&self, def: DefId, fn_sig: &FnSig) -> bool {
        std::iter::once((def, Subst::new()))
            .chain(self.supertypes(def))
            .any(|(owner, subst)| {
                let methods = self.sig(owner).methods.get(&fn_sig.name);
                methods.into_iter().flatten().any(|method| {
                    !method.is_abstract
                        && method.receiver.is_some()
                        && same_params(&instantiate(method, &subst).params, &fn_sig.params)
                })
            })
    }
}

fn override_subst(subst: &Subst, theirs: &MethodSig, ours: &MethodSig) -> Subst {
    let mut subst = subst.clone();
    for (their_param, our_param) in theirs.generics.iter().zip(&ours.generics) {
        subst.insert(their_param.name, Ty::Param(our_param.name));
    }
    subst
}

fn same_params(a: &[Ty], b: &[Ty]) -> bool {
    a.len() == b.len()
        && a.iter()
            .zip(b)
            .all(|(a, b)| a == b || a.is_unknown() || b.is_unknown())
}

fn article(kind: AdtKind) -> &'static str {
    match kind {
        AdtKind::Class => "a class",
        AdtKind::Record => "a record",
        AdtKind::Interface => "an interface",
        AdtKind::Enum => "an enum",
    }
}

fn describe_receiver(receiver: Option<ReceiverKind>) -> &'static str {
    match receiver {
        None => "is `static`",
        Some(ReceiverKind::Owned) => "is `move`",
        Some(ReceiverKind::Ref) => "only reads the object",
        Some(ReceiverKind::RefMut) => "is `mut`",
    }
}

fn describe_method(method: &MethodSig, fn_sig: &FnSig) -> String {
    let modifier = match method.receiver {
        None => "static ",
        Some(ReceiverKind::Owned) => "move ",
        Some(ReceiverKind::Ref) => "",
        Some(ReceiverKind::RefMut) => "mut ",
    };
    let params: Vec<String> = fn_sig.params.iter().map(Ty::to_string).collect();
    let ret = if fn_sig.ret == Ty::Void {
        "void".to_owned()
    } else {
        fn_sig.ret.to_string()
    };
    format!("`{modifier}{ret} {}({})`", fn_sig.name, params.join(", "))
}

fn visibility_rank(vis: Visibility) -> u8 {
    match vis {
        Visibility::Private(_) => 0,
        Visibility::Protected(_) => 1,
        Visibility::Default | Visibility::Public(_) => 2,
    }
}

fn describe_visibility(vis: Visibility) -> &'static str {
    match vis {
        Visibility::Private(_) => "private",
        Visibility::Protected(_) => "protected",
        Visibility::Default | Visibility::Public(_) => "public",
    }
}

/// Whether two signatures take the same parameters, treating the generic
/// parameters of the methods as the same when they are in the same position.
fn same_signature(a: &MethodSig, b: &MethodSig) -> bool {
    if a.params.len() != b.params.len() || a.variadic != b.variadic {
        return false;
    }
    let rename: Subst = b
        .generics
        .iter()
        .zip(&a.generics)
        .map(|(from, to)| (from.name, Ty::Param(to.name)))
        .collect();
    a.params
        .iter()
        .zip(&b.params)
        .all(|(x, y)| *x == y.subst(&rename))
}
