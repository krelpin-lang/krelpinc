use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

use krelpin_ast::ast::{
    CompilationUnit, FieldStorage, GenericParamKind, Ident, Import, Item, ItemKind, Member,
    MemberKind, Method, Variant, is_intrinsic,
};
use krelpin_errors::{DiagCtxt, Diagnostic};
use krelpin_span::def_id::DefId;
use krelpin_span::{Span, Symbol};

use crate::{PackagePath, Res};

#[derive(Debug, Default)]
pub struct ItemTable {
    pub defs: Vec<TypeDef>,
    pub packages: HashMap<PackagePath, HashMap<Symbol, DefId>>,
    pub scopes: Vec<UnitScope>,
}

#[derive(Debug)]
pub struct TypeDef {
    pub def: DefId,
    pub name: Ident,
    pub package: PackagePath,
    pub unit: usize,
    pub path: Vec<usize>,
    pub parent: Option<DefId>,
    pub keyword: &'static str,
    pub nested: HashMap<Symbol, DefId>,
    pub fields: HashMap<Symbol, FieldDef>,
    pub methods: HashMap<Symbol, Vec<MethodDef>>,
    pub borrow_params: usize,
}

#[derive(Clone, Copy, Debug)]
pub struct FieldDef {
    pub span: Span,
    pub is_instance: bool,
}

#[derive(Clone, Copy, Debug)]
pub struct MethodDef {
    pub span: Span,
    pub has_receiver: bool,
}

#[derive(Debug, Default)]
pub struct UnitScope {
    pub package: PackagePath,
    pub imports: HashMap<Symbol, Res>,
    pub globs: Vec<PackagePath>,
}

impl ItemTable {
    pub fn def(&self, def: DefId) -> &TypeDef {
        &self.defs[def.index()]
    }

    pub fn lookup(&self, package: &PackagePath, name: Symbol) -> Option<DefId> {
        self.packages.get(package)?.get(&name).copied()
    }

    pub fn lookup_path(&self, path: &str) -> Option<DefId> {
        let (outer, name) = path.rsplit_once('.')?;
        let name = Symbol::intern(name);
        self.lookup(&PackagePath::parse(outer), name)
            .or_else(|| self.nested(self.lookup_path(outer)?, name))
    }

    pub fn items<'u>(
        &self,
        units: &'u [CompilationUnit],
    ) -> impl Iterator<Item = (&TypeDef, &'u Item)> {
        self.defs
            .iter()
            .map(move |def| (def, item_at(&units[def.unit], &def.path)))
    }

    pub fn nested(&self, def: DefId, name: Symbol) -> Option<DefId> {
        self.def(def).nested.get(&name).copied()
    }
}

pub(crate) fn collect(units: &[CompilationUnit], dcx: &DiagCtxt) -> ItemTable {
    let mut table = ItemTable::default();

    for (unit_index, unit) in units.iter().enumerate() {
        let package = PackagePath::of_unit(unit);

        for (item_index, item) in unit.items.iter().enumerate() {
            let def = collect_type(
                &mut table,
                dcx,
                &package,
                unit_index,
                vec![item_index],
                item,
                None,
            );
            let names = table.packages.entry(package.clone()).or_default();
            match names.entry(item.name.name) {
                Entry::Occupied(_) => report_redefinition(dcx, "name", item.name),
                Entry::Vacant(entry) => {
                    entry.insert(def);
                }
            }
        }
    }

    table.scopes = units
        .iter()
        .map(|unit| collect_imports(&table, unit, dcx))
        .collect();
    table
}

fn collect_type(
    table: &mut ItemTable,
    dcx: &DiagCtxt,
    package: &PackagePath,
    unit: usize,
    path: Vec<usize>,
    item: &Item,
    parent: Option<DefId>,
) -> DefId {
    let def = DefId::from_index(table.defs.len());
    let mut type_def = TypeDef {
        def,
        name: item.name,
        package: package.clone(),
        unit,
        path: path.clone(),
        parent,
        keyword: match &item.kind {
            ItemKind::Class(_) => "class",
            ItemKind::Record(_) => "record",
            ItemKind::Interface(_) => "interface",
            ItemKind::Enum(_) => "enum",
        },
        nested: HashMap::new(),
        fields: HashMap::new(),
        methods: HashMap::new(),
        borrow_params: item
            .generics()
            .params
            .iter()
            .filter(|param| param.kind == GenericParamKind::BorrowSource)
            .count(),
    };

    let members: &[Member] = match &item.kind {
        ItemKind::Class(class) => &class.members,
        ItemKind::Record(def) => {
            for component in &def.components {
                add_field(dcx, &mut type_def, component.name, true);
            }
            &def.members
        }
        ItemKind::Interface(interface) => &interface.members,
        ItemKind::Enum(enum_def) => &enum_def.members,
    };

    for member in members {
        match &member.kind {
            MemberKind::Field(field) => {
                let is_instance = field.storage == FieldStorage::Instance;
                add_field(dcx, &mut type_def, field.name, is_instance);
            }
            MemberKind::Method(method) => {
                if is_intrinsic(&member.annotations) && !package.is_std() {
                    dcx.emit(
                        Diagnostic::error("only the standard library can declare intrinsics")
                            .with_span(method.name.span)
                            .with_help("give the method a body, or mark it `abstract`"),
                    );
                }
                add_method(&mut type_def, method);
            }
            MemberKind::Constructor(_) | MemberKind::Type(_) => {}
        }
    }

    if let ItemKind::Enum(enum_def) = &item.kind {
        add_variants(dcx, &mut type_def, &enum_def.variants);
    }
    table.defs.push(type_def);

    for (index, member) in members.iter().enumerate() {
        let MemberKind::Type(nested) = &member.kind else {
            continue;
        };
        let mut nested_path = path.clone();
        nested_path.push(index);
        let child = collect_type(table, dcx, package, unit, nested_path, nested, Some(def));
        match table.defs[def.index()].nested.entry(nested.name.name) {
            Entry::Occupied(_) => report_redefinition(dcx, "type", nested.name),
            Entry::Vacant(entry) => {
                entry.insert(child);
            }
        }
    }
    def
}

fn item_at<'u>(unit: &'u CompilationUnit, path: &[usize]) -> &'u Item {
    let mut item = &unit.items[path[0]];
    for &index in &path[1..] {
        let members = match &item.kind {
            ItemKind::Class(class) => &class.members,
            ItemKind::Record(def) => &def.members,
            ItemKind::Interface(interface) => &interface.members,
            ItemKind::Enum(def) => &def.members,
        };
        if let MemberKind::Type(nested) = &members[index].kind {
            item = nested;
        }
    }
    item
}

fn add_variants(dcx: &DiagCtxt, def: &mut TypeDef, variants: &[Variant]) {
    let mut seen = HashSet::new();
    for variant in variants {
        let name = variant.name;
        if !seen.insert(name.name) {
            report_redefinition(dcx, "variant", name);
            continue;
        }
        if def.fields.contains_key(&name.name) || def.methods.contains_key(&name.name) {
            dcx.emit(
                Diagnostic::error(format!(
                    "the variant `{}` has the same name as a member of the enum",
                    name.name
                ))
                .with_span(name.span)
                .with_help("rename the variant or the member"),
            );
            continue;
        }
        if variant.fields.is_empty() {
            add_field(dcx, def, name, false);
        } else {
            def.methods.entry(name.name).or_default().push(MethodDef {
                span: name.span,
                has_receiver: false,
            });
        }
    }
}

fn collect_imports(table: &ItemTable, unit: &CompilationUnit, dcx: &DiagCtxt) -> UnitScope {
    let mut scope = UnitScope {
        package: PackagePath::of_unit(unit),
        ..UnitScope::default()
    };
    let defined_here: HashSet<Symbol> = unit.items.iter().map(|item| item.name.name).collect();

    for import in &unit.imports {
        if import.glob {
            let package = PackagePath::from_idents(&import.path.segments);
            if table.packages.contains_key(&package) {
                scope.globs.push(package);
            } else {
                report_unknown_package(dcx, &import.path.segments);
            }
            continue;
        }

        let Some(&name) = import.path.segments.last() else {
            continue;
        };
        if defined_here.contains(&name.name) || scope.imports.contains_key(&name.name) {
            report_redefinition(dcx, "name", name);
            continue;
        }
        if let Some(res) = resolve_import(table, import, dcx) {
            scope.imports.insert(name.name, res);
        }
    }

    scope
}

fn resolve_import(table: &ItemTable, import: &Import, dcx: &DiagCtxt) -> Option<Res> {
    let (name, package_segments) = import.path.segments.split_last()?;
    let package = PackagePath::from_idents(package_segments);

    let Some(types) = table.packages.get(&package) else {
        if let Some(def) = resolve_nested(table, &import.path.segments) {
            return Some(Res::Item(def));
        }
        report_unknown_package(dcx, package_segments);
        return None;
    };
    match types.get(&name.name) {
        Some(&def) => Some(Res::Item(def)),
        None => {
            dcx.emit(
                Diagnostic::error(format!(
                    "cannot find type `{}` in package `{package}`",
                    name.name
                ))
                .with_span(name.span)
                .with_label("not found in this package"),
            );
            None
        }
    }
}

fn resolve_nested(table: &ItemTable, segments: &[Ident]) -> Option<DefId> {
    for split in (1..segments.len().saturating_sub(1)).rev() {
        let package = PackagePath::from_idents(&segments[..split]);
        let Some(types) = table.packages.get(&package) else {
            continue;
        };
        let mut def = *types.get(&segments[split].name)?;
        for segment in &segments[split + 1..] {
            def = table
                .defs
                .iter()
                .find(|candidate| {
                    candidate.parent == Some(def) && candidate.name.name == segment.name
                })?
                .def;
        }
        return Some(def);
    }
    None
}

fn report_unknown_package(dcx: &DiagCtxt, segments: &[Ident]) {
    let (Some(first), Some(last)) = (segments.first(), segments.last()) else {
        return;
    };
    let package = PackagePath::from_idents(segments);
    dcx.emit(
        Diagnostic::error(format!(
            "unresolved import: there is no package `{package}`"
        ))
        .with_span(first.span.to(last.span))
        .with_label("no such package")
        .with_note("a crate can use the standard library, its own packages and the libraries passed with `--dep`"),
    );
}

fn add_field(dcx: &DiagCtxt, def: &mut TypeDef, name: Ident, is_instance: bool) {
    if def.fields.contains_key(&name.name) {
        report_redefinition(dcx, "field", name);
        return;
    }
    def.fields.insert(
        name.name,
        FieldDef {
            span: name.span,
            is_instance,
        },
    );
}

fn add_method(def: &mut TypeDef, method: &Method) {
    def.methods
        .entry(method.name.name)
        .or_default()
        .push(MethodDef {
            span: method.name.span,
            has_receiver: method.receiver.is_some(),
        });
}

fn report_redefinition(dcx: &DiagCtxt, what: &str, name: Ident) {
    dcx.emit(
        Diagnostic::error(format!(
            "the {what} `{}` is defined multiple times",
            name.name
        ))
        .with_span(name.span)
        .with_label(format!("`{}` redefined here", name.name))
        .with_note(format!("`{}` must be defined only once", name.name)),
    );
}
