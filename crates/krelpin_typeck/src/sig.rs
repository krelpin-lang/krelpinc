use std::collections::HashMap;

use krelpin_ast::ast::{
    self, CompilationUnit, Constructor, FieldStorage, FnRetTy, GenericParamKind, Generics, Ident,
    ItemKind, Member, MemberKind, Method, Param, ReceiverKind, TyKind, Visibility, WherePredicate,
    is_intrinsic,
};
use krelpin_errors::DiagCtxt;
use krelpin_resolve::{ItemTable, Res, Resolutions, ResolverOutput};
use krelpin_span::def_id::DefId;
use krelpin_span::{Span, Symbol, kw};

use crate::lang_items::{LangItem, LangItems};
use crate::param_env::ParamEnv;
use crate::ty::{Subst, Ty};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdtKind {
    Class,
    Record,
    Interface,
    Enum,
}

#[derive(Debug)]
pub struct TypeSig {
    pub name: Ident,
    pub kind: AdtKind,
    pub is_abstract: bool,
    pub is_final: bool,
    pub generics: Vec<GenericParamSig>,
    pub superclass: Option<Ty>,
    pub interfaces: Vec<Ty>,
    pub fields: HashMap<Symbol, FieldSig>,
    pub methods: HashMap<Symbol, Vec<MethodSig>>,
    pub ctors: Vec<MethodSig>,
    pub variants: Vec<VariantSig>,
    pub components: Vec<Symbol>,
    pub borrow_params: Vec<Symbol>,
}

impl TypeSig {
    pub fn variant(&self, name: Symbol) -> Option<&VariantSig> {
        self.variants
            .iter()
            .find(|variant| variant.name.name == name)
    }
}

#[derive(Clone, Debug)]
pub struct VariantSig {
    pub name: Ident,
    pub fields: Vec<VariantFieldSig>,
}

#[derive(Clone, Debug)]
pub struct VariantFieldSig {
    pub name: Ident,
    pub ty: Ty,
}

#[derive(Clone, Debug)]
pub struct FieldSig {
    pub name: Ident,
    pub ty: Ty,
    pub vis: Visibility,
    pub storage: FieldStorage,
    pub is_final: bool,
    pub owner: DefId,
    pub stateless: bool,
}

#[derive(Clone, Debug)]
pub struct MethodSig {
    pub name: Ident,
    pub params: Vec<Ty>,
    pub variadic: bool,
    pub ret: Ty,
    pub receiver: Option<ReceiverKind>,
    pub vis: Visibility,
    pub owner: DefId,
    pub generics: Vec<GenericParamSig>,
    pub where_bounds: Vec<GenericParamSig>,
    pub throws: Vec<Ty>,
    pub is_abstract: bool,
    pub is_final: bool,
    pub borrows: RetBorrows,
    pub storage: Vec<Storage>,
    pub member: Option<u32>,
    pub is_override: Option<Span>,
    /// For an `async` method, the type its body returns; `ret` is then the
    /// `Future` of it that a call gives. `async void` methods produce `Unit`.
    pub output: Option<Ty>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Storage {
    pub whole: bool,
    pub contents: bool,
    /// A static method keeps the argument with no object to keep it in,
    /// so it may outlive the caller: it must not borrow anything.
    pub detached: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BorrowSource {
    This,
    Param(usize),
    Class(Symbol),
}

#[derive(Clone, Debug, Default)]
pub struct RetBorrows {
    pub sources: Vec<BorrowSource>,
    pub elided: bool,
}

impl RetBorrows {
    pub fn explicit(&self) -> Option<&[BorrowSource]> {
        (!self.elided && !self.sources.is_empty()).then_some(self.sources.as_slice())
    }
}

#[derive(Clone, Debug)]
pub struct GenericParamSig {
    pub name: Symbol,
    pub bounds: Vec<Ty>,
}

pub struct Tcx<'a> {
    pub types: Vec<TypeSig>,
    pub lang_items: LangItems,
    pub(crate) items: &'a ItemTable,
    pub(crate) resolutions: &'a Resolutions,
    pub(crate) dcx: &'a DiagCtxt,
}

impl<'a> Tcx<'a> {
    pub fn new(units: &[CompilationUnit], resolved: &'a ResolverOutput, dcx: &'a DiagCtxt) -> Self {
        let mut tcx = Tcx {
            types: Vec::new(),
            lang_items: LangItems::collect(&resolved.items, dcx),
            items: &resolved.items,
            resolutions: &resolved.resolutions,
            dcx,
        };
        tcx.types = resolved
            .items
            .items(units)
            .map(|(type_def, item)| tcx.collect_item(type_def.def, item))
            .collect();
        tcx
    }

    pub fn sig(&self, def: DefId) -> &TypeSig {
        &self.types[def.index()]
    }

    pub fn lang_ty(&self, item: LangItem) -> Ty {
        self.lang_items
            .get(item)
            .map_or(Ty::Unknown, |def| self.def_ty(def, Vec::new()))
    }

    /// `Future<output>`, the type a call to an `async` method has.
    pub fn future_of(&self, output: Ty) -> Ty {
        self.lang_items
            .get(LangItem::Future)
            .map_or(Ty::Unknown, |def| self.def_ty(def, vec![output]))
    }

    /// `Poll<output>`, what the poll of an `async` body returns.
    pub fn poll_of(&self, output: Ty) -> Ty {
        self.lang_items
            .get(LangItem::Poll)
            .map_or(Ty::Unknown, |def| self.def_ty(def, vec![output]))
    }

    /// The `T` of a type that is or implements `Future<T>`.
    pub fn future_output(&self, ty: &Ty) -> Option<Ty> {
        let future = self.lang_items.get(LangItem::Future)?;
        let Ty::Adt { def, args, .. } = ty else {
            return None;
        };
        self.upcast(*def, args, future)?.into_iter().next()
    }

    pub fn is_lang_ty(&self, ty: &Ty, item: LangItem) -> bool {
        matches!(ty, Ty::Adt { def, .. } if self.lang_items.is(*def, item))
    }

    pub fn string_ty(&self) -> Ty {
        self.lang_ty(LangItem::String)
    }

    pub fn is_string(&self, ty: &Ty) -> bool {
        self.is_lang_ty(ty, LangItem::String)
    }

    pub(crate) fn def_ty(&self, def: DefId, args: Vec<Ty>) -> Ty {
        Ty::Adt {
            def,
            name: self.items.def(def).name.name,
            args,
        }
    }

    pub fn lower_ty(&self, ty: &ast::Ty) -> Ty {
        match &ty.kind {
            TyKind::Primitive(primitive) => Ty::Primitive(*primitive),
            TyKind::Path { path, args, .. } => {
                let args: Vec<Ty> = args.iter().map(|arg| self.lower_ty(arg)).collect();
                let Some(segment) = path.segments.last() else {
                    return Ty::Unknown;
                };
                match self.resolutions.get(segment.span) {
                    Some(Res::Item(def)) => self.def_ty(def, args),
                    Some(Res::TypeParam(_)) => Ty::Param(segment.name),
                    _ => Ty::Unknown,
                }
            }
            TyKind::Ref { mutable, ty, .. } => Ty::Ref {
                mutable: *mutable,
                ty: Box::new(self.lower_ty(ty)),
            },
            TyKind::Nullable(ty) => Ty::Nullable(Box::new(self.lower_ty(ty))),
            TyKind::Array(ty) => Ty::Array(Box::new(self.lower_ty(ty))),
        }
    }

    pub fn self_ty(&self, def: DefId) -> Ty {
        if let Some(primitive) = self.lang_items.primitive_of(def) {
            return Ty::Primitive(primitive);
        }
        let generics = &self.sig(def).generics;
        self.def_ty(
            def,
            generics.iter().map(|param| Ty::Param(param.name)).collect(),
        )
    }

    pub fn subst_for(&self, def: DefId, args: &[Ty]) -> Subst {
        let generics = &self.sig(def).generics;
        if args.len() == generics.len() {
            generics
                .iter()
                .map(|param| param.name)
                .zip(args.iter().cloned())
                .collect()
        } else {
            generics
                .iter()
                .map(|param| (param.name, Ty::Unknown))
                .collect()
        }
    }

    pub fn is_copy(&self, ty: &Ty) -> bool {
        self.is_copy_inner(ty, &mut Vec::new())
    }

    pub fn uncopyable_part(&self, ty: &Ty) -> Option<(Symbol, Ty)> {
        let Ty::Adt { def, args, .. } = ty.non_null() else {
            return None;
        };
        let sig = self.sig(*def);
        let subst = self.subst_for(*def, args);
        let parts: Vec<(Symbol, Ty)> = match sig.kind {
            AdtKind::Record => sig
                .components
                .iter()
                .filter_map(|name| {
                    sig.fields
                        .get(name)
                        .map(|field| (*name, field.ty.subst(&subst)))
                })
                .collect(),
            AdtKind::Enum => sig
                .variants
                .iter()
                .flat_map(|variant| &variant.fields)
                .map(|field| (field.name.name, field.ty.subst(&subst)))
                .collect(),
            AdtKind::Class | AdtKind::Interface => return None,
        };
        parts.into_iter().find(|(_, ty)| !self.is_copy(ty))
    }

    fn is_copy_inner(&self, ty: &Ty, visiting: &mut Vec<DefId>) -> bool {
        match ty {
            Ty::Primitive(_) | Ty::Null | Ty::Void | Ty::Unknown => true,
            Ty::Ref { mutable, .. } => !mutable,
            Ty::Nullable(inner) => self.is_copy_inner(inner, visiting),
            Ty::Array(_) | Ty::Param(_) => false,
            Ty::Adt { def, args, .. } => {
                if self.lang_items.is(*def, LangItem::String) {
                    return true;
                }
                if visiting.contains(def) {
                    return false;
                }
                let sig = self.sig(*def);
                let subst = self.subst_for(*def, args);
                visiting.push(*def);
                let copy = match sig.kind {
                    AdtKind::Enum => sig
                        .variants
                        .iter()
                        .flat_map(|variant| &variant.fields)
                        .all(|field| self.is_copy_inner(&field.ty.subst(&subst), visiting)),
                    AdtKind::Record => sig.components.iter().all(|name| {
                        sig.fields.get(name).is_some_and(|field| {
                            self.is_copy_inner(&field.ty.subst(&subst), visiting)
                        })
                    }),
                    AdtKind::Class | AdtKind::Interface => false,
                };
                visiting.pop();
                copy
            }
        }
    }

    pub(crate) fn nested_type(&self, owner: DefId, name: Symbol) -> Option<DefId> {
        self.items
            .defs
            .iter()
            .find(|def| def.parent == Some(owner) && def.name.name == name)
            .map(|def| def.def)
    }

    pub fn outermost(&self, mut def: DefId) -> DefId {
        while let Some(parent) = self.items.defs[def.index()].parent {
            def = parent;
        }
        def
    }

    pub fn is_subclass(&self, sub: DefId, sup: DefId) -> bool {
        if sub == sup {
            return true;
        }
        let sig = self.sig(sub);
        sig.superclass
            .iter()
            .chain(sig.interfaces.iter())
            .any(|parent| matches!(parent, Ty::Adt { def, .. } if self.is_subclass(*def, sup)))
    }

    pub fn upcast(&self, def: DefId, args: &[Ty], target: DefId) -> Option<Vec<Ty>> {
        if def == target {
            return Some(args.to_vec());
        }
        let subst = self.subst_for(def, args);
        let sig = self.sig(def);
        sig.superclass
            .iter()
            .chain(sig.interfaces.iter())
            .find_map(|parent| match parent.subst(&subst) {
                Ty::Adt { def, args, .. } => self.upcast(def, &args, target),
                _ => None,
            })
    }

    pub fn methods_named(&self, def: DefId, args: &[Ty], name: Symbol) -> Vec<(MethodSig, Subst)> {
        let mut out = Vec::new();
        self.find_methods(def, args, name, &mut out);
        if !out.is_empty() || self.sig(def).kind != AdtKind::Interface {
            return out;
        }
        if let Some(object) = self.lang_items.get(LangItem::Object) {
            self.find_methods(object, &[], name, &mut out);
        }
        out
    }

    fn find_methods(
        &self,
        def: DefId,
        args: &[Ty],
        name: Symbol,
        out: &mut Vec<(MethodSig, Subst)>,
    ) {
        let sig = self.sig(def);
        let subst = self.subst_for(def, args);
        if let Some(methods) = sig.methods.get(&name) {
            out.extend(methods.iter().map(|method| (method.clone(), subst.clone())));
        }
        for parent in sig.superclass.iter().chain(sig.interfaces.iter()) {
            if let Ty::Adt { def, args, .. } = parent.subst(&subst) {
                self.find_methods(def, &args, name, out);
            }
        }
    }

    pub fn closes_itself(&self, def: DefId) -> bool {
        let closeable = self.lang_items.get(LangItem::AutoCloseable);
        self.supertypes(def)
            .iter()
            .any(|(parent, _)| Some(*parent) == closeable)
    }

    pub fn supertypes(&self, def: DefId) -> Vec<(DefId, Subst)> {
        let mut out = Vec::new();
        let self_args: Vec<Ty> = self
            .sig(def)
            .generics
            .iter()
            .map(|param| Ty::Param(param.name))
            .collect();
        self.collect_supertypes(def, &self_args, &mut out);
        out
    }

    fn collect_supertypes(&self, def: DefId, args: &[Ty], out: &mut Vec<(DefId, Subst)>) {
        let subst = self.subst_for(def, args);
        let sig = self.sig(def);
        for parent in sig.superclass.iter().chain(sig.interfaces.iter()) {
            match parent.subst(&subst) {
                Ty::Adt { def, args, .. } if out.iter().all(|(seen, _)| *seen != def) => {
                    out.push((def, self.subst_for(def, &args)));
                    self.collect_supertypes(def, &args, out);
                }
                _ => {}
            }
        }
    }

    fn implicit_superclass(&self, def: DefId, kind: AdtKind) -> Option<Ty> {
        let parent = match kind {
            AdtKind::Class | AdtKind::Record => LangItem::Object,
            AdtKind::Enum => LangItem::Enum,
            AdtKind::Interface => return None,
        };
        let parent = self.lang_items.get(parent)?;
        (parent != def).then(|| self.def_ty(parent, Vec::new()))
    }

    fn collect_item(&self, def_id: DefId, item: &ast::Item) -> TypeSig {
        let (kind, generics, superclass, interfaces, members): (_, _, _, Vec<Ty>, &[Member]) =
            match &item.kind {
                ItemKind::Class(class) => (
                    AdtKind::Class,
                    &class.generics,
                    class.extends.as_ref().map(|ty| self.lower_ty(ty)),
                    self.lower_tys(&class.implements),
                    &class.members,
                ),
                ItemKind::Record(def) => (
                    AdtKind::Record,
                    &def.generics,
                    None,
                    self.lower_tys(&def.implements),
                    &def.members,
                ),
                ItemKind::Interface(interface) => (
                    AdtKind::Interface,
                    &interface.generics,
                    None,
                    self.lower_tys(&interface.extends),
                    &interface.members,
                ),
                ItemKind::Enum(def) => (
                    AdtKind::Enum,
                    &def.generics,
                    None,
                    self.lower_tys(&def.implements),
                    &def.members,
                ),
            };

        let mut sig = TypeSig {
            name: item.name,
            kind,
            is_abstract: kind == AdtKind::Interface || item.inheritance.abstract_kw.is_some(),
            is_final: item.inheritance.final_kw.is_some(),
            generics: self.generic_params(generics),
            superclass: superclass.or_else(|| self.implicit_superclass(def_id, kind)),
            interfaces,
            fields: HashMap::new(),
            methods: HashMap::new(),
            ctors: Vec::new(),
            variants: Vec::new(),
            components: Vec::new(),
            borrow_params: generics
                .params
                .iter()
                .filter(|param| param.kind == GenericParamKind::BorrowSource)
                .map(|param| param.name.name)
                .collect(),
        };

        if let ItemKind::Enum(def) = &item.kind {
            self.collect_variants(&mut sig, def_id, &def.variants);
        }
        if let ItemKind::Record(def) = &item.kind {
            self.collect_components(&mut sig, def_id, def);
        }

        for (index, member) in members.iter().enumerate() {
            let index = index as u32;
            let vis = match member.vis {
                _ if kind == AdtKind::Interface => Visibility::Public(member.span),
                vis => vis,
            };
            match &member.kind {
                MemberKind::Type(_) => {}
                MemberKind::Field(field) => {
                    sig.fields.entry(field.name.name).or_insert(FieldSig {
                        name: field.name,
                        ty: self.lower_ty(&field.ty),
                        vis,
                        storage: field.storage,
                        is_final: field.final_kw.is_some(),
                        owner: def_id,
                        stateless: matches!(field.storage, FieldStorage::Static(_))
                            && field.init.as_ref().is_some_and(is_lambda),
                    });
                }
                MemberKind::Constructor(ctor) => {
                    sig.ctors.push(MethodSig {
                        member: Some(index),
                        ..self.ctor_sig(ctor, vis, def_id)
                    });
                }
                MemberKind::Method(method) => {
                    let method_sig = MethodSig {
                        member: Some(index),
                        ..self.method_sig(member, method, vis, def_id, &sig.borrow_params)
                    };
                    sig.methods
                        .entry(method.name.name)
                        .or_default()
                        .push(method_sig);
                }
            }
        }

        sig
    }

    fn collect_components(&self, sig: &mut TypeSig, def: DefId, record: &ast::Record) {
        for component in &record.components {
            let name = component.name;
            sig.components.push(name.name);
            // Components are read through their accessors outside the
            // record, like any other encapsulated state.
            sig.fields.entry(name.name).or_insert(FieldSig {
                name,
                ty: self.lower_ty(&component.ty),
                vis: Visibility::Private(name.span),
                storage: FieldStorage::Instance,
                is_final: true,
                owner: def,
                stateless: false,
            });
        }
        let has_compact_ctor = record
            .members
            .iter()
            .any(|member| matches!(&member.kind, MemberKind::Constructor(ctor) if ctor.compact));
        if !has_compact_ctor {
            sig.ctors.push(MethodSig {
                params: self.param_tys(&record.components),
                storage: self.param_storage(&record.components, &[]),
                is_final: false,
                ..synthesized_method(sig.name, def, None, Ty::Void)
            });
        }
    }

    fn collect_variants(&self, sig: &mut TypeSig, def: DefId, variants: &[ast::Variant]) {
        let self_ty = self.def_ty(
            def,
            sig.generics
                .iter()
                .map(|param| Ty::Param(param.name))
                .collect(),
        );
        for variant in variants {
            let fields: Vec<VariantFieldSig> = variant
                .fields
                .iter()
                .map(|field| VariantFieldSig {
                    name: field.name,
                    ty: self.lower_ty(&field.ty),
                })
                .collect();
            let name = variant.name;
            if fields.is_empty() {
                sig.fields.entry(name.name).or_insert(FieldSig {
                    name,
                    ty: self_ty.clone(),
                    vis: Visibility::Public(name.span),
                    storage: FieldStorage::Static(name.span),
                    is_final: true,
                    owner: def,
                    stateless: false,
                });
            } else {
                let ctor = MethodSig {
                    params: fields.iter().map(|field| field.ty.clone()).collect(),
                    generics: sig.generics.clone(),
                    ..synthesized_method(name, def, None, self_ty.clone())
                };
                sig.methods.entry(name.name).or_default().push(ctor);
            }
            sig.variants.push(VariantSig { name, fields });
        }

        if sig.variants.iter().all(|variant| variant.fields.is_empty()) {
            self.synthesize_unit_enum_members(sig, def, self_ty);
        }
    }

    /// Gives every component of a record an accessor of the same name,
    /// unless the record declares one: `point.x()`. A component that can
    /// be copied is returned as a copy, and any other as a reference into
    /// the record.
    pub(crate) fn add_record_accessors(&mut self) {
        for def in (0..self.types.len()).map(DefId::from_index) {
            let sig = self.sig(def);
            if sig.kind != AdtKind::Record {
                continue;
            }
            let mut accessors = Vec::new();
            for name in &sig.components {
                let declared = sig
                    .methods
                    .get(name)
                    .is_some_and(|methods| methods.iter().any(|method| method.params.is_empty()));
                if declared {
                    continue;
                }
                let field = &sig.fields[name];
                let ret = self.accessor_ty(&field.ty);
                // What the accessor returns may borrow from the record.
                let borrows = RetBorrows {
                    sources: Vec::new(),
                    elided: true,
                };
                accessors.push(MethodSig {
                    borrows,
                    ..synthesized_method(field.name, def, Some(ReceiverKind::Ref), ret)
                });
            }
            let sig = &mut self.types[def.index()];
            for accessor in accessors {
                sig.methods
                    .entry(accessor.name.name)
                    .or_default()
                    .push(accessor);
            }
        }
    }

    /// What the accessor of a component of type `component` returns: a
    /// copy if the component can be copied, else a reference to it.
    pub(crate) fn accessor_ty(&self, component: &Ty) -> Ty {
        if self.is_copy(component) {
            component.clone()
        } else {
            Ty::Ref {
                mutable: false,
                ty: Box::new(component.clone()),
            }
        }
    }

    pub(crate) fn derive_record_equality(&mut self) {
        loop {
            let mut changed = false;
            for def in (0..self.types.len()).map(DefId::from_index) {
                for item in [
                    LangItem::Equatable,
                    LangItem::Hashable,
                    LangItem::Cloneable,
                    LangItem::Comparable,
                ] {
                    changed |= self.add_record_interface(def, item);
                }
            }
            if !changed {
                return;
            }
        }
    }

    fn add_record_interface(&mut self, def: DefId, item: LangItem) -> bool {
        let sig = self.sig(def);
        let Some(interface) = self.lang_items.get(item) else {
            return false;
        };
        let method_name = match item {
            LangItem::Equatable => "equals",
            LangItem::Cloneable => "clone",
            LangItem::Comparable => "compareTo",
            _ => "hashCode",
        };
        let already_implemented = sig.methods.contains_key(&Symbol::intern(method_name))
            || sig.interfaces.iter().any(
                |parent| matches!(parent, Ty::Adt { def: parent, .. } if *parent == interface),
            );
        let unit_enum = sig.kind == AdtKind::Enum
            && sig.variants.iter().all(|variant| variant.fields.is_empty());
        let applies = match item {
            LangItem::Comparable => unit_enum,
            _ => matches!(sig.kind, AdtKind::Record | AdtKind::Enum),
        };
        if !applies || already_implemented {
            return false;
        }
        let env = ParamEnv::default().with_generics(&sig.generics);
        let components: Vec<Ty> = match sig.kind {
            AdtKind::Enum => sig
                .variants
                .iter()
                .flat_map(|variant| variant.fields.iter().map(|field| field.ty.clone()))
                .collect(),
            _ => sig
                .components
                .iter()
                .map(|name| sig.fields[name].ty.clone())
                .collect(),
        };
        let every_component = components.into_iter().all(|ty| {
            let ty = ty.non_null().clone();
            let bound = self.def_ty(interface, vec![ty.clone()]);
            ty.references_unknown() || self.satisfies_bound(&env, &ty, &bound)
        });
        if !every_component {
            return false;
        }

        let self_ty = self.self_ty(def);
        let span = sig.name.span;
        let name = Ident::new(Symbol::intern(method_name), span);
        let method = match item {
            LangItem::Equatable | LangItem::Comparable => MethodSig {
                params: vec![Ty::Ref {
                    mutable: false,
                    ty: Box::new(self_ty.clone()),
                }],
                ..synthesized_method(
                    name,
                    def,
                    Some(ReceiverKind::Ref),
                    if item == LangItem::Equatable {
                        Ty::BOOLEAN
                    } else {
                        Ty::INT
                    },
                )
            },
            LangItem::Cloneable => {
                synthesized_method(name, def, Some(ReceiverKind::Ref), self_ty.clone())
            }
            _ => synthesized_method(name, def, Some(ReceiverKind::Ref), Ty::INT),
        };
        let interface_ty = self.def_ty(interface, vec![self_ty]);
        let sig = &mut self.types[def.index()];
        sig.interfaces.push(interface_ty);
        sig.methods
            .entry(method.name.name)
            .or_default()
            .push(method);
        true
    }

    pub(crate) fn satisfies_bound(&self, env: &ParamEnv, arg: &Ty, bound: &Ty) -> bool {
        if self.is_assignable(env, arg, bound) {
            return true;
        }
        let Ty::Adt { def, args, .. } = bound else {
            return false;
        };
        let Some(item) = [LangItem::Equatable, LangItem::Hashable, LangItem::Cloneable]
            .into_iter()
            .find(|item| self.lang_items.get(*item) == Some(*def))
        else {
            return false;
        };
        if args.first() != Some(arg) {
            return false;
        }
        if let Ty::Nullable(inner) = arg {
            let inner = inner.as_ref();
            return self.satisfies_bound(env, inner, &self.def_ty(*def, vec![inner.clone()]));
        }
        self.has_structural_method(env, arg, item)
    }

    fn has_structural_method(&self, env: &ParamEnv, ty: &Ty, item: LangItem) -> bool {
        let Ty::Adt { def, args, .. } = ty else {
            return false;
        };
        let borrowed = Ty::Ref {
            mutable: false,
            ty: Box::new(ty.clone()),
        };
        let (name, params, ret) = match item {
            LangItem::Equatable => ("equals", vec![borrowed], Ty::BOOLEAN),
            LangItem::Hashable => {
                if !self.has_structural_method(env, ty, LangItem::Equatable)
                    && !self.is_assignable(env, ty, &self.def_ty_of(LangItem::Equatable, ty))
                {
                    return false;
                }
                ("hashCode", Vec::new(), Ty::INT)
            }
            LangItem::Cloneable => ("clone", Vec::new(), ty.clone()),
            _ => return false,
        };
        self.methods_named(*def, args, Symbol::intern(name))
            .iter()
            .any(|(method, subst)| {
                method.receiver == Some(ReceiverKind::Ref)
                    && method
                        .params
                        .iter()
                        .map(|param| param.subst(subst))
                        .eq(params.iter().cloned())
                    && method.ret.subst(subst) == ret
                    && self.where_bounds_hold(env, method, subst)
            })
    }

    fn where_bounds_hold(&self, env: &ParamEnv, method: &MethodSig, subst: &Subst) -> bool {
        method.where_bounds.iter().all(|param| {
            subst.get(&param.name).is_some_and(|arg| {
                param
                    .bounds
                    .iter()
                    .all(|bound| self.satisfies_bound(env, arg, &bound.subst(subst)))
            })
        })
    }

    pub fn implementation_holds(
        &self,
        env: &ParamEnv,
        def: DefId,
        args: &[Ty],
        iface: &Ty,
    ) -> bool {
        self.implementing_methods(def, args, iface)
            .iter()
            .all(|(method, subst)| self.where_bounds_hold(env, method, subst))
    }

    fn implementing_methods(&self, def: DefId, args: &[Ty], iface: &Ty) -> Vec<(MethodSig, Subst)> {
        let Ty::Adt {
            def: iface_def,
            args: iface_args,
            ..
        } = iface
        else {
            return Vec::new();
        };
        if self.sig(*iface_def).kind != AdtKind::Interface {
            return Vec::new();
        }
        let mut out = Vec::new();
        for (declared, required) in self.abstract_methods(*iface_def, iface_args) {
            if !declared.where_bounds.is_empty() {
                continue;
            }
            out.extend(
                self.methods_named(def, args, required.name)
                    .into_iter()
                    .filter(|(method, subst)| {
                        !method.is_abstract
                            && method.receiver.is_some()
                            && !method.where_bounds.is_empty()
                            && self.sig(method.owner).kind != AdtKind::Interface
                            && method
                                .params
                                .iter()
                                .map(|param| param.subst(subst))
                                .eq(required.params.iter().cloned())
                    }),
            );
        }
        out
    }

    pub(crate) fn erased_name(&self, ty: &Ty) -> Ty {
        match ty {
            Ty::Adt { def, .. } => {
                let args = self
                    .sig(*def)
                    .generics
                    .iter()
                    .map(|param| Ty::Param(param.name))
                    .collect();
                self.def_ty(*def, args)
            }
            _ => ty.clone(),
        }
    }

    pub(crate) fn unmet_conditions(&self, ty: &Ty, iface: &Ty) -> Option<String> {
        let (Ty::Adt { def, .. }, Ty::Adt { def: iface_def, .. }) = (ty.strip_refs(), iface) else {
            return None;
        };
        if !self.is_subclass(*def, *iface_def) {
            return None;
        }
        let conditions = self.implementation_conditions(ty.strip_refs(), iface);
        if conditions.is_empty() {
            return None;
        }
        Some(format!(
            "`{}` implements `{iface}` only where {}",
            self.erased_name(ty.strip_refs()),
            conditions.join(" and ")
        ))
    }

    pub(crate) fn implementation_conditions(&self, ty: &Ty, iface: &Ty) -> Vec<String> {
        let Ty::Adt { def, .. } = ty else {
            return Vec::new();
        };
        let mut conditions = Vec::new();
        let erased = self.erased_name(ty);
        let Ty::Adt { args: own, .. } = &erased else {
            return Vec::new();
        };
        let Some(iface_args) = (match iface {
            Ty::Adt { def: iface_def, .. } => self.upcast(*def, own, *iface_def),
            _ => None,
        }) else {
            return Vec::new();
        };
        let iface = match iface {
            Ty::Adt { def, name, .. } => Ty::Adt {
                def: *def,
                name: *name,
                args: iface_args,
            },
            _ => return Vec::new(),
        };
        for (method, _) in self.implementing_methods(*def, own, &iface) {
            for param in &method.where_bounds {
                let bounds: Vec<String> =
                    param.bounds.iter().map(|bound| bound.to_string()).collect();
                let condition = format!("`{} extends {}`", param.name, bounds.join(" & "));
                if !conditions.contains(&condition) {
                    conditions.push(condition);
                }
            }
        }
        conditions
    }

    pub(crate) fn def_ty_of(&self, item: LangItem, arg: &Ty) -> Ty {
        match self.lang_items.get(item) {
            Some(def) => self.def_ty(def, vec![arg.clone()]),
            None => Ty::Unknown,
        }
    }

    fn synthesize_unit_enum_members(&self, sig: &mut TypeSig, def: DefId, self_ty: Ty) {
        if let Some(hashable) = self.lang_items.get(LangItem::Hashable) {
            sig.interfaces
                .push(self.def_ty(hashable, vec![self_ty.clone()]));
        }

        let span = sig.name.span;
        let name = |name: &str| Ident::new(Symbol::intern(name), span);
        let borrowed_self = Ty::Ref {
            mutable: false,
            ty: Box::new(self_ty.clone()),
        };
        let methods = [
            synthesized_method(name("values"), def, None, Ty::Array(Box::new(self_ty))),
            MethodSig {
                params: vec![borrowed_self],
                ..synthesized_method(name("equals"), def, Some(ReceiverKind::Ref), Ty::BOOLEAN)
            },
            synthesized_method(name("hashCode"), def, Some(ReceiverKind::Ref), Ty::INT),
        ];
        for method in methods {
            sig.methods
                .entry(method.name.name)
                .or_default()
                .push(method);
        }
    }

    fn method_sig(
        &self,
        member: &Member,
        method: &Method,
        vis: Visibility,
        owner: DefId,
        class_sources: &[Symbol],
    ) -> MethodSig {
        let declared = match &method.ret {
            FnRetTy::Void(_) => Ty::Void,
            FnRetTy::Ty(ty) => self.lower_ty(ty),
        };
        let (ret, output, borrows) = if method.asyncness.is_some() {
            let output = match declared {
                Ty::Void => self.lang_ty(LangItem::Unit),
                ty => ty,
            };
            // The future holds every argument until it finishes, so it
            // borrows whatever they borrow.
            let borrows = RetBorrows {
                sources: Vec::new(),
                elided: true,
            };
            (self.future_of(output.clone()), Some(output), borrows)
        } else {
            (declared, None, self.ret_borrows(method, class_sources))
        };
        let storage = self.method_param_storage(method);
        let is_abstract = member.inheritance.abstract_kw.is_some()
            || (method.body.is_none() && !is_intrinsic(&member.annotations));
        MethodSig {
            name: method.name,
            params: self.param_tys(&method.params),
            variadic: is_variadic(&method.params),
            ret,
            receiver: method.receiver.map(|receiver| receiver.kind),
            vis,
            owner,
            generics: self.generic_params(&method.generics),
            where_bounds: self.where_bounds(&method.where_clause),
            throws: self.lower_tys(&method.throws),
            is_abstract,
            is_final: member.inheritance.final_kw.is_some(),
            borrows,
            storage,
            member: None,
            is_override: member
                .annotations
                .iter()
                .find(|annotation| annotation.is("Override"))
                .map(|annotation| annotation.span),
            output,
        }
    }

    /// Where a method may keep its arguments. A static method that keeps one
    /// has no object to keep it in, so it keeps it forever: `detached`.
    pub fn method_param_storage(&self, method: &Method) -> Vec<Storage> {
        let mut storage = self.param_storage(&method.params, &method.keeps);
        if method.receiver.is_none() {
            for (storage, param) in storage.iter_mut().zip(&method.params) {
                storage.detached = method.keeps.iter().any(|kept| kept.name == param.name.name);
            }
        }
        storage
    }

    pub fn param_storage(&self, params: &[Param], keeps: &[Ident]) -> Vec<Storage> {
        params
            .iter()
            .map(|param| {
                let kept = keeps.iter().any(|kept| kept.name == param.name.name);
                match &param.ty.kind {
                    TyKind::Ref { ty, .. } => Storage {
                        whole: kept,
                        contents: kept || self.mentions_storable(ty),
                        detached: false,
                    },
                    _ => Storage {
                        whole: kept || self.mentions_storable(&param.ty),
                        contents: false,
                        detached: false,
                    },
                }
            })
            .collect()
    }

    fn mentions_storable(&self, ty: &ast::Ty) -> bool {
        match &ty.kind {
            TyKind::Primitive(_) => false,
            TyKind::Ref { ty, .. } | TyKind::Nullable(ty) | TyKind::Array(ty) => {
                self.mentions_storable(ty)
            }
            TyKind::Path { path, args } => {
                let res = path
                    .segments
                    .last()
                    .and_then(|segment| self.resolutions.get(segment.span));
                match res {
                    Some(Res::TypeParam(_)) => true,
                    Some(Res::Item(def)) if self.view_def(def) => true,
                    _ => args.iter().any(|arg| self.mentions_storable(arg)),
                }
            }
        }
    }

    fn view_def(&self, def: DefId) -> bool {
        self.items.def(def).borrow_params > 0
    }

    fn borrows_anything(&self, ty: &ast::Ty) -> bool {
        match &ty.kind {
            TyKind::Primitive(_) => false,
            TyKind::Ref { .. } => true,
            TyKind::Nullable(ty) | TyKind::Array(ty) => self.borrows_anything(ty),
            TyKind::Path { path, args } => {
                let res = path
                    .segments
                    .last()
                    .and_then(|segment| self.resolutions.get(segment.span));
                matches!(res, Some(Res::Item(def)) if self.view_def(def))
                    || args.iter().any(|arg| self.borrows_anything(arg))
            }
        }
    }

    pub fn ret_borrows(&self, method: &Method, class_sources: &[Symbol]) -> RetBorrows {
        let FnRetTy::Ty(ret) = &method.ret else {
            return RetBorrows::default();
        };
        if !self.borrows_anything(ret) {
            return RetBorrows::default();
        }
        if !method.borrows.is_empty() {
            let mut sources = Vec::new();
            for name in &method.borrows {
                let source = if name.name == kw::This {
                    Some(BorrowSource::This)
                } else if let Some(index) = method
                    .params
                    .iter()
                    .position(|param| param.name.name == name.name)
                {
                    Some(BorrowSource::Param(index))
                } else {
                    class_sources
                        .contains(&name.name)
                        .then_some(BorrowSource::Class(name.name))
                };
                if let Some(source) = source.filter(|source| !sources.contains(source)) {
                    sources.push(source);
                }
            }
            return RetBorrows {
                sources,
                elided: false,
            };
        }
        let receiver = method.receiver.map(|receiver| receiver.kind);
        if matches!(receiver, Some(ReceiverKind::Ref | ReceiverKind::RefMut)) {
            return RetBorrows {
                sources: vec![BorrowSource::This],
                elided: false,
            };
        }
        let borrowed: Vec<usize> = method
            .params
            .iter()
            .enumerate()
            .filter(|(_, param)| self.borrows_anything(&param.ty))
            .map(|(index, _)| index)
            .collect();
        match borrowed.as_slice() {
            [index] => RetBorrows {
                sources: vec![BorrowSource::Param(*index)],
                elided: false,
            },
            _ => RetBorrows {
                sources: Vec::new(),
                elided: true,
            },
        }
    }

    fn ctor_sig(&self, ctor: &Constructor, vis: Visibility, owner: DefId) -> MethodSig {
        MethodSig {
            name: ctor.name,
            params: self.param_tys(&ctor.params),
            variadic: is_variadic(&ctor.params),
            ret: Ty::Void,
            receiver: None,
            vis,
            owner,
            generics: Vec::new(),
            where_bounds: Vec::new(),
            throws: self.lower_tys(&ctor.throws),
            is_abstract: false,
            is_final: false,
            borrows: RetBorrows::default(),
            storage: self.param_storage(&ctor.params, &ctor.keeps),
            member: None,
            is_override: None,
            output: None,
        }
    }

    fn param_tys(&self, params: &[Param]) -> Vec<Ty> {
        params
            .iter()
            .map(|param| {
                let ty = self.lower_ty(&param.ty);
                if param.variadic {
                    Ty::Array(Box::new(ty))
                } else {
                    ty
                }
            })
            .collect()
    }

    pub(crate) fn where_bounds(&self, predicates: &[WherePredicate]) -> Vec<GenericParamSig> {
        predicates
            .iter()
            .map(|predicate| GenericParamSig {
                name: predicate.param.name,
                bounds: self.lower_tys(&predicate.bounds),
            })
            .collect()
    }

    pub(crate) fn generic_params(&self, generics: &Generics) -> Vec<GenericParamSig> {
        generics
            .params
            .iter()
            .filter_map(|param| match &param.kind {
                GenericParamKind::Type { bounds } => Some(GenericParamSig {
                    name: param.name.name,
                    bounds: self.lower_tys(bounds),
                }),
                GenericParamKind::BorrowSource => None,
            })
            .collect()
    }

    pub(crate) fn lower_tys(&self, tys: &[ast::Ty]) -> Vec<Ty> {
        tys.iter().map(|ty| self.lower_ty(ty)).collect()
    }
}

fn is_variadic(params: &[Param]) -> bool {
    params.last().is_some_and(|param| param.variadic)
}

fn synthesized_method(
    name: Ident,
    owner: DefId,
    receiver: Option<ReceiverKind>,
    ret: Ty,
) -> MethodSig {
    MethodSig {
        name,
        params: Vec::new(),
        variadic: false,
        ret,
        receiver,
        vis: Visibility::Public(name.span),
        owner,
        generics: Vec::new(),
        where_bounds: Vec::new(),
        throws: Vec::new(),
        is_abstract: false,
        is_final: true,
        borrows: RetBorrows::default(),
        storage: Vec::new(),
        member: None,
        is_override: None,
        output: None,
    }
}

fn is_lambda(expr: &ast::Expr) -> bool {
    match &expr.kind {
        ast::ExprKind::Lambda { .. } => true,
        ast::ExprKind::Cast { expr, .. } => is_lambda(expr),
        _ => false,
    }
}
