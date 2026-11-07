use krelpin_ast::ast::{self, FieldStorage, Item, ItemKind, Member, MemberKind, TyKind};
use krelpin_errors::Diagnostic;
use krelpin_resolve::Res;
use krelpin_span::Span;
use krelpin_span::def_id::DefId;

use crate::check::plural;
use crate::param_env::ParamEnv;
use crate::sig::{GenericParamSig, Tcx};
use crate::ty::Ty;

impl Tcx<'_> {
    pub(crate) fn check_item_wf(&self, def: DefId, item: &Item) {
        let sig = self.sig(def);
        let env = ParamEnv::default().with_generics(&sig.generics);

        let (generics, parents, members): (&ast::Generics, Vec<&ast::Ty>, &[Member]) = match &item
            .kind
        {
            ItemKind::Class(class) => (
                &class.generics,
                class.extends.iter().chain(&class.implements).collect(),
                &class.members,
            ),
            ItemKind::Record(def) => (&def.generics, def.implements.iter().collect(), &def.members),
            ItemKind::Interface(interface) => (
                &interface.generics,
                interface.extends.iter().collect(),
                &interface.members,
            ),
            ItemKind::Enum(def) => (&def.generics, def.implements.iter().collect(), &def.members),
        };

        self.check_bounds_wf(&env, generics);
        if let ItemKind::Record(def) = &item.kind {
            for component in &def.components {
                self.check_wf(&env, &component.ty);
            }
        }
        if let ItemKind::Enum(def) = &item.kind {
            for field in def.variants.iter().flat_map(|variant| &variant.fields) {
                self.check_wf(&env, &field.ty);
            }
        }
        for parent in parents {
            self.check_wf(&env, parent);
        }
        for member in members {
            self.check_member_wf(&env, member);
        }
        self.check_static_fields(def);
    }

    fn check_static_fields(&self, def: DefId) {
        let sig = self.sig(def);
        let mut fields: Vec<_> = sig
            .fields
            .values()
            .filter(|field| field.owner == def && matches!(field.storage, FieldStorage::Static(_)))
            .filter(|field| !sig.variants.iter().any(|variant| variant.name.name == field.name.name))
            .collect();
        fields.sort_by_key(|field| field.name.span.lo);
        for field in fields {
            if !self.holds_declared_refs(&field.ty) {
                continue;
            }
            self.dcx.emit(
                Diagnostic::error(format!(
                    "the `static` field `{}` has type `{}`, which may hold references",
                    field.name.name, field.ty
                ))
                .with_span(field.name.span)
                .with_note("a `static` field lives as long as the program, longer than anything it could borrow")
                .with_help("keep it in a local or an instance field, or store owned values instead of references"),
            );
        }
    }

    fn check_member_wf(&self, env: &ParamEnv, member: &Member) {
        match &member.kind {
            MemberKind::Type(_) => {}
            MemberKind::Field(field) => self.check_wf(env, &field.ty),
            MemberKind::Constructor(ctor) => {
                for param in &ctor.params {
                    self.check_wf(env, &param.ty);
                }
                for ty in &ctor.throws {
                    self.check_wf(env, ty);
                }
                self.check_throws_clause(env, &ctor.throws);
            }
            MemberKind::Method(method) => {
                let env = env
                    .clone()
                    .with_generics(&self.generic_params(&method.generics))
                    .with_where_bounds(&self.where_bounds(&method.where_clause));
                self.check_bounds_wf(&env, &method.generics);
                for predicate in &method.where_clause {
                    for bound in &predicate.bounds {
                        self.check_wf(&env, bound);
                    }
                }
                if let ast::FnRetTy::Ty(ty) = &method.ret {
                    self.check_wf(&env, ty);
                }
                for param in &method.params {
                    self.check_wf(&env, &param.ty);
                }
                for ty in &method.throws {
                    self.check_wf(&env, ty);
                }
                self.check_throws_clause(&env, &method.throws);
            }
        }
    }

    fn check_bounds_wf(&self, env: &ParamEnv, generics: &ast::Generics) {
        for param in &generics.params {
            if env.is_cyclic(param.name.name) {
                self.dcx.emit(
                    Diagnostic::error(format!(
                        "the bounds of `{}` lead back to `{}`",
                        param.name.name, param.name.name
                    ))
                    .with_span(param.name.span)
                    .with_label("this parameter extends itself")
                    .with_help("a type parameter can't be bounded by itself, directly or through other parameters"),
                );
            }
            if let ast::GenericParamKind::Type { bounds } = &param.kind {
                for bound in bounds {
                    self.check_wf(env, bound);
                }
            }
        }
    }

    pub(crate) fn check_wf(&self, env: &ParamEnv, ty: &ast::Ty) {
        self.check_wf_with(env, ty, false);
    }

    /// Like `check_wf`, but the outermost type may leave out its type
    /// arguments because they are inferred, as in `new ArrayList<>()`.
    pub(crate) fn check_wf_inferred(&self, env: &ParamEnv, ty: &ast::Ty) {
        self.check_wf_with(env, ty, true);
    }

    fn check_wf_with(&self, env: &ParamEnv, ty: &ast::Ty, inferred: bool) {
        match &ty.kind {
            TyKind::Primitive(_) => {}
            TyKind::Path { path, args } => {
                for arg in args {
                    self.check_wf(env, arg);
                }
                let Some(segment) = path.segments.last() else {
                    return;
                };
                match self.resolutions.get(segment.span) {
                    Some(Res::Item(def)) => match self.lang_items.primitive_of(def) {
                        Some(primitive) => {
                            self.dcx.emit(
                                Diagnostic::error(format!("`{}` is not a type", segment.name))
                                    .with_span(ty.span)
                                    .with_help(format!("use `{}` instead", primitive.name())),
                            );
                        }
                        None if inferred && args.is_empty() => {}
                        None => self.check_generic_args(env, def, args, ty.span),
                    },
                    Some(Res::TypeParam(_)) if !args.is_empty() => {
                        self.dcx.emit(
                            Diagnostic::error(format!(
                                "type parameter `{}` does not take type arguments",
                                segment.name
                            ))
                            .with_span(ty.span),
                        );
                    }
                    _ => {}
                }
            }
            TyKind::Ref { ty, .. } | TyKind::Nullable(ty) | TyKind::Array(ty) => {
                self.check_wf(env, ty);
            }
        }
    }

    fn check_generic_args(&self, env: &ParamEnv, def: DefId, args: &[ast::Ty], span: Span) {
        let generics = &self.sig(def).generics;
        if args.is_empty() && !generics.is_empty() {
            let name = self.sig(def).name.name;
            let params: Vec<String> = generics
                .iter()
                .map(|param| param.name.to_string())
                .collect();
            self.dcx.emit(
                Diagnostic::error(format!("missing type arguments for `{name}`"))
                    .with_span(span)
                    .with_label(format!(
                        "expected {}",
                        plural(generics.len(), "type argument")
                    ))
                    .with_help(format!("write `{name}<{}>`", params.join(", "))),
            );
            return;
        }
        if args.len() != generics.len() {
            let supplied = if args.len() == 1 { "was" } else { "were" };
            self.dcx.emit(
                Diagnostic::error(format!(
                    "`{}` takes {} but {} {supplied} supplied",
                    self.sig(def).name.name,
                    plural(generics.len(), "type argument"),
                    args.len()
                ))
                .with_span(span),
            );
            return;
        }

        let lowered: Vec<Ty> = args.iter().map(|arg| self.lower_ty(arg)).collect();
        let subst = self.subst_for(def, &lowered);
        for ((param, arg), ast_arg) in generics.iter().zip(&lowered).zip(args) {
            self.check_bound(env, param, arg, &subst, ast_arg.span);
        }
    }

    pub(crate) fn check_bound(
        &self,
        env: &ParamEnv,
        param: &GenericParamSig,
        arg: &Ty,
        subst: &crate::ty::Subst,
        span: Span,
    ) {
        for bound in &param.bounds {
            let bound = bound.subst(subst);
            if !self.satisfies_bound(env, arg, &bound) {
                self.dcx.emit(
                    Diagnostic::error(format!(
                        "type `{arg}` does not satisfy the bound of `{}`",
                        param.name
                    ))
                    .with_span(span)
                    .with_label(format!("`{arg}` is not a `{bound}`"))
                    .with_notes(self.unmet_conditions(arg, &bound)),
                );
            }
        }
    }
}
