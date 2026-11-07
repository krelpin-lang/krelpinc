use krelpin_ast::ast::{
    BinOp, Expr, ExprKind, FieldInit, FieldStorage, Ident, PrimitiveTy, SwitchExprBody, TyKind,
    UnOp, Visibility,
};
use krelpin_ast::token::{Lit, LitKind};
use krelpin_errors::Diagnostic;
use krelpin_resolve::Res;
use krelpin_span::def_id::DefId;
use krelpin_span::{Span, Symbol};

use crate::call::PendingChain;
use crate::check::{FnCtxt, plural};
use crate::closure::is_closure;
use crate::lang_items::LangItem;
use crate::pat::Coverage;
use crate::sig::{AdtKind, FieldSig, MethodSig};
use crate::ty::{Subst, Ty, promote, promote_unary};

enum Receiver {
    None,
    Type(Ty),
    Value(Ty),
}

impl FnCtxt<'_, '_> {
    pub(crate) fn check_expr(&mut self, expr: &Expr) -> Ty {
        let ty = self.check_expr_kind(expr);
        self.results.expr_types.insert(expr.span, ty.clone());
        ty
    }

    pub(crate) fn check_expr_coerce(&mut self, expr: &Expr, expected: &Ty) -> Ty {
        if is_closure(expr) {
            return self.check_closure(expr, expected);
        }
        if let ExprKind::ArrayInit { ty: None, elems } = &expr.kind {
            let Ty::Array(elem) = expected.non_null().strip_refs() else {
                if !expected.is_unknown() {
                    self.error(
                        expr.span,
                        format!("an array initializer cannot be used as `{expected}`"),
                    );
                }
                return Ty::Unknown;
            };
            let elem = elem.as_ref().clone();
            for value in elems {
                self.check_expr_coerce(value, &elem);
            }
            self.results.expr_types.insert(expr.span, expected.clone());
            return expected.clone();
        }

        if let ExprKind::MethodCall { name, .. } = &expr.kind {
            self.call_expectations.insert(name.span, expected.clone());
        }
        let actual = match &expr.kind {
            ExprKind::New { ty, args } => {
                let actual = self.check_new(ty, args, expr.span, Some(expected));
                self.results.expr_types.insert(expr.span, actual.clone());
                actual
            }
            // Each branch is checked against the expected type, so it reaches
            // values like `Poll.Pending` inside them.
            ExprKind::Ternary { cond, then, els } if !expected.references_unknown() => {
                self.check_expr_coerce(cond, &Ty::BOOLEAN);
                let (when_true, when_false) = self.null_checks(cond);
                let then_ty =
                    self.with_narrowing(&when_true, |fcx| fcx.check_expr_coerce(then, expected));
                let els_ty =
                    self.with_narrowing(&when_false, |fcx| fcx.check_expr_coerce(els, expected));
                let actual =
                    self.common_or_error(&then_ty, &els_ty, expr.span, "the branches of `?`");
                self.results.expr_types.insert(expr.span, actual.clone());
                actual
            }
            _ => self.check_expr(expr),
        };
        // A value like `Poll.Pending` names no type arguments; it takes them
        // from the type it is used as.
        let actual = match (&actual, expected.non_null()) {
            (Ty::Adt { def, .. }, Ty::Adt { def: wanted, .. })
                if def == wanted
                    && actual.references_unknown()
                    && !expected.references_unknown() =>
            {
                let inferred = expected.non_null().clone();
                self.results.expr_types.insert(expr.span, inferred.clone());
                inferred
            }
            _ => actual,
        };
        self.require_assignable(expr, &actual, expected);
        actual
    }

    pub(crate) fn require_assignable(&self, expr: &Expr, actual: &Ty, expected: &Ty) {
        if self.accepts(expr, actual, expected) || narrows_literal(expr, expected) {
            return;
        }
        self.mismatch(expr.span, expected, actual);
    }

    fn check_expr_kind(&mut self, expr: &Expr) -> Ty {
        match &expr.kind {
            ExprKind::Lit(lit) => self.lit_ty(lit),
            ExprKind::Bool(_) => Ty::BOOLEAN,
            ExprKind::Null => Ty::Null,
            ExprKind::This => self.self_ty.clone(),
            ExprKind::Super => self
                .tcx
                .sig(self.owner)
                .superclass
                .clone()
                .unwrap_or_else(|| self.tcx.lang_ty(LangItem::Object)),
            ExprKind::Name(name) => self.check_name(*name),
            ExprKind::Field {
                expr: base,
                name,
                safe,
            } => self.field_access(base, *name, *safe).0,
            ExprKind::MethodCall {
                receiver,
                type_args,
                name,
                args,
                safe,
            } => {
                if !type_args.is_empty() {
                    let tys = type_args.iter().map(|ty| self.lower_ty(ty)).collect();
                    self.explicit_type_args.insert(name.span, tys);
                }
                self.check_method_call(receiver.as_deref(), *name, args, *safe)
            }
            ExprKind::Call { callee, args } => {
                if self.delegation != Some(expr.span) {
                    let keyword = if matches!(callee.kind, ExprKind::Super) {
                        "super"
                    } else {
                        "this"
                    };
                    self.emit(
                        Diagnostic::error(format!(
                            "`{keyword}(...)` can only be the first statement of a constructor"
                        ))
                        .with_span(expr.span)
                        .with_help(if keyword == "this" {
                            "to make a new object, write `new` and the class name"
                        } else {
                            "the superclass constructor runs once, before the rest of the constructor"
                        }),
                    );
                    for arg in args {
                        self.check_expr(arg);
                    }
                    return Ty::Unknown;
                }
                let arg_tys = self.check_closure_args(args);
                let target = match callee.kind {
                    ExprKind::Super => self.tcx.sig(self.owner).superclass.clone(),
                    _ => Some(self.tcx.self_ty(self.owner)),
                };
                if let Some(Ty::Adt {
                    def, args: ty_args, ..
                }) = target
                {
                    let name = Ident::new(self.type_name(def), callee.span);
                    self.check_ctor_call(def, &ty_args, args, &arg_tys, name);
                }
                self.finish_closure_args(args);
                Ty::Void
            }
            ExprKind::Index { expr: base, index } => self.check_index(base, index),
            ExprKind::New { ty, args } => self.check_new(ty, args, expr.span, None),
            ExprKind::NewArray { elem, len } => {
                self.check_expr_coerce(len, &Ty::INT);
                Ty::Array(Box::new(self.lower_ty(elem)))
            }
            ExprKind::ArrayInit { ty, elems } => {
                let ty = ty.as_ref().map_or(Ty::Unknown, |ty| self.lower_ty(ty));
                if ty.is_unknown() {
                    self.error(
                        expr.span,
                        "an array initializer needs an explicit array type here",
                    );
                    return Ty::Unknown;
                }
                let elem = match &ty {
                    Ty::Array(elem) => elem.as_ref().clone(),
                    _ => Ty::Unknown,
                };
                for value in elems {
                    self.check_expr_coerce(value, &elem);
                }
                ty
            }
            ExprKind::Unary { op, expr: operand } => self.check_unary(*op, operand, expr.span),
            ExprKind::Borrow {
                mutable,
                expr: operand,
            } => Ty::Ref {
                mutable: *mutable,
                ty: Box::new(self.check_expr(operand)),
            },
            ExprKind::Binary { op, lhs, rhs } => self.check_binary(*op, lhs, rhs, expr.span),
            ExprKind::Assign { op, lhs, rhs } => self.check_assign(*op, lhs, rhs, expr.span),
            ExprKind::Ternary { cond, then, els } => {
                self.check_expr_coerce(cond, &Ty::BOOLEAN);
                let (when_true, when_false) = self.null_checks(cond);
                let then_ty = self.with_narrowing(&when_true, |fcx| fcx.check_expr(then));
                let els_ty = self.with_narrowing(&when_false, |fcx| fcx.check_expr(els));
                self.common_or_error(&then_ty, &els_ty, expr.span, "the branches of `?`")
            }
            ExprKind::InstanceOf { expr: operand, pat } => {
                let ty = self.check_expr(operand);
                self.check_pat(pat, &ty);
                Ty::BOOLEAN
            }
            ExprKind::Cast { ty, expr: operand } => {
                let from = self.check_expr(operand);
                let to = self.lower_ty(ty);
                self.check_cast(&from, &to, expr.span);
                to
            }
            ExprKind::With { base, fields } => self.check_with(base, fields, expr.span),
            ExprKind::Await(operand) => self.check_await(operand, expr.span),
            ExprKind::Lambda { .. } | ExprKind::MethodRef { .. } => {
                // Reached only where nothing says which interface the closure
                // implements; everywhere else goes through `check_closure`.
                self.emit(
                    Diagnostic::error("cannot tell what type this closure has")
                        .with_span(expr.span)
                        .with_help(
                            "store it in a variable of a functional interface type first, like `Supplier<int> f = ...`",
                        ),
                );
                self.check_closure(expr, &Ty::Unknown)
            }
            ExprKind::Switch { scrutinee, arms } => {
                let scrutinee_ty = self.check_expr(scrutinee);
                let mut arm_tys = Vec::new();
                let mut match_arms = Vec::new();
                for arm in arms {
                    match_arms.extend(self.check_case_label(&arm.label, &scrutinee_ty));
                    match &arm.body {
                        SwitchExprBody::Expr(value) => {
                            arm_tys.push((value.span, self.check_expr(value)))
                        }
                        SwitchExprBody::Throw(value) => {
                            self.check_throw(value);
                        }
                        SwitchExprBody::Block(block) => {
                            self.yields.push(Vec::new());
                            self.check_block(block);
                            let yields = self.yields.pop().unwrap_or_default();
                            arm_tys.extend(yields.into_iter().map(|ty| (block.span, ty)));
                        }
                    }
                }
                self.check_match(
                    &scrutinee_ty,
                    &match_arms,
                    Coverage::Required("this `switch` expression"),
                    expr.span,
                );

                let mut result: Option<Ty> = None;
                for (span, ty) in arm_tys {
                    result = Some(match result {
                        None => ty,
                        Some(previous) => {
                            self.common_or_error(&previous, &ty, span, "the cases of this `switch`")
                        }
                    });
                }
                result.unwrap_or(Ty::Unknown)
            }
        }
    }

    fn check_with(&mut self, base: &Expr, fields: &[FieldInit], span: Span) -> Ty {
        let base_ty = self.check_expr(base);
        let ty = base_ty.strip_refs().clone();
        let record_ty = match &ty {
            Ty::Adt { def, args, .. } if self.tcx.sig(*def).kind == AdtKind::Record => {
                Some((*def, args.clone()))
            }
            Ty::Unknown => None,
            other => {
                self.emit(
                    Diagnostic::error(format!("`with` cannot be used on `{other}`"))
                        .with_span(base.span)
                        .with_note("only records can be copied with some components changed")
                        .with_help(
                            "a class keeps its rules in its constructor; create a new object",
                        ),
                );
                None
            }
        };

        let mut seen: Vec<Symbol> = Vec::new();
        for field in fields {
            let name = field.name;
            let expected = match &record_ty {
                Some((def, args)) => match self.find_field(*def, args, name.name) {
                    Some((sig, field_ty)) if sig.storage == FieldStorage::Instance => {
                        self.results.fields.insert(name.span, sig);
                        field_ty
                    }
                    _ => {
                        self.no_field(&ty, name);
                        Ty::Unknown
                    }
                },
                None => Ty::Unknown,
            };
            if seen.contains(&name.name) {
                self.error(
                    name.span,
                    format!("the field `{}` is set more than once", name.name),
                );
            }
            seen.push(name.name);
            self.check_expr_coerce(&field.value, &expected);
        }
        // A record with a compact constructor checks every value it is
        // made of, so `with` runs it too.
        if let Some((def, args)) = &record_ty {
            let ctor = self
                .tcx
                .sig(*def)
                .ctors
                .iter()
                .find(|ctor| ctor.member.is_some())
                .cloned();
            if let Some(ctor) = ctor {
                let subst = self.tcx.subst_for(*def, args);
                let sig = crate::closure::instantiate(&ctor, &subst);
                for thrown in &sig.throws {
                    self.raise(thrown.clone(), span);
                }
                self.results.callees.insert(
                    span,
                    crate::Callee {
                        method: ctor,
                        params: sig.params,
                        ret: sig.ret,
                        packs_varargs: false,
                        subst,
                    },
                );
            }
        }
        ty
    }

    pub(crate) fn type_of_name(&self, expr: &Expr) -> Option<Ty> {
        match &expr.kind {
            ExprKind::Name(name) => self.type_of_ident(*name),
            ExprKind::Field { name, .. } => match self.tcx.resolutions.get(name.span)? {
                Res::Item(_) => self.type_of_ident(*name),
                _ => None,
            },
            _ => None,
        }
    }

    pub(crate) fn type_of_ident(&self, name: Ident) -> Option<Ty> {
        match self.tcx.resolutions.get(name.span)? {
            Res::Item(def) => Some(self.tcx.def_ty(def, Vec::new())),
            Res::TypeParam(_) => Some(Ty::Param(name.name)),
            Res::PrimTy(primitive) => Some(Ty::Primitive(primitive)),
            Res::Local(_) | Res::BorrowSource(_) => None,
        }
    }

    fn check_name(&mut self, name: Ident) -> Ty {
        match self.tcx.resolutions.get(name.span) {
            Some(Res::Local(decl)) => self.local_ty(decl),
            Some(Res::PrimTy(_)) => {
                self.error(
                    name.span,
                    format!("expected a value, found type `{}`", name.name),
                );
                Ty::Unknown
            }
            Some(Res::Item(_) | Res::TypeParam(_)) => {
                self.emit(
                    Diagnostic::error(format!("expected a value, found type `{}`", name.name))
                        .with_span(name.span)
                        .with_help(format!(
                            "to create an object, write `new {}(...)`",
                            name.name
                        )),
                );
                Ty::Unknown
            }
            _ => Ty::Unknown,
        }
    }

    fn receiver(&mut self, base: &Expr, safe: bool) -> (Receiver, bool) {
        if let Some(ty) = self.type_of_name(base) {
            return (Receiver::Type(ty), false);
        }

        let ty = self.check_expr(base);
        self.receiver_of(base, ty, safe)
    }

    fn receiver_of(&mut self, base: &Expr, ty: Ty, safe: bool) -> (Receiver, bool) {
        match ty {
            Ty::Nullable(inner) => {
                if !safe {
                    self.emit(
                        Diagnostic::error(format!("value of type `{}?` may be null", inner))
                            .with_span(base.span)
                            .with_help(
                                "use `?.` to access it only when it is not null, \
                                 or check `!= null` first",
                            ),
                    );
                }
                (Receiver::Value(*inner), safe)
            }
            Ty::Null => {
                self.error(base.span, "`null` has no fields or methods");
                (Receiver::Value(Ty::Unknown), false)
            }
            Ty::Ref { .. } if matches!(ty.strip_refs(), Ty::Nullable(_)) => {
                let span = match &base.kind {
                    ExprKind::Borrow { expr, .. } => expr.span,
                    _ => base.span,
                };
                self.emit(
                    Diagnostic::error(format!("value of type `{}` may be null", ty.strip_refs()))
                        .with_span(span)
                        .with_help("check `!= null` first, or give a default with `?:`"),
                );
                (Receiver::Value(Ty::Unknown), false)
            }
            ty => {
                if safe && !ty.is_unknown() {
                    self.emit(
                        Diagnostic::lint(
                            "unnecessary_safe_call",
                            "unnecessary `?.` on a value that is never null",
                        )
                        .with_span(base.span)
                        .with_help("use `.` instead"),
                    );
                }
                (Receiver::Value(ty), false)
            }
        }
    }

    pub(crate) fn field_access(
        &mut self,
        base: &Expr,
        name: Ident,
        safe: bool,
    ) -> (Ty, Option<FieldSig>) {
        let (receiver, nullable) = self.receiver(base, safe);
        let (ty, field) = match receiver {
            Receiver::Type(ty) => self.static_field(&ty, name),
            Receiver::Value(ty) => self.instance_field(ty.strip_refs(), name),
            Receiver::None => (Ty::Unknown, None),
        };
        let ty = if nullable { ty.nullable() } else { ty };
        if let Some(field) = &field {
            self.results.fields.insert(name.span, field.clone());
        }
        (ty, field)
    }

    fn static_field(&mut self, ty: &Ty, name: Ident) -> (Ty, Option<FieldSig>) {
        let Some(def) = self.static_def(ty, name) else {
            return (Ty::Unknown, None);
        };
        let Some((field, field_ty)) = self.find_field(def, &[], name.name) else {
            self.no_field(ty, name);
            return (Ty::Unknown, None);
        };
        if field.storage == FieldStorage::Instance {
            self.emit(
                Diagnostic::error(format!("`{}` is a field of each object", name.name))
                    .with_span(name.span)
                    .with_help(format!(
                        "access it through an object of `{}`, like `this.{}`",
                        self.type_name(field.owner),
                        name.name
                    )),
            );
        }
        self.check_vis(field.vis, field.owner, true, "field", name);
        (field_ty, Some(field))
    }

    fn instance_field(&mut self, ty: &Ty, name: Ident) -> (Ty, Option<FieldSig>) {
        match ty {
            Ty::Adt { .. } | Ty::Param(_) | Ty::Primitive(_) => {
                let found = self
                    .receiver_adts(ty)
                    .into_iter()
                    .find_map(|(def, args)| self.find_field(def, &args, name.name));
                let Some((field, field_ty)) = found else {
                    self.no_field(ty, name);
                    return (Ty::Unknown, None);
                };
                if field.storage != FieldStorage::Instance {
                    let owner = self.type_name(field.owner);
                    self.emit(
                        Diagnostic::error(format!(
                            "`{}` belongs to the class `{owner}`",
                            name.name
                        ))
                        .with_span(name.span)
                        .with_help(format!("write `{owner}.{}`", name.name)),
                    );
                }
                self.check_vis(field.vis, field.owner, true, "field", name);
                (field_ty, Some(field))
            }
            Ty::Array(_) if name.name.as_str() == "length" => (Ty::INT, None),
            Ty::Array(_) | Ty::Void => {
                self.no_field(ty, name);
                (Ty::Unknown, None)
            }
            _ => (Ty::Unknown, None),
        }
    }

    fn no_field(&self, ty: &Ty, name: Ident) {
        if let Some(owner) = self.enum_with_variant(ty, name) {
            self.emit(
                Diagnostic::error(format!("the variant `{owner}.{}` has fields", name.name))
                    .with_span(name.span)
                    .with_help(format!("create it with `{owner}.{}(...)`", name.name)),
            );
            return;
        }
        self.emit(
            Diagnostic::error(format!("no field `{}` on type `{ty}`", name.name))
                .with_span(name.span)
                .with_label("unknown field"),
        );
    }

    fn enum_with_variant(&self, ty: &Ty, name: Ident) -> Option<Symbol> {
        let Ty::Adt { def, .. } = ty else {
            return None;
        };
        let sig = self.tcx.sig(*def);
        sig.variant(name.name).map(|_| sig.name.name)
    }

    fn find_field(&self, def: DefId, args: &[Ty], name: Symbol) -> Option<(FieldSig, Ty)> {
        let sig = self.tcx.sig(def);
        let subst = self.tcx.subst_for(def, args);
        if let Some(field) = sig.fields.get(&name) {
            return Some((field.clone(), field.ty.subst(&subst)));
        }
        match &sig.superclass {
            Some(Ty::Adt {
                def: parent, args, ..
            }) => {
                let args: Vec<Ty> = args.iter().map(|arg| arg.subst(&subst)).collect();
                self.find_field(*parent, &args, name)
            }
            _ => None,
        }
    }

    pub(crate) fn check_vis(
        &self,
        vis: Visibility,
        owner: DefId,
        default_private: bool,
        what: &str,
        name: Ident,
    ) {
        let level = match vis {
            Visibility::Public(_) => return,
            Visibility::Default if !default_private => return,
            Visibility::Default | Visibility::Private(_) => "private",
            Visibility::Protected(_) => {
                if self.tcx.is_subclass(self.owner, owner) {
                    return;
                }
                "protected"
            }
        };
        if self.tcx.outermost(self.owner) == self.tcx.outermost(owner) {
            return;
        }
        let mut diagnostic = Diagnostic::error(format!(
            "{what} `{}` of `{}` is {level}",
            name.name,
            self.type_name(owner)
        ))
        .with_span(name.span)
        .with_label(format!("{level} {what}"));
        let component = what == "field" && self.tcx.sig(owner).components.contains(&name.name);
        if component && self.assigning == Some(name.span) {
            return;
        }
        if component {
            diagnostic = diagnostic.with_help(format!(
                "read the component with its accessor: `{}()`",
                name.name
            ));
        }
        self.emit(diagnostic);
    }

    fn check_method_call(
        &mut self,
        receiver: Option<&Expr>,
        name: Ident,
        args: &[Expr],
        safe: bool,
    ) -> Ty {
        let ty = self.method_call_ty(receiver, name, args, safe);
        if !self.pending_chains.contains_key(&name.span) {
            self.finish_closure_args(args);
        }
        if name.name.as_str() == "close" && args.is_empty() {
            self.reject_explicit_close(receiver, name);
        }
        ty
    }

    fn reject_explicit_close(&self, receiver: Option<&Expr>, name: Ident) {
        let owner = match receiver {
            Some(receiver) if matches!(receiver.kind, ExprKind::Super) => return,
            Some(receiver) => match self
                .results
                .expr_types
                .get(&receiver.span)
                .map(Ty::strip_refs)
            {
                Some(Ty::Adt { def, .. }) => *def,
                _ => return,
            },
            None => self.owner,
        };
        if !self.tcx.closes_itself(owner)
            && self.tcx.lang_items.get(LangItem::AutoCloseable) != Some(owner)
        {
            return;
        }
        let what = match receiver {
            Some(receiver) => format!("`{receiver}`"),
            None => "this object".to_owned(),
        };
        self.emit(
            Diagnostic::error("`close` cannot be called directly")
                .with_span(name.span)
                .with_note(format!(
                    "{what} is `AutoCloseable`, so `close` runs by itself when it is dropped"
                ))
                .with_help("to close it early, end its scope or pass it to a method that takes it"),
        );
    }

    pub(crate) fn finish_chain(&mut self, expr: &Expr, chain: PendingChain, expected: &Ty) {
        if !expected.references_unknown() {
            self.call_expectations
                .insert(chain.name.span, expected.clone());
        }
        let base_expected = self
            .receiver_expectation(&chain.receiver, chain.name, chain.args.len(), expected)
            .unwrap_or(Ty::Unknown);
        self.finish_pending(&chain.base, &base_expected);
        let base_ty = self
            .results
            .expr_types
            .get(&chain.base.span)
            .cloned()
            .unwrap_or(Ty::Unknown);
        let (receiver, nullable) = self.receiver_of(&chain.base, base_ty, chain.safe);
        let ty = self.method_call_rest(receiver, nullable, chain.name, &chain.args);
        self.finish_closure_args(&chain.args);
        self.results.expr_types.insert(expr.span, ty);
    }

    fn chained_receiver(
        &mut self,
        base: &Expr,
        name: Ident,
        args: &[Expr],
        safe: bool,
    ) -> Result<(Receiver, bool), Ty> {
        let ExprKind::MethodCall {
            name: base_name, ..
        } = &base.kind
        else {
            return Ok(self.receiver(base, safe));
        };
        self.deferrable.insert(base_name.span);
        let mut ty = self.check_expr(base);
        self.deferrable.remove(&base_name.span);
        if self.is_pending(base) {
            let expected = self.call_expectations.get(&name.span).cloned();
            let base_expected = expected
                .and_then(|expected| self.receiver_expectation(&ty, name, args.len(), &expected));
            match base_expected {
                Some(base_expected) => self.finish_pending(base, &base_expected),
                None if self.deferrable.remove(&name.span) => {
                    let placeholder = self.chain_placeholder(&ty, name, args.len());
                    self.pending_chains.insert(
                        name.span,
                        PendingChain {
                            base: base.clone(),
                            receiver: ty,
                            name,
                            args: args.to_vec(),
                            safe,
                        },
                    );
                    return Err(placeholder);
                }
                None => self.finish_pending(base, &Ty::Unknown),
            }
            ty = self
                .results
                .expr_types
                .get(&base.span)
                .cloned()
                .unwrap_or(Ty::Unknown);
        }
        Ok(self.receiver_of(base, ty, safe))
    }

    fn method_call_ty(
        &mut self,
        receiver: Option<&Expr>,
        name: Ident,
        args: &[Expr],
        safe: bool,
    ) -> Ty {
        let (receiver, nullable) = match receiver {
            Some(base) => match self.chained_receiver(base, name, args, safe) {
                Ok(receiver) => receiver,
                Err(placeholder) => return placeholder,
            },
            None => (Receiver::None, false),
        };
        self.method_call_rest(receiver, nullable, name, args)
    }

    fn method_call_rest(
        &mut self,
        receiver: Receiver,
        nullable: bool,
        name: Ident,
        args: &[Expr],
    ) -> Ty {
        let unknown = matches!(
            &receiver,
            Receiver::Type(ty) | Receiver::Value(ty) if is_unknown_code(ty)
        );
        if unknown {
            self.calls_unknown_code();
        }
        let arg_tys = self.check_closure_args(args);

        let ret = match receiver {
            Receiver::None => {
                let owner = self.owner;
                let candidates = self.tcx.methods_named(owner, &[], name.name);
                let statics: Vec<_> = candidates
                    .into_iter()
                    .filter(|(method, _)| method.receiver.is_none())
                    .collect();
                if statics.is_empty() {
                    Ty::Unknown
                } else {
                    let what = self.callee_kind(owner, name);
                    self.call(statics, args, &arg_tys, name, what)
                }
            }
            Receiver::Type(ty) => self.static_call(&ty, name, args, &arg_tys),
            Receiver::Value(ty) => self.instance_call(ty.strip_refs(), name, args, &arg_tys),
        };

        if nullable { ret.nullable() } else { ret }
    }

    fn static_call(&mut self, ty: &Ty, name: Ident, args: &[Expr], arg_tys: &[Ty]) -> Ty {
        let Some(def) = self.static_def(ty, name) else {
            return Ty::Unknown;
        };

        let candidates = self.tcx.methods_named(def, &[], name.name);
        if candidates.is_empty() {
            self.no_method(ty, name);
            return Ty::Unknown;
        }
        let statics: Vec<_> = candidates
            .into_iter()
            .filter(|(method, _)| method.receiver.is_none())
            .collect();
        if statics.is_empty() {
            self.emit(
                Diagnostic::error(format!(
                    "method `{}` needs an object to be called on",
                    name.name
                ))
                .with_span(name.span)
                .with_help(format!("call it on an object of `{ty}`")),
            );
            return Ty::Unknown;
        }
        let what = self.callee_kind(def, name);
        self.call(statics, args, arg_tys, name, what)
    }

    fn callee_kind(&self, def: DefId, name: Ident) -> &'static str {
        if self.tcx.sig(def).variant(name.name).is_some() {
            "variant"
        } else {
            "method"
        }
    }

    fn instance_call(&mut self, ty: &Ty, name: Ident, args: &[Expr], arg_tys: &[Ty]) -> Ty {
        match ty {
            Ty::Adt { .. } | Ty::Param(_) | Ty::Primitive(_) => {
                let receivers = self.receiver_adts(ty);
                let candidates: Vec<_> = receivers
                    .iter()
                    .flat_map(|(def, args)| self.tcx.methods_named(*def, args, name.name))
                    .collect();
                if candidates.is_empty() {
                    self.no_method(ty, name);
                    return Ty::Unknown;
                }
                let (candidates, unmet): (Vec<_>, Vec<_>) = candidates
                    .into_iter()
                    .partition(|(method, subst)| self.implementation_reaches(ty, method, subst));
                if candidates.is_empty() {
                    let (method, subst) = &unmet[0];
                    let iface = self.declaring_ty(method.owner, subst);
                    self.emit(
                        Diagnostic::error(format!(
                            "`{}` is only available where `{ty}` is a `{iface}`",
                            name.name
                        ))
                        .with_span(name.span)
                        .with_notes(self.tcx.unmet_conditions(ty, &iface)),
                    );
                    return Ty::Unknown;
                }
                let instance: Vec<_> = candidates
                    .into_iter()
                    .filter(|(method, _)| method.receiver.is_some())
                    .collect();
                if instance.is_empty() {
                    let owner = self.type_name(receivers[0].0);
                    self.emit(
                        Diagnostic::error(format!(
                            "`{}` belongs to the class `{owner}`",
                            name.name
                        ))
                        .with_span(name.span)
                        .with_help(format!("call it as `{owner}.{}(...)`", name.name)),
                    );
                    return Ty::Unknown;
                }
                self.call(instance, args, arg_tys, name, "method")
            }
            Ty::Void | Ty::Array(_) | Ty::Null => {
                self.no_method(ty, name);
                Ty::Unknown
            }
            _ => Ty::Unknown,
        }
    }

    fn implementation_reaches(&self, ty: &Ty, method: &MethodSig, subst: &Subst) -> bool {
        if !matches!(ty, Ty::Adt { .. }) || self.tcx.sig(method.owner).kind != AdtKind::Interface {
            return true;
        }
        let iface = self.declaring_ty(method.owner, subst);
        self.tcx.is_assignable(&self.param_env, ty, &iface)
    }

    fn declaring_ty(&self, owner: DefId, subst: &Subst) -> Ty {
        let args = self
            .tcx
            .sig(owner)
            .generics
            .iter()
            .map(|param| subst.get(&param.name).cloned().unwrap_or(Ty::Unknown))
            .collect();
        self.tcx.def_ty(owner, args)
    }

    /// The class whose static `member` is named through the type `ty`.
    fn static_def(&self, ty: &Ty, member: Ident) -> Option<DefId> {
        match ty {
            Ty::Adt { def, .. } => Some(*def),
            Ty::Primitive(primitive) => self.tcx.lang_items.primitive_impl(*primitive),
            Ty::Unknown => None,
            Ty::Param(param) => {
                self.emit(
                    Diagnostic::error(format!(
                        "cannot reach `{}` through type parameter `{param}`",
                        member.name
                    ))
                    .with_span(member.span)
                    .with_help(format!(
                        "`{param}` stands for whatever type the caller picks, so it has no static members; use a value of type `{param}` instead"
                    )),
                );
                None
            }
            _ => {
                self.error(member.span, format!("type `{ty}` has no static members"));
                None
            }
        }
    }

    pub(crate) fn receiver_adts(&self, ty: &Ty) -> Vec<(DefId, Vec<Ty>)> {
        match ty {
            Ty::Adt { def, args, .. } => vec![(*def, args.clone())],
            Ty::Primitive(primitive) => {
                let def = self.tcx.lang_items.primitive_impl(*primitive);
                def.into_iter().map(|def| (def, Vec::new())).collect()
            }
            Ty::Param(name) => {
                let bounds: Vec<_> = self
                    .param_env
                    .bounds(*name)
                    .iter()
                    .flat_map(|bound| self.receiver_adts(bound))
                    .collect();
                if !bounds.is_empty() {
                    return bounds;
                }
                let object = self.tcx.lang_items.get(LangItem::Object);
                object.into_iter().map(|def| (def, Vec::new())).collect()
            }
            _ => Vec::new(),
        }
    }

    fn no_method(&self, ty: &Ty, name: Ident) {
        if let Some(owner) = self.enum_with_variant(ty, name) {
            self.emit(
                Diagnostic::error(format!("the variant `{owner}.{}` has no fields", name.name))
                    .with_span(name.span)
                    .with_help(format!("write `{owner}.{}` without parentheses", name.name)),
            );
            return;
        }
        self.emit(
            Diagnostic::error(format!("no method named `{}` found for `{ty}`", name.name))
                .with_span(name.span)
                .with_label("method not found"),
        );
    }

    pub(crate) fn check_ctor_call(
        &mut self,
        def: DefId,
        ty_args: &[Ty],
        args: &[Expr],
        arg_tys: &[Ty],
        name: Ident,
    ) {
        let ctors = self.tcx.sig(def).ctors.clone();
        if ctors.is_empty() {
            if !args.is_empty() {
                self.error(
                    name.span,
                    format!(
                        "`{}` has no constructor that takes {}",
                        self.type_name(def),
                        plural(args.len(), "argument")
                    ),
                );
            }
            return;
        }
        let subst = self.tcx.subst_for(def, ty_args);
        let candidates = ctors
            .into_iter()
            .map(|ctor| (ctor, subst.clone()))
            .collect();
        self.call(candidates, args, arg_tys, name, "constructor");
    }

    fn check_new(
        &mut self,
        ty: &krelpin_ast::ast::Ty,
        args: &[Expr],
        span: Span,
        expected: Option<&Ty>,
    ) -> Ty {
        let ty = self.new_object_ty(ty, args, span, expected);
        self.finish_closure_args(args);
        ty
    }

    fn new_object_ty(
        &mut self,
        ty: &krelpin_ast::ast::Ty,
        args: &[Expr],
        span: Span,
        expected: Option<&Ty>,
    ) -> Ty {
        self.tcx.check_wf_inferred(&self.param_env, ty);
        let written_args = matches!(&ty.kind, TyKind::Path { args, .. } if !args.is_empty());
        let ty = self.tcx.lower_ty(ty);
        let arg_tys = self.check_closure_args(args);
        let ty = self.infer_diamond(ty, &arg_tys, span, expected);
        if !written_args {
            self.check_inferred_bounds(&ty, span);
        }

        match &ty {
            Ty::Adt {
                def,
                name,
                args: ty_args,
            } => {
                let sig = self.tcx.sig(*def);
                let problem = match sig.kind {
                    AdtKind::Interface => Some("an interface"),
                    AdtKind::Enum => Some("an enum"),
                    AdtKind::Class if sig.is_abstract => Some("an abstract class"),
                    _ => None,
                };
                if let Some(problem) = problem {
                    let diagnostic =
                        Diagnostic::error(format!("cannot create an object of {problem} `{name}`"))
                            .with_span(span);
                    let diagnostic = match sig.variants.first() {
                        Some(variant) if sig.kind == AdtKind::Enum => {
                            let case = variant.name.name;
                            let example = if variant.fields.is_empty() {
                                format!("{name}.{case}")
                            } else {
                                format!("{name}.{case}(...)")
                            };
                            diagnostic
                                .with_note("an enum has only the cases it declares")
                                .with_help(format!("use one of its cases, like `{example}`"))
                        }
                        _ => diagnostic,
                    };
                    self.emit(diagnostic);
                    return ty;
                }
                let name = Ident::new(*name, span);
                self.check_ctor_call(*def, ty_args, args, &arg_tys, name);
            }
            Ty::Param(name) => {
                self.error(
                    span,
                    format!("cannot create an object of generic parameter `{name}`"),
                );
            }
            ty if is_unknown_code(ty) => self.calls_unknown_code(),
            other => {
                self.emit(
                    Diagnostic::error(format!("cannot create an object of type `{other}`"))
                        .with_span(span)
                        .with_help("`new` takes the name of a class or record"),
                );
                return Ty::Unknown;
            }
        }
        ty
    }

    /// Type arguments inferred for `new HashSet()` must meet the bounds just
    /// like written ones, which `check_wf` has already checked.
    fn check_inferred_bounds(&self, ty: &Ty, span: Span) {
        let Ty::Adt { def, args, .. } = ty else {
            return;
        };
        let generics = &self.tcx.sig(*def).generics;
        if args.len() != generics.len() || args.iter().any(Ty::is_unknown) {
            return;
        }
        let subst = self.tcx.subst_for(*def, args);
        for (param, arg) in generics.iter().zip(args) {
            self.tcx
                .check_bound(&self.param_env, param, arg, &subst, span);
        }
    }

    fn check_index(&mut self, base: &Expr, index: &Expr) -> Ty {
        let base_ty = self.check_expr(base);
        self.check_expr_coerce(index, &Ty::INT);
        match base_ty.strip_refs() {
            Ty::Array(elem) => elem.as_ref().clone(),
            Ty::Unknown | Ty::Param(_) => Ty::Unknown,
            Ty::Nullable(_) => {
                self.error(base.span, format!("value of type `{base_ty}` may be null"));
                Ty::Unknown
            }
            other => {
                let diagnostic =
                    Diagnostic::error(format!("cannot index into a value of type `{other}`"))
                        .with_span(base.span);
                let has_get = match other {
                    Ty::Adt { def, args, .. } => !self
                        .tcx
                        .methods_named(*def, args, Symbol::intern("get"))
                        .is_empty(),
                    _ => false,
                };
                let diagnostic = if has_get {
                    diagnostic.with_help("use `.get(index)` instead")
                } else {
                    diagnostic
                };
                self.emit(diagnostic);
                Ty::Unknown
            }
        }
    }

    fn check_unary(&mut self, op: UnOp, operand: &Expr, span: Span) -> Ty {
        let ty = match op {
            UnOp::PreInc | UnOp::PreDec | UnOp::PostInc | UnOp::PostDec => {
                self.check_place(operand)
            }
            UnOp::Neg | UnOp::Not | UnOp::BitNot => self.check_expr(operand),
        };
        let value = ty.strip_refs().clone();
        if value.is_unknown() {
            return Ty::Unknown;
        }

        let ok = match op {
            UnOp::Not => value.is_boolean(),
            UnOp::BitNot => value.is_integral(),
            _ => value.is_numeric(),
        };
        if !ok && op == UnOp::Not {
            self.mismatch(operand.span, &Ty::BOOLEAN, &value);
            return Ty::Unknown;
        }
        if !ok {
            let symbol = match op {
                UnOp::Neg => "-",
                UnOp::Not => "!",
                UnOp::BitNot => "~",
                UnOp::PreInc | UnOp::PostInc => "++",
                UnOp::PreDec | UnOp::PostDec => "--",
            };
            self.error(span, format!("cannot apply `{symbol}` to `{value}`"));
            return Ty::Unknown;
        }

        match (op, value.primitive()) {
            (UnOp::Neg | UnOp::BitNot, Some(primitive)) => promote_unary(primitive),
            _ => value,
        }
    }

    fn check_binary(&mut self, op: BinOp, lhs: &Expr, rhs: &Expr, span: Span) -> Ty {
        if matches!(op, BinOp::And | BinOp::Or) {
            self.check_expr_coerce(lhs, &Ty::BOOLEAN);
            let (when_true, when_false) = self.null_checks(lhs);
            let narrowing = if op == BinOp::And {
                when_true
            } else {
                when_false
            };
            self.with_narrowing(&narrowing, |fcx| fcx.check_expr_coerce(rhs, &Ty::BOOLEAN));
            return Ty::BOOLEAN;
        }

        let left = self.check_expr(lhs);
        let right = self.check_expr(rhs);

        if op == BinOp::Elvis {
            let left = match left {
                Ty::Ref { mutable: false, ty }
                    if matches!(ty.as_ref(), Ty::Nullable(_)) && self.tcx.is_copy(&ty) =>
                {
                    *ty
                }
                other => other,
            };
            return match &left {
                Ty::Nullable(inner) => {
                    self.common_or_error(inner, &right, span, "the sides of `?:`")
                }
                Ty::Null | Ty::Unknown => right,
                other => {
                    self.emit(
                        Diagnostic::lint(
                            "unnecessary_elvis",
                            "the left side of `?:` can never be null",
                        )
                        .with_span(lhs.span)
                        .with_help("remove the `?:` and the default value"),
                    );
                    self.common_or_error(other, &right, span, "the sides of `?:`")
                }
            };
        }

        let (l, r) = (left.strip_refs(), right.strip_refs());
        let is_comparison = matches!(
            op,
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
        );
        if l.is_unknown() || r.is_unknown() {
            return if is_comparison {
                Ty::BOOLEAN
            } else if op == BinOp::Add && (self.tcx.is_string(l) || self.tcx.is_string(r)) {
                self.tcx.string_ty()
            } else {
                Ty::Unknown
            };
        }

        if matches!(op, BinOp::Eq | BinOp::Ne) {
            self.check_equality(l, r, op, span);
            return Ty::BOOLEAN;
        }

        let both = |pred: fn(&Ty) -> bool| pred(l) && pred(r);
        let result = match op {
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                both(Ty::is_numeric).then_some(Ty::BOOLEAN)
            }
            BinOp::Add if self.tcx.is_string(l) || self.tcx.is_string(r) => {
                Some(self.tcx.string_ty())
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => numeric_result(l, r),
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor if both(Ty::is_boolean) => {
                Some(Ty::BOOLEAN)
            }
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => both(Ty::is_integral)
                .then(|| numeric_result(l, r))
                .flatten(),
            BinOp::Shl | BinOp::Shr | BinOp::UShr => both(Ty::is_integral)
                .then(|| l.primitive().map(promote_unary))
                .flatten(),
            BinOp::Eq | BinOp::Ne | BinOp::And | BinOp::Or | BinOp::Elvis => None,
        };

        result.unwrap_or_else(|| {
            self.error(
                span,
                format!("cannot apply `{}` to `{l}` and `{r}`", op.as_str()),
            );
            Ty::Unknown
        })
    }

    fn check_equality(&self, l: &Ty, r: &Ty, op: BinOp, span: Span) {
        if matches!(
            (l, r),
            (Ty::Null, Ty::Nullable(_)) | (Ty::Nullable(_), Ty::Null)
        ) {
            return;
        }
        let compatible = match (l.non_null(), r.non_null()) {
            (Ty::Null, Ty::Primitive(_)) | (Ty::Primitive(_), Ty::Null) => false,
            (Ty::Null, _) | (_, Ty::Null) => return,
            (l @ Ty::Primitive(_), r @ Ty::Primitive(_)) => {
                (l.is_numeric() && r.is_numeric()) || (l.is_boolean() && r.is_boolean())
            }
            (l, r) => self.is_assignable(l, r) || self.is_assignable(r, l),
        };
        if !compatible {
            self.error(span, format!("cannot compare `{l}` with `{r}`"));
            return;
        }

        let (l, r) = (l.non_null(), r.non_null());
        let ty = if self.is_assignable(l, r) { r } else { l };
        if self.is_equatable(ty) {
            return;
        }
        let help = match ty {
            Ty::Param(name) => format!("add the bound `{name} extends Equatable<{name}>`"),
            Ty::Adt { def, .. } if self.tcx.sig(*def).kind == AdtKind::Record => {
                if self.tcx.sig(*def).generics.is_empty() {
                    format!(
                        "a record is `Equatable` when all of its components are, \
                         and one of `{ty}`'s is not"
                    )
                } else {
                    "a generic record is `Equatable` when its type parameters are bounded, \
                     like `<T extends Equatable<T>>`"
                        .to_owned()
                }
            }
            ty => format!("implement `Equatable<{ty}>` for `{ty}`"),
        };
        self.emit(
            Diagnostic::error(format!(
                "values of type `{ty}` cannot be compared with `{}`",
                op.as_str()
            ))
            .with_span(span)
            .with_help(help),
        );
    }

    fn is_equatable(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Primitive(_) | Ty::Unknown => true,
            ty => {
                self.is_assignable(ty, &self.tcx.lang_ty(LangItem::Equatable))
                    || self.tcx.satisfies_bound(
                        &self.param_env,
                        ty,
                        &self.tcx.def_ty_of(LangItem::Equatable, ty),
                    )
            }
        }
    }

    fn check_assign(&mut self, op: Option<BinOp>, lhs: &Expr, rhs: &Expr, span: Span) -> Ty {
        let target = self.check_place(lhs);
        let assigned_local = match lhs.kind {
            ExprKind::Name(name) => match self.tcx.resolutions.get(name.span) {
                Some(Res::Local(decl)) => Some(decl),
                _ => None,
            },
            _ => None,
        };
        if let Some(decl) = assigned_local {
            for scope in &mut self.narrowed {
                scope.remove(&decl);
            }
        }

        match op {
            None if matches!(target, Ty::Ref { mutable: true, .. }) => {
                let actual = self.check_expr(rhs);
                if matches!(actual, Ty::Ref { .. } | Ty::Null | Ty::Unknown) {
                    self.require_assignable(rhs, &actual, &target);
                } else {
                    let inner = target.strip_refs().clone();
                    self.require_assignable(rhs, &actual, &inner);
                    return inner;
                }
            }
            None => {
                self.check_expr_coerce(rhs, &target);
            }
            Some(op) => {
                let value = self.check_expr(rhs);
                let value = value.strip_refs();
                let target_value = target.strip_refs();
                let ok = target_value.is_unknown()
                    || value.is_unknown()
                    || (op == BinOp::Add && self.tcx.is_string(target_value))
                    || match op {
                        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => {
                            (target_value.is_boolean() && value.is_boolean())
                                || (target_value.is_integral() && value.is_integral())
                        }
                        BinOp::Shl | BinOp::Shr | BinOp::UShr => {
                            target_value.is_integral() && value.is_integral()
                        }
                        _ => target_value.is_numeric() && value.is_numeric(),
                    };
                if !ok {
                    self.error(
                        span,
                        format!(
                            "cannot apply `{}=` to `{target_value}` and `{value}`",
                            op.as_str()
                        ),
                    );
                }
            }
        }
        target
    }

    fn check_place(&mut self, expr: &Expr) -> Ty {
        match &expr.kind {
            ExprKind::Name(name) => match self.tcx.resolutions.get(name.span) {
                Some(Res::Local(decl)) => {
                    let ty = self.locals.get(&decl).cloned().unwrap_or(Ty::Unknown);
                    self.results.expr_types.insert(expr.span, ty.clone());
                    ty
                }
                _ => self.check_expr(expr),
            },
            ExprKind::Index { .. } => self.check_expr(expr),
            ExprKind::Field {
                expr: base,
                name,
                safe,
            } => {
                if *safe {
                    self.error(expr.span, "cannot assign through `?.`");
                }
                self.assigning = Some(name.span);
                let (ty, field) = self.field_access(base, *name, *safe);
                self.assigning = None;
                self.results.expr_types.insert(expr.span, ty.clone());
                if let Some(field) = field {
                    let through_this = matches!(base.kind, ExprKind::This);
                    self.check_field_assignable(&field, *name, through_this);
                } else if name.name.as_str() == "length"
                    && matches!(
                        self.results.expr_types.get(&base.span).map(Ty::strip_refs),
                        Some(Ty::Array(_))
                    )
                {
                    self.emit(
                        Diagnostic::error("cannot assign to the length of an array")
                            .with_span(name.span)
                            .with_note("an array keeps the length it was created with")
                            .with_help("create a new array, or use an `ArrayList`"),
                    );
                }
                ty
            }
            _ => {
                let ty = self.check_expr(expr);
                self.error(expr.span, "invalid left-hand side of assignment");
                ty
            }
        }
    }

    fn check_field_assignable(&self, field: &FieldSig, name: Ident, through_this: bool) {
        match field.storage {
            FieldStorage::Instance if self.tcx.sig(field.owner).kind == AdtKind::Record => self
                .emit(
                    Diagnostic::error(format!(
                        "cannot assign to `{}`, a component of the record `{}`",
                        name.name,
                        self.type_name(field.owner)
                    ))
                    .with_span(name.span)
                    .with_note("the components of a record never change")
                    .with_help("make a changed copy with `with { ... }`"),
                ),
            FieldStorage::Instance
                if field.is_final
                    && !(self.in_ctor && through_this && field.owner == self.owner) =>
            {
                self.emit(
                    Diagnostic::error(format!("cannot assign to `final` field `{}`", name.name))
                        .with_span(name.span)
                        .with_note("a `final` field is given its value once, in a constructor")
                        .with_help(format!(
                            "remove `final` from `{}` to change it after construction",
                            name.name
                        )),
                );
            }
            FieldStorage::Instance => {}
            FieldStorage::Static(_) => self.emit(
                Diagnostic::error(format!(
                    "cannot assign to `static final` field `{}`",
                    name.name
                ))
                .with_span(name.span)
                .with_note("a `static` field can be used from many threads at once")
                .with_help(
                    "store a type that can be changed safely, like `AtomicInt` or `Mutex<T>`",
                ),
            ),
        }
    }

    fn check_cast(&self, from: &Ty, to: &Ty, span: Span) {
        let (from_value, to_value) = (from.strip_refs(), to.strip_refs());
        let invalid = match (from_value.primitive(), to_value.primitive()) {
            (Some(a), Some(b)) => (a == PrimitiveTy::Boolean) != (b == PrimitiveTy::Boolean),
            (Some(_), None) | (None, Some(_)) => {
                !(from_value.is_unknown()
                    || to_value.is_unknown()
                    || self.is_assignable(from_value, to_value)
                    || self.is_assignable(to_value, from_value))
            }
            (None, None) => false,
        };
        if invalid {
            self.error(span, format!("cannot cast `{from}` to `{to}`"));
        }
    }

    pub(crate) fn common_or_error(&self, a: &Ty, b: &Ty, span: Span, what: &str) -> Ty {
        if a.is_unknown() || b.is_unknown() {
            return if a.is_unknown() { b.clone() } else { a.clone() };
        }
        self.tcx
            .common_ty(&self.param_env, a, b)
            .unwrap_or_else(|| {
                self.error(
                    span,
                    format!("{what} have incompatible types `{a}` and `{b}`"),
                );
                Ty::Unknown
            })
    }

    fn lit_ty(&self, lit: &Lit) -> Ty {
        let suffix = lit.suffix.map(Symbol::as_str);
        match lit.kind {
            LitKind::Integer => match suffix {
                Some("L" | "l") => Ty::LONG,
                _ => Ty::INT,
            },
            LitKind::Float => match suffix {
                Some("f" | "F") => Ty::FLOAT,
                _ => Ty::DOUBLE,
            },
            LitKind::Char => Ty::CHAR,
            LitKind::Str | LitKind::TextBlock => self.tcx.string_ty(),
            LitKind::Err => Ty::Unknown,
        }
    }
}

fn numeric_result(l: &Ty, r: &Ty) -> Option<Ty> {
    match (l.primitive(), r.primitive()) {
        (Some(a), Some(b)) if l.is_numeric() && r.is_numeric() => promote(a, b),
        _ => None,
    }
}

fn narrows_literal(expr: &Expr, expected: &Ty) -> bool {
    is_int_literal(expr)
        && matches!(
            expected.non_null(),
            Ty::Primitive(
                PrimitiveTy::Byte | PrimitiveTy::Short | PrimitiveTy::Char | PrimitiveTy::Float
            )
        )
}

fn is_int_literal(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Lit(lit) => lit.kind == LitKind::Integer && lit.suffix.is_none(),
        ExprKind::Unary {
            op: UnOp::Neg,
            expr,
        } => is_int_literal(expr),
        _ => false,
    }
}

fn is_unknown_code(ty: &Ty) -> bool {
    matches!(ty.strip_refs().non_null(), Ty::Unknown)
}
