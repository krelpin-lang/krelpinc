use std::collections::HashMap;

use krelpin_ast::ast::{BinOp, Block, Expr, ExprKind, Stmt, StmtKind, UnOp};
use krelpin_errors::Diagnostic;
use krelpin_resolve::Res;
use krelpin_span::Span;

use crate::check::FnCtxt;
use crate::lang_items::LangItem;
use crate::pat::Coverage;
use crate::ty::Ty;

impl FnCtxt<'_, '_> {
    pub(crate) fn check_block(&mut self, block: &Block) -> bool {
        self.narrowed.push(HashMap::new());
        let mut diverges = false;
        for stmt in &block.stmts {
            diverges |= self.check_stmt(stmt);
        }
        self.narrowed.pop();
        diverges
    }

    fn check_stmt(&mut self, stmt: &Stmt) -> bool {
        match &stmt.kind {
            StmtKind::Local(local) => {
                let ty = self.lower_ty(&local.ty);
                if let Some(init) = &local.init {
                    self.check_expr_coerce(init, &ty);
                }
                self.locals.insert(local.name.span, ty);
                false
            }
            StmtKind::Expr(expr) => {
                self.check_expr(expr);
                false
            }
            StmtKind::Block(block) => self.check_block(block),
            StmtKind::If { cond, then, els } => {
                self.check_expr_coerce(cond, &Ty::BOOLEAN);
                let (when_true, when_false) = self.null_checks(cond);
                let then_diverges = self.with_narrowing(&when_true, |fcx| fcx.check_stmt(then));
                let else_diverges = match els {
                    Some(els) => self.with_narrowing(&when_false, |fcx| fcx.check_stmt(els)),
                    None => false,
                };
                // `if (x == null) { return; }` and `{ break; }` both mean
                // that `x` isn't null after the `if`.
                if (then_diverges || jumps_away(then)) && els.is_none() {
                    self.narrow_here(&when_false);
                }
                then_diverges && else_diverges
            }
            StmtKind::While { cond, body } => {
                self.check_expr_coerce(cond, &Ty::BOOLEAN);
                let (when_true, _) = self.null_checks(cond);
                self.with_narrowing(&when_true, |fcx| fcx.check_stmt(body));
                is_true(cond) && !contains_break(body)
            }
            StmtKind::DoWhile { body, cond } => {
                let diverges = self.check_stmt(body);
                self.check_expr_coerce(cond, &Ty::BOOLEAN);
                diverges
            }
            StmtKind::For {
                init,
                cond,
                update,
                body,
            } => {
                self.narrowed.push(HashMap::new());
                for stmt in init {
                    self.check_stmt(stmt);
                }
                if let Some(cond) = cond {
                    self.check_expr_coerce(cond, &Ty::BOOLEAN);
                }
                for expr in update {
                    self.check_expr(expr);
                }
                self.check_stmt(body);
                self.narrowed.pop();
                cond.as_ref().is_none_or(is_true) && !contains_break(body)
            }
            StmtKind::ForEach {
                ty,
                name,
                iter,
                body,
                ..
            } => {
                let iter_ty = self.check_expr(iter);
                let elem = self.element_ty(&iter_ty, iter.span);
                let declared = self.lower_ty(ty);
                let copied = match &elem {
                    Ty::Ref { ty: inner, .. } => self.is_assignable(inner, &declared),
                    _ => false,
                };
                if !copied && !self.is_assignable(&elem, &declared) {
                    self.mismatch(ty.span, &declared, &elem);
                }
                self.locals.insert(name.span, declared);
                self.check_stmt(body);
                false
            }
            StmtKind::Switch { scrutinee, arms } => {
                let scrutinee_ty = self.check_expr(scrutinee);
                let mut all_diverge = true;
                let mut match_arms = Vec::new();
                for arm in arms {
                    match_arms.extend(self.check_case_label(&arm.label, &scrutinee_ty));
                    all_diverge &= self.check_stmt(&arm.body) && !contains_break(&arm.body);
                }
                let coverage = if self.is_enum(&scrutinee_ty) {
                    Coverage::Required("this `switch` statement")
                } else {
                    Coverage::Optional
                };
                let exhaustive = self.check_match(&scrutinee_ty, &match_arms, coverage, stmt.span);
                exhaustive && all_diverge
            }
            StmtKind::Try {
                body,
                catches,
                finally,
            } => {
                self.enter_try(catches);
                let mut diverges = self.check_block(body);
                let thrown = self.exit_try();
                let mut caught = Vec::new();
                for catch in catches {
                    let ty = self.check_catch(catch, &thrown, &mut caught);
                    self.locals.insert(catch.name.span, ty);
                    diverges &= self.check_block(&catch.body);
                }
                let finally_diverges = finally
                    .as_ref()
                    .is_some_and(|finally| self.check_block(finally));
                diverges || finally_diverges
            }
            StmtKind::Return(value) => {
                self.check_return(value.as_ref(), stmt.span);
                true
            }
            StmtKind::Yield(value) => {
                let ty = self.check_expr(value);
                if let Some(yields) = self.yields.last_mut() {
                    yields.push(ty);
                }
                true
            }
            StmtKind::Throw(value) => {
                self.check_throw(value);
                true
            }
            StmtKind::Break | StmtKind::Continue | StmtKind::Empty => false,
        }
    }

    fn check_return(&mut self, value: Option<&Expr>, span: Span) {
        let ret = self.ret.clone();
        match (value, &ret) {
            (Some(value), Ty::Void) => {
                self.check_expr(value);
                self.emit(
                    Diagnostic::error("cannot return a value from a method that returns `void`")
                        .with_span(value.span)
                        .with_help("remove the value, or change the return type of the method"),
                );
            }
            (Some(value), Ty::Unknown) if !self.inferred_returns.is_empty() => {
                let ty = self.check_expr(value);
                if let Some(returns) = self.inferred_returns.last_mut() {
                    returns.push(ty);
                }
            }
            (Some(value), ret) => {
                self.check_expr_coerce(value, ret);
            }
            (None, Ty::Void | Ty::Unknown) => {}
            (None, ret) => {
                self.emit(
                    Diagnostic::error(format!("this method must return a `{ret}`"))
                        .with_span(span)
                        .with_label("missing value"),
                );
            }
        }
    }

    fn element_ty(&self, iter_ty: &Ty, span: Span) -> Ty {
        let elem = match iter_ty.strip_refs() {
            Ty::Array(elem) => elem.as_ref().clone(),
            Ty::Adt { def, args, .. } => {
                let iterable = self.tcx.lang_items.get(LangItem::Iterable);
                match iterable.and_then(|iterable| self.tcx.upcast(*def, args, iterable)) {
                    Some(args) => args.first().cloned().unwrap_or(Ty::Unknown),
                    None => {
                        self.cannot_iterate(iter_ty, span);
                        return Ty::Unknown;
                    }
                }
            }
            Ty::Primitive(_) | Ty::Null | Ty::Void => {
                self.cannot_iterate(iter_ty, span);
                return Ty::Unknown;
            }
            Ty::Nullable(_) => {
                self.error(span, format!("value of type `{iter_ty}` may be null"));
                return Ty::Unknown;
            }
            _ => return Ty::Unknown,
        };

        if elem.is_unknown() || matches!(elem, Ty::Ref { .. }) {
            return elem;
        }
        Ty::Ref {
            mutable: false,
            ty: Box::new(elem),
        }
    }

    fn cannot_iterate(&self, iter_ty: &Ty, span: Span) {
        self.emit(
            Diagnostic::error(format!("cannot iterate over a value of type `{iter_ty}`"))
                .with_span(span)
                .with_note("`for` loops work with arrays and types that implement `Iterable`"),
        );
    }

    pub(crate) fn null_checks(&self, cond: &Expr) -> (Vec<Span>, Vec<Span>) {
        match &cond.kind {
            ExprKind::Binary { op, lhs, rhs } => match op {
                BinOp::Ne | BinOp::Eq => {
                    let checked = match (&lhs.kind, &rhs.kind) {
                        (ExprKind::Name(name), ExprKind::Null)
                        | (ExprKind::Null, ExprKind::Name(name)) => self.local_decl(name.span),
                        _ => None,
                    };
                    let checked: Vec<Span> = checked.into_iter().collect();
                    if *op == BinOp::Ne {
                        (checked, Vec::new())
                    } else {
                        (Vec::new(), checked)
                    }
                }
                BinOp::And => {
                    let (mut when_true, _) = self.null_checks(lhs);
                    when_true.extend(self.null_checks(rhs).0);
                    (when_true, Vec::new())
                }
                BinOp::Or => {
                    let (_, mut when_false) = self.null_checks(lhs);
                    when_false.extend(self.null_checks(rhs).1);
                    (Vec::new(), when_false)
                }
                _ => (Vec::new(), Vec::new()),
            },
            ExprKind::Unary {
                op: UnOp::Not,
                expr,
            } => {
                let (when_true, when_false) = self.null_checks(expr);
                (when_false, when_true)
            }
            _ => (Vec::new(), Vec::new()),
        }
    }

    fn local_decl(&self, span: Span) -> Option<Span> {
        match self.tcx.resolutions.get(span) {
            Some(Res::Local(decl)) => Some(decl),
            _ => None,
        }
    }

    pub(crate) fn with_narrowing<T>(
        &mut self,
        decls: &[Span],
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let scope = self.narrowing_for(decls);
        self.narrowed.push(scope);
        let result = f(self);
        self.narrowed.pop();
        result
    }

    fn narrow_here(&mut self, decls: &[Span]) {
        let scope = self.narrowing_for(decls);
        if let Some(current) = self.narrowed.last_mut() {
            current.extend(scope);
        }
    }

    fn narrowing_for(&self, decls: &[Span]) -> HashMap<Span, Ty> {
        decls
            .iter()
            .map(|&decl| (decl, self.local_ty(decl).non_null().clone()))
            .collect()
    }
}

fn is_true(expr: &Expr) -> bool {
    matches!(expr.kind, ExprKind::Bool(true))
}

/// Whether `stmt` always leaves the enclosing loop iteration with `break` or
/// `continue`, so the statements after it in the same block don't run.
fn jumps_away(stmt: &Stmt) -> bool {
    match &stmt.kind {
        StmtKind::Break | StmtKind::Continue => true,
        StmtKind::Block(block) => block.stmts.iter().any(jumps_away),
        StmtKind::If {
            then,
            els: Some(els),
            ..
        } => jumps_away(then) && jumps_away(els),
        _ => false,
    }
}

fn contains_break(stmt: &Stmt) -> bool {
    match &stmt.kind {
        StmtKind::Break => true,
        StmtKind::Block(block) => block.stmts.iter().any(contains_break),
        StmtKind::If { then, els, .. } => {
            contains_break(then) || els.as_deref().is_some_and(contains_break)
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            body.stmts.iter().any(contains_break)
                || catches
                    .iter()
                    .any(|catch| catch.body.stmts.iter().any(contains_break))
                || finally
                    .as_ref()
                    .is_some_and(|finally| finally.stmts.iter().any(contains_break))
        }
        _ => false,
    }
}
