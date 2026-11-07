use std::collections::BTreeMap;

use krelpin_ast::ast::UnOp;

use crate::hir::{
    Arm, ArmBody, Block, Capture, ClosureBody, ClosureKind, Expr, ExprKind, LocalId, Pat, PatKind,
    Stmt, StmtKind,
};

pub(crate) fn captures(body: &ClosureBody, first_inner: LocalId) -> Vec<Capture> {
    let mut finder = CaptureFinder::new(first_inner);
    match body {
        ClosureBody::Expr(expr) => finder.expr(expr, false),
        ClosureBody::Block(block) => finder.block(block),
    }
    finder.finish()
}

pub(crate) fn expr_captures(expr: &Expr, first_inner: LocalId) -> Vec<Capture> {
    let mut finder = CaptureFinder::new(first_inner);
    finder.expr(expr, false);
    finder.finish()
}

struct CaptureFinder {
    first_inner: LocalId,
    found: BTreeMap<LocalId, bool>,
}

impl CaptureFinder {
    fn new(first_inner: LocalId) -> CaptureFinder {
        CaptureFinder {
            first_inner,
            found: BTreeMap::new(),
        }
    }

    fn finish(self) -> Vec<Capture> {
        self.found
            .into_iter()
            .map(|(local, mutable)| Capture { local, mutable })
            .collect()
    }

    fn local(&mut self, local: LocalId, mutable: bool) {
        if local < self.first_inner {
            *self.found.entry(local).or_default() |= mutable;
        }
    }

    fn block(&mut self, block: &Block) {
        for stmt in &block.stmts {
            self.stmt(stmt);
        }
    }

    fn stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Let { init, .. } => {
                if let Some(init) = init {
                    self.expr(init, false);
                }
            }
            StmtKind::Expr(expr)
            | StmtKind::Yield(expr)
            | StmtKind::Throw(expr)
            | StmtKind::Return(Some(expr)) => self.expr(expr, false),
            StmtKind::Block(block) => self.block(block),
            StmtKind::If { cond, then, els } => {
                self.expr(cond, false);
                self.block(then);
                if let Some(els) = els {
                    self.block(els);
                }
            }
            StmtKind::Loop {
                cond, update, body, ..
            } => {
                if let Some(cond) = cond {
                    self.expr(cond, false);
                }
                for expr in update {
                    self.expr(expr, false);
                }
                self.block(body);
            }
            StmtKind::ForEach { iter, body, .. } => {
                self.expr(iter, false);
                self.block(body);
            }
            StmtKind::Switch { scrutinee, arms } => {
                self.expr(scrutinee, false);
                self.arms(arms);
            }
            StmtKind::Try {
                body,
                catches,
                finally,
            } => {
                self.block(body);
                for catch in catches {
                    self.block(&catch.body);
                }
                if let Some(finally) = finally {
                    self.block(finally);
                }
            }
            StmtKind::Labeled { body, .. } => self.stmt(body),
            StmtKind::Return(None) | StmtKind::Break(_) | StmtKind::Continue(_) => {}
        }
    }

    fn arms(&mut self, arms: &[Arm]) {
        for arm in arms {
            for pat in &arm.pats {
                self.pat(pat);
            }
            if let Some(guard) = &arm.guard {
                self.expr(guard, false);
            }
            match &arm.body {
                ArmBody::Expr(expr) | ArmBody::Throw(expr) => self.expr(expr, false),
                ArmBody::Block(block) => self.block(block),
            }
        }
    }

    fn pat(&mut self, pat: &Pat) {
        match &pat.kind {
            PatKind::Lit(expr) => self.expr(expr, false),
            PatKind::Variant { fields, .. } | PatKind::Record { fields, .. } => {
                for field in fields {
                    self.pat(field);
                }
            }
            PatKind::Wild | PatKind::Binding { .. } | PatKind::Const { .. } => {}
        }
    }

    fn exprs(&mut self, exprs: &[Expr]) {
        for expr in exprs {
            self.expr(expr, false);
        }
    }

    fn expr(&mut self, expr: &Expr, mutated: bool) {
        match &expr.kind {
            ExprKind::Local(local) => self.local(*local, mutated),
            ExprKind::Field { base, .. } => self.expr(base, mutated),
            ExprKind::Index { base, index } => {
                self.expr(base, mutated);
                self.expr(index, false);
            }
            ExprKind::Call { receiver, args, .. } => {
                if let Some(receiver) = receiver {
                    self.expr(receiver, false);
                }
                self.exprs(args);
            }
            ExprKind::New { args, .. } => self.exprs(args),
            ExprKind::CtorCall { this, args, .. } => {
                self.expr(this, false);
                self.exprs(args);
            }
            ExprKind::NewArray { len } => self.expr(len, false),
            ExprKind::Len { array } => self.expr(array, false),
            ExprKind::Array { elems } => self.exprs(elems),
            ExprKind::Unary { op, expr: operand } => {
                let changes = matches!(
                    op,
                    UnOp::PreInc | UnOp::PreDec | UnOp::PostInc | UnOp::PostDec
                );
                self.expr(operand, changes);
            }
            ExprKind::Borrow {
                mutable,
                expr: operand,
            } => self.expr(operand, *mutable),
            ExprKind::Binary { lhs, rhs, .. } => {
                self.expr(lhs, false);
                self.expr(rhs, false);
            }
            ExprKind::With { base, fields, .. } => {
                self.expr(base, false);
                for field in fields {
                    self.expr(&field.value, false);
                }
            }
            ExprKind::Equals { lhs, rhs, .. } => {
                self.expr(lhs, false);
                self.expr(rhs, false);
            }
            ExprKind::Assign { place, value, .. } => {
                self.expr(place, true);
                self.expr(value, false);
            }
            ExprKind::If { cond, then, els } => {
                self.expr(cond, false);
                self.expr(then, false);
                self.expr(els, false);
            }
            ExprKind::Is { expr: operand, pat } => {
                self.expr(operand, false);
                self.pat(pat);
            }
            ExprKind::Cast { expr: operand }
            | ExprKind::Await { expr: operand }
            | ExprKind::Deref { expr: operand, .. } => self.expr(operand, false),
            ExprKind::Switch { scrutinee, arms } => {
                self.expr(scrutinee, false);
                self.arms(arms);
            }
            ExprKind::Closure(closure) => {
                for capture in &closure.captures {
                    self.local(capture.local, capture.mutable);
                }
                if let ClosureKind::MethodRef {
                    bound: Some(bound), ..
                } = &closure.kind
                {
                    self.expr(bound, false);
                }
            }
            ExprKind::Lit(_)
            | ExprKind::Bool(_)
            | ExprKind::Null
            | ExprKind::Static { .. }
            | ExprKind::Unresolved => {}
        }
    }
}
