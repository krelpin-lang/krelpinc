use std::fmt::Write;

use krelpin_ast::ast::UnOp;
use krelpin_span::Symbol;
use krelpin_typeck::{Callee, Tcx, Ty};

use crate::hir::{
    Arm, ArmBody, Block, Body, BodyKind, BodyValue, Closure, ClosureBody, ClosureKind, Dispatch,
    Expr, ExprKind, LocalId, LoopKind, Pat, PatKind, Stmt, StmtKind,
};

pub fn print<'b>(bodies: impl IntoIterator<Item = &'b Body>, tcx: &Tcx<'_>) -> String {
    let mut out = String::new();
    for body in bodies {
        let mut printer = Printer {
            tcx,
            body,
            out: String::new(),
            depth: 0,
        };
        printer.body();
        out.push_str(&printer.out);
        out.push('\n');
    }
    out
}

struct Printer<'a, 'tcx> {
    tcx: &'a Tcx<'tcx>,
    body: &'a Body,
    out: String,
    depth: usize,
}

impl Printer<'_, '_> {
    fn body(&mut self) {
        let owner = self.tcx.sig(self.body.owner).name.name;
        let params: Vec<String> = self
            .body
            .this
            .iter()
            .chain(&self.body.params)
            .map(|&local| format!("{}: {}", self.name(local), self.body.local(local).ty))
            .collect();
        let keyword = match self.body.kind {
            BodyKind::Method => "fn",
            BodyKind::Constructor => "ctor",
            BodyKind::FieldInit => "field",
        };
        let _ = write!(
            self.out,
            "{keyword} {owner}.{}({}) -> {} ",
            self.body.name,
            params.join(", "),
            self.body.ret
        );
        match &self.body.value {
            BodyValue::Block(block) => self.block(block),
            BodyValue::Expr(expr) => {
                self.out.push_str("= ");
                self.expr(expr);
                self.out.push(';');
            }
        }
        self.out.push('\n');
    }

    fn name(&self, local: LocalId) -> String {
        format!("{}_{}", self.body.local(local).name, local.0)
    }

    fn line(&mut self) {
        self.out.push('\n');
        for _ in 0..self.depth {
            self.out.push_str("    ");
        }
    }

    fn block(&mut self, block: &Block) {
        self.out.push('{');
        self.depth += 1;
        for stmt in &block.stmts {
            self.line();
            self.stmt(stmt);
        }
        self.depth -= 1;
        self.line();
        self.out.push('}');
    }

    fn stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Let { local, init } => {
                let decl = self.body.local(*local);
                let _ = write!(self.out, "let {}: {}", self.name(*local), decl.ty);
                if let Some(init) = init {
                    self.out.push_str(" = ");
                    self.expr(init);
                }
                self.out.push(';');
            }
            StmtKind::Expr(expr) => {
                self.expr(expr);
                self.out.push(';');
            }
            StmtKind::Block(block) => self.block(block),
            StmtKind::If { cond, then, els } => {
                self.out.push_str("if ");
                self.expr(cond);
                self.out.push(' ');
                self.block(then);
                if let Some(els) = els {
                    self.out.push_str(" else ");
                    self.block(els);
                }
            }
            StmtKind::Loop {
                kind,
                cond,
                update,
                body,
            } => {
                self.out.push_str(match kind {
                    LoopKind::While => "while ",
                    LoopKind::DoWhile => "do-while ",
                });
                match cond {
                    Some(cond) => self.expr(cond),
                    None => self.out.push_str("true"),
                }
                for expr in update {
                    self.out.push_str(" then ");
                    self.expr(expr);
                }
                self.out.push(' ');
                self.block(body);
            }
            StmtKind::ForEach { local, iter, body } => {
                let _ = write!(self.out, "for {} in ", self.name(*local));
                self.expr(iter);
                self.out.push(' ');
                self.block(body);
            }
            StmtKind::Switch { scrutinee, arms } => self.switch(scrutinee, arms),
            StmtKind::Try {
                body,
                catches,
                finally,
            } => {
                self.out.push_str("try ");
                self.block(body);
                for catch in catches {
                    let tys: Vec<String> = catch.tys.iter().map(ToString::to_string).collect();
                    let _ = write!(
                        self.out,
                        " catch {}: {} ",
                        self.name(catch.local),
                        tys.join(" | ")
                    );
                    self.block(&catch.body);
                }
                if let Some(finally) = finally {
                    self.out.push_str(" finally ");
                    self.block(finally);
                }
            }
            StmtKind::Return(value) => {
                self.out.push_str("return");
                if let Some(value) = value {
                    self.out.push(' ');
                    self.expr(value);
                }
                self.out.push(';');
            }
            StmtKind::Yield(value) => self.keyword_expr("yield", value),
            StmtKind::Throw(value) => self.keyword_expr("throw", value),
            StmtKind::Break(label) => self.jump("break", *label),
            StmtKind::Continue(label) => self.jump("continue", *label),
            StmtKind::Labeled { label, body } => {
                self.out.push_str(label.as_str());
                self.out.push_str(": ");
                self.stmt(body);
            }
        }
    }

    fn jump(&mut self, keyword: &str, label: Option<Symbol>) {
        match label {
            Some(label) => {
                let _ = write!(self.out, "{keyword} {label};");
            }
            None => {
                let _ = write!(self.out, "{keyword};");
            }
        }
    }

    fn keyword_expr(&mut self, keyword: &str, value: &Expr) {
        let _ = write!(self.out, "{keyword} ");
        self.expr(value);
        self.out.push(';');
    }

    fn switch(&mut self, scrutinee: &Expr, arms: &[Arm]) {
        self.out.push_str("switch ");
        self.expr(scrutinee);
        self.out.push_str(" {");
        self.depth += 1;
        for arm in arms {
            self.line();
            for (index, pat) in arm.pats.iter().enumerate() {
                if index > 0 {
                    self.out.push_str(" | ");
                }
                self.pat(pat);
            }
            if let Some(guard) = &arm.guard {
                self.out.push_str(" if ");
                self.expr(guard);
            }
            self.out.push_str(" => ");
            match &arm.body {
                ArmBody::Expr(expr) => self.expr(expr),
                ArmBody::Block(block) => self.block(block),
                ArmBody::Throw(expr) => {
                    self.out.push_str("throw ");
                    self.expr(expr);
                }
            }
        }
        self.depth -= 1;
        self.line();
        self.out.push('}');
    }

    fn pat(&mut self, pat: &Pat) {
        match &pat.kind {
            PatKind::Wild => self.out.push('_'),
            PatKind::Lit(expr) => self.expr(expr),
            PatKind::Binding { local, ty } => match local {
                Some(local) => {
                    let _ = write!(self.out, "{}: {ty}", self.name(*local));
                }
                None => {
                    let _ = write!(self.out, "_: {ty}");
                }
            },
            PatKind::Variant { def, index, fields } => {
                let sig = self.tcx.sig(*def);
                let _ = write!(
                    self.out,
                    "{}::{}",
                    sig.name.name, sig.variants[*index].name.name
                );
                if !fields.is_empty() {
                    self.out.push('(');
                    for (position, field) in fields.iter().enumerate() {
                        if position > 0 {
                            self.out.push_str(", ");
                        }
                        self.pat(field);
                    }
                    self.out.push(')');
                }
            }
            PatKind::Record { def, fields } => {
                let _ = write!(self.out, "{}(", self.tcx.sig(*def).name.name);
                for (position, field) in fields.iter().enumerate() {
                    if position > 0 {
                        self.out.push_str(", ");
                    }
                    self.pat(field);
                }
                self.out.push(')');
            }
            PatKind::Const { owner, name } => {
                let _ = write!(self.out, "{}::{name}", self.tcx.sig(*owner).name.name);
            }
        }
    }

    fn closure(&mut self, closure: &Closure) {
        let captures: Vec<String> = closure
            .captures
            .iter()
            .map(|capture| {
                let borrow = if capture.mutable { "&mut " } else { "&" };
                format!("{borrow}{}", self.name(capture.local))
            })
            .collect();
        match &closure.kind {
            ClosureKind::Lambda {
                moves,
                params,
                ret,
                body,
            } => {
                let params: Vec<String> = params
                    .iter()
                    .map(|&local| format!("{}: {}", self.name(local), self.body.local(local).ty))
                    .collect();
                let prefix = if *moves { "move " } else { "" };
                let _ = write!(
                    self.out,
                    "{prefix}|{}| -> {ret} [{}] ",
                    params.join(", "),
                    captures.join(", ")
                );
                match body {
                    ClosureBody::Expr(expr) => self.expr(expr),
                    ClosureBody::Block(block) => self.block(block),
                }
            }
            ClosureKind::MethodRef {
                callee,
                bound,
                constructs,
            } => {
                self.out
                    .push_str(if *constructs { "ref new " } else { "ref " });
                match callee {
                    Some(callee) => self.callee(callee),
                    None => self.out.push_str("<default>"),
                }
                if let Some(bound) = bound {
                    self.out.push_str(" on ");
                    self.expr(bound);
                }
            }
        }
    }

    fn exprs(&mut self, exprs: &[Expr]) {
        for (index, expr) in exprs.iter().enumerate() {
            if index > 0 {
                self.out.push_str(", ");
            }
            self.expr(expr);
        }
    }

    fn callee(&mut self, callee: &Callee) {
        let owner = self.tcx.sig(callee.method.owner).name.name;
        let _ = write!(self.out, "{owner}::{}", callee.method.name.name);
    }

    fn expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Lit(lit) => {
                let _ = write!(self.out, "{lit}");
            }
            ExprKind::Bool(value) => {
                let _ = write!(self.out, "{value}");
            }
            ExprKind::Null => self.out.push_str("null"),
            ExprKind::Local(local) => self.out.push_str(&self.name(*local)),
            ExprKind::Field {
                base, name, safe, ..
            } => {
                self.expr(base);
                let _ = write!(self.out, "{}{name}", if *safe { "?." } else { "." });
            }
            ExprKind::Static { owner, name } => {
                let _ = write!(self.out, "{}::{name}", self.tcx.sig(*owner).name.name);
            }
            ExprKind::Call {
                callee,
                receiver,
                args,
                dispatch,
                safe,
            } => {
                if *dispatch == Dispatch::Static && receiver.is_some() {
                    self.out.push_str("static ");
                }
                if *safe {
                    self.out.push_str("safe ");
                }
                self.callee(callee);
                self.out.push('(');
                if let Some(receiver) = receiver {
                    self.expr(receiver);
                    if !args.is_empty() {
                        self.out.push_str(", ");
                    }
                }
                self.exprs(args);
                self.out.push(')');
            }
            ExprKind::New { args, .. } => {
                let _ = write!(self.out, "new {}(", expr.ty);
                self.exprs(args);
                self.out.push(')');
            }
            ExprKind::CtorCall { callee, this, args } => {
                self.callee(callee);
                self.out.push_str("::<init>(");
                self.expr(this);
                if !args.is_empty() {
                    self.out.push_str(", ");
                }
                self.exprs(args);
                self.out.push(')');
            }
            ExprKind::Index { base, index } => {
                self.expr(base);
                self.out.push('[');
                self.expr(index);
                self.out.push(']');
            }
            ExprKind::NewArray { len } => {
                let elem = match &expr.ty {
                    Ty::Array(elem) => elem.to_string(),
                    ty => ty.to_string(),
                };
                let _ = write!(self.out, "new {elem}[");
                self.expr(len);
                self.out.push(']');
            }
            ExprKind::Len { array } => {
                self.out.push_str("len(");
                self.expr(array);
                self.out.push(')');
            }
            ExprKind::Array { elems } => {
                self.out.push('[');
                self.exprs(elems);
                self.out.push(']');
            }
            ExprKind::Unary { op, expr: operand } => {
                let (prefix, suffix) = match op {
                    UnOp::Neg => ("-", ""),
                    UnOp::Not => ("!", ""),
                    UnOp::BitNot => ("~", ""),
                    UnOp::PreInc => ("++", ""),
                    UnOp::PreDec => ("--", ""),
                    UnOp::PostInc => ("", "++"),
                    UnOp::PostDec => ("", "--"),
                };
                self.out.push('(');
                self.out.push_str(prefix);
                self.expr(operand);
                self.out.push_str(suffix);
                self.out.push(')');
            }
            ExprKind::Borrow {
                mutable,
                expr: operand,
            } => {
                self.out.push_str(if *mutable { "&mut " } else { "&" });
                self.expr(operand);
            }
            ExprKind::Binary { op, lhs, rhs } => {
                self.out.push('(');
                self.expr(lhs);
                let _ = write!(self.out, " {} ", op.as_str());
                self.expr(rhs);
                self.out.push(')');
            }
            ExprKind::Assign { op, place, value } => {
                self.expr(place);
                let _ = write!(self.out, " {}= ", op.map_or("", |op| op.as_str()));
                self.expr(value);
            }
            ExprKind::If { cond, then, els } => {
                self.out.push_str("if ");
                self.expr(cond);
                self.out.push_str(" { ");
                self.expr(then);
                self.out.push_str(" } else { ");
                self.expr(els);
                self.out.push_str(" }");
            }
            ExprKind::Is { expr: operand, pat } => {
                self.out.push('(');
                self.expr(operand);
                self.out.push_str(" is ");
                self.pat(pat);
                self.out.push(')');
            }
            ExprKind::Await { expr: operand } => {
                self.out.push_str("(await ");
                self.expr(operand);
                self.out.push(')');
            }
            ExprKind::Cast { expr: operand } => {
                self.out.push('(');
                self.expr(operand);
                let _ = write!(self.out, " as {})", expr.ty);
            }
            ExprKind::Deref {
                expr: operand,
                safe,
            } => {
                self.out.push_str(if *safe { "(?*" } else { "(*" });
                self.expr(operand);
                self.out.push(')');
            }
            ExprKind::Switch { scrutinee, arms } => self.switch(scrutinee, arms),
            ExprKind::With { base, fields, .. } => {
                self.expr(base);
                self.out.push_str(" with { ");
                for (index, field) in fields.iter().enumerate() {
                    if index > 0 {
                        self.out.push_str(", ");
                    }
                    let _ = write!(self.out, "{} = ", field.name);
                    self.expr(&field.value);
                }
                self.out.push_str(" }");
            }
            ExprKind::Equals {
                callee,
                lhs,
                rhs,
                negated,
            } => {
                if *negated {
                    self.out.push('!');
                }
                self.callee(callee);
                self.out.push('(');
                self.expr(lhs);
                self.out.push_str(", ");
                self.expr(rhs);
                self.out.push(')');
            }
            ExprKind::Closure(closure) => self.closure(closure),
            ExprKind::Unresolved => self.out.push_str("<unresolved>"),
        }
    }
}
