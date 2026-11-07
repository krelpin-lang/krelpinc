use std::fmt;

use crate::token::{Lit, LitKind};

use super::{
    CaseLabel, Expr, ExprKind, Ident, LambdaBody, LambdaParam, Pat, PatKind, Path, SwitchExprArm,
    SwitchExprBody, Ty, TyKind, UnOp,
};

impl fmt::Debug for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} @ {:?}", self.name, self.span)
    }
}

impl fmt::Debug for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"{self}\" @ {:?}", self.span)
    }
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let names: Vec<&str> = self.segments.iter().map(|s| s.name.as_str()).collect();
        f.write_str(&names.join("."))
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            TyKind::Primitive(primitive) => f.write_str(primitive.name()),
            TyKind::Path { path, args } => {
                write!(f, "{path}")?;
                if !args.is_empty() {
                    let args: Vec<String> = args.iter().map(Ty::to_string).collect();
                    write!(f, "<{}>", args.join(", "))?;
                }
                Ok(())
            }
            TyKind::Ref { mutable, ty } => {
                f.write_str("&")?;
                if *mutable {
                    f.write_str("mut ")?;
                }
                match ty.kind {
                    TyKind::Nullable(_) => write!(f, "({ty})"),
                    _ => write!(f, "{ty}"),
                }
            }
            TyKind::Nullable(ty) => write!(f, "{ty}?"),
            TyKind::Array(ty) => match ty.kind {
                TyKind::Ref { .. } | TyKind::Nullable(_) => write!(f, "({ty})[]"),
                _ => write!(f, "{ty}[]"),
            },
        }
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            LitKind::Str => write!(f, "\"{}\"", self.symbol)?,
            LitKind::Char => write!(f, "'{}'", self.symbol)?,
            LitKind::TextBlock => write!(f, "\"\"\"{}\"\"\"", self.symbol)?,
            LitKind::Integer | LitKind::Float | LitKind::Err => write!(f, "{}", self.symbol)?,
        }
        if let Some(suffix) = self.suffix {
            write!(f, "{suffix}")?;
        }
        Ok(())
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            ExprKind::Lit(lit) => write!(f, "{lit}"),
            ExprKind::Bool(value) => write!(f, "{value}"),
            ExprKind::Null => f.write_str("null"),
            ExprKind::This => f.write_str("this"),
            ExprKind::Super => f.write_str("super"),
            ExprKind::Name(name) => write!(f, "{}", name.name),
            ExprKind::Field { expr, name, safe } => {
                write!(f, "{expr}{}{}", access(*safe), name.name)
            }
            ExprKind::MethodCall {
                receiver,
                type_args,
                name,
                args,
                safe,
            } => {
                if let Some(receiver) = receiver {
                    write!(f, "{receiver}{}", access(*safe))?;
                }
                if !type_args.is_empty() {
                    write!(f, "<{}>", list(type_args))?;
                }
                write!(f, "{}({})", name.name, list(args))
            }
            ExprKind::Call { callee, args } => write!(f, "{callee}({})", list(args)),
            ExprKind::Index { expr, index } => write!(f, "{expr}[{index}]"),
            ExprKind::New { ty, args } => write!(f, "new {ty}({})", list(args)),
            ExprKind::NewArray { elem, len } => write!(f, "new {elem}[{len}]"),
            ExprKind::ArrayInit { ty, elems } => match ty {
                Some(ty) => write!(f, "new {ty} {{{}}}", list(elems)),
                None => write!(f, "{{{}}}", list(elems)),
            },
            ExprKind::Unary { op, expr } => match op {
                UnOp::Neg => write!(f, "(-{expr})"),
                UnOp::Not => write!(f, "(!{expr})"),
                UnOp::BitNot => write!(f, "(~{expr})"),
                UnOp::PreInc => write!(f, "(++{expr})"),
                UnOp::PreDec => write!(f, "(--{expr})"),
                UnOp::PostInc => write!(f, "({expr}++)"),
                UnOp::PostDec => write!(f, "({expr}--)"),
            },
            ExprKind::Borrow { mutable, expr } => {
                let prefix = if *mutable { "&mut " } else { "&" };
                write!(f, "({prefix}{expr})")
            }
            ExprKind::Binary { op, lhs, rhs } => write!(f, "({lhs} {} {rhs})", op.as_str()),
            ExprKind::Assign { op, lhs, rhs } => {
                let op = op.map_or("", |op| op.as_str());
                write!(f, "({lhs} {op}= {rhs})")
            }
            ExprKind::Ternary { cond, then, els } => write!(f, "({cond} ? {then} : {els})"),
            ExprKind::InstanceOf { expr, pat } => write!(f, "({expr} instanceof {pat})"),
            ExprKind::Cast { ty, expr } => write!(f, "(({ty}) {expr})"),
            ExprKind::Await(expr) => write!(f, "(await {expr})"),
            ExprKind::Lambda {
                moves,
                params,
                body,
            } => {
                let params: Vec<String> = params.iter().map(LambdaParam::to_string).collect();
                let prefix = if *moves { "move " } else { "" };
                match body.as_ref() {
                    LambdaBody::Expr(expr) => {
                        write!(f, "({prefix}({}) -> {expr})", params.join(", "))
                    }
                    LambdaBody::Block(_) => {
                        write!(f, "({prefix}({}) -> {{ ... }})", params.join(", "))
                    }
                }
            }
            ExprKind::MethodRef { expr, name } => write!(f, "{expr}::{}", name.name),
            ExprKind::With { base, fields } => {
                let fields: Vec<String> = fields
                    .iter()
                    .map(|field| format!("{} = {}", field.name.name, field.value))
                    .collect();
                write!(f, "({base} with {{ {} }})", fields.join(", "))
            }
            ExprKind::Switch { scrutinee, arms } => {
                let arms: Vec<String> = arms.iter().map(SwitchExprArm::to_string).collect();
                write!(f, "switch ({scrutinee}) {{ {} }}", arms.join(" "))
            }
        }
    }
}

impl fmt::Display for SwitchExprArm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} -> ", self.label)?;
        match &self.body {
            SwitchExprBody::Expr(expr) => write!(f, "{expr};"),
            SwitchExprBody::Block(_) => f.write_str("{ ... }"),
            SwitchExprBody::Throw(expr) => write!(f, "throw {expr};"),
        }
    }
}

impl fmt::Display for CaseLabel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CaseLabel::Default(_) => f.write_str("default"),
            CaseLabel::Case { pats, guard } => {
                write!(f, "case {}", list(pats))?;
                match guard {
                    Some(guard) => write!(f, " when {guard}"),
                    None => Ok(()),
                }
            }
        }
    }
}

impl fmt::Display for Pat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            PatKind::Wild => f.write_str("_"),
            PatKind::Lit(expr) => write!(f, "{expr}"),
            PatKind::Path(path) => write!(f, "{path}"),
            PatKind::Ty { ty, binding } => match binding {
                Some(binding) => write!(f, "{ty} {}", binding.name),
                None => write!(f, "{ty}"),
            },
            PatKind::Variant { path, fields } => write!(f, "{path}({})", list(fields)),
        }
    }
}

impl fmt::Display for LambdaParam {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.ty {
            Some(ty) => write!(f, "{ty} {}", self.name.name),
            None => write!(f, "{}", self.name.name),
        }
    }
}

fn access(safe: bool) -> &'static str {
    if safe { "?." } else { "." }
}

fn list<T: fmt::Display>(items: &[T]) -> String {
    let parts: Vec<String> = items.iter().map(T::to_string).collect();
    parts.join(", ")
}
