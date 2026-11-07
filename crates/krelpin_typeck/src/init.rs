//! Checks that every field which can't be null gets a value before it can be
//! read. Objects start zeroed, so a forgotten field of a class type would
//! otherwise hold a null that the type says is impossible.

use krelpin_ast::ast::{
    Block, Constructor, ExprKind, FieldStorage, Item, ItemKind, MemberKind, Stmt, StmtKind,
};
use krelpin_errors::Diagnostic;
use krelpin_span::Symbol;
use krelpin_span::def_id::DefId;

use crate::sig::Tcx;
use crate::ty::Ty;

impl Tcx<'_> {
    pub(crate) fn check_field_initialization(&self, def: DefId, item: &Item) {
        let ItemKind::Class(class) = &item.kind else {
            return;
        };
        let ctors: Vec<&Constructor> = class
            .members
            .iter()
            .filter_map(|member| match &member.kind {
                MemberKind::Constructor(ctor) => Some(ctor),
                _ => None,
            })
            .collect();
        for member in &class.members {
            let MemberKind::Field(field) = &member.kind else {
                continue;
            };
            if field.init.is_some() {
                continue;
            }
            let Some(sig) = self.sig(def).fields.get(&field.name.name) else {
                continue;
            };
            let name = field.name;
            if field.final_kw.is_some() && matches!(field.storage, FieldStorage::Instance) {
                if ctors.is_empty() {
                    self.dcx.emit(
                        Diagnostic::error(format!(
                            "`final` field `{}` is never given a value",
                            name.name
                        ))
                        .with_span(name.span)
                        .with_label("a `final` field is assigned exactly once")
                        .with_help("give it an initial value or assign it in a constructor"),
                    );
                }
                continue;
            }
            if !needs_value(&sig.ty) || self.is_primitive_class(&sig.ty) {
                continue;
            }
            if matches!(field.storage, FieldStorage::Static(_)) {
                self.dcx.emit(
                    Diagnostic::error(format!(
                        "static field `{}` is never given a value",
                        name.name
                    ))
                    .with_span(name.span)
                    .with_label(format!("`{}` can't be null", sig.ty))
                    .with_help(format!(
                        "give it an initial value, or declare it as `{}?`",
                        sig.ty
                    )),
                );
                continue;
            }
            if ctors.is_empty() {
                self.dcx.emit(
                    Diagnostic::error(format!("field `{}` is never given a value", name.name))
                        .with_span(name.span)
                        .with_label(format!("`{}` can't be null", sig.ty))
                        .with_help("give it an initial value or assign it in a constructor"),
                );
                continue;
            }
            for ctor in &ctors {
                if delegates(&ctor.body) || assigns_block(&ctor.body, name.name) {
                    continue;
                }
                self.dcx.emit(
                    Diagnostic::error(format!(
                        "this constructor doesn't always give field `{}` a value",
                        name.name
                    ))
                    .with_span(ctor.name.span)
                    .with_secondary(name.span, format!("`{}` can't be null", sig.ty))
                    .with_help(format!(
                        "assign `this.{} = ...` on every path through the constructor",
                        name.name
                    )),
                );
            }
        }
    }
}

impl Tcx<'_> {
    /// `Int` and the other classes behind the primitives, which are reported
    /// as not being types where they are written.
    fn is_primitive_class(&self, ty: &Ty) -> bool {
        matches!(ty, Ty::Adt { def, .. } if self.lang_items.primitive_of(*def).is_some())
    }
}

/// Whether a field of type `ty` holds a pointer that can't be null, as
/// opposed to a number, a nullable value or something already reported.
fn needs_value(ty: &Ty) -> bool {
    !matches!(
        ty,
        Ty::Primitive(_) | Ty::Nullable(_) | Ty::Unknown | Ty::Null
    )
}

/// A constructor that starts with `this(...)` leaves the fields to the one it
/// calls.
pub(crate) fn delegates(body: &Block) -> bool {
    body.stmts.first().is_some_and(|stmt| {
        matches!(&stmt.kind, StmtKind::Expr(expr)
            if matches!(&expr.kind, ExprKind::Call { callee, .. }
                if matches!(callee.kind, ExprKind::This)))
    })
}

/// Whether the statements of `block`, run in order, always assign
/// `this.field` before the constructor can return.
fn assigns_block(block: &Block, field: Symbol) -> bool {
    for stmt in &block.stmts {
        if assigns(stmt, field) {
            return true;
        }
        if may_return(stmt) {
            return false;
        }
    }
    false
}

fn may_return(stmt: &Stmt) -> bool {
    match &stmt.kind {
        StmtKind::Return(_) => true,
        StmtKind::Block(block) => block.stmts.iter().any(may_return),
        StmtKind::If { then, els, .. } => {
            may_return(then) || els.as_deref().is_some_and(may_return)
        }
        StmtKind::Labeled { body, .. }
        | StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::ForEach { body, .. } => may_return(body),
        StmtKind::Switch { arms, .. } => arms.iter().any(|arm| may_return(&arm.body)),
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            body.stmts.iter().any(may_return)
                || catches
                    .iter()
                    .any(|catch| catch.body.stmts.iter().any(may_return))
                || finally
                    .as_ref()
                    .is_some_and(|finally| finally.stmts.iter().any(may_return))
        }
        _ => false,
    }
}

/// Whether running `stmt` to its end always assigns `this.field`.
fn assigns(stmt: &Stmt, field: Symbol) -> bool {
    match &stmt.kind {
        StmtKind::Expr(expr) => match &expr.kind {
            ExprKind::Assign { op: None, lhs, .. } => matches!(&lhs.kind,
                ExprKind::Field { expr, name, .. }
                    if name.name == field && matches!(expr.kind, ExprKind::This)),
            _ => false,
        },
        StmtKind::Block(block) => assigns_block(block, field),
        StmtKind::If {
            then,
            els: Some(els),
            ..
        } => assigns(then, field) && assigns(els, field),
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            finally
                .as_ref()
                .is_some_and(|finally| assigns_block(finally, field))
                || (assigns_block(body, field)
                    && catches
                        .iter()
                        .all(|catch| assigns_block(&catch.body, field)))
        }
        // A constructor that throws on some path never hands out the object.
        StmtKind::Throw(_) => true,
        _ => false,
    }
}
