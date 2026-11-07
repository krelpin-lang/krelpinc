mod accessors;
mod asyncness;
mod call;
mod check;
mod closure;
mod coerce;
mod exceptions;
mod expr;
mod finals;
mod inherit;
mod init;
mod lang_items;
mod param_env;
mod pat;
mod sig;
mod stmt;
pub mod ty;
mod usefulness;
mod wfcheck;

#[cfg(test)]
mod tests;

use std::collections::HashMap;

use krelpin_ast::ast::CompilationUnit;
use krelpin_errors::DiagCtxt;
use krelpin_resolve::ResolverOutput;
use krelpin_span::def_id::DefId;
use krelpin_span::{Span, Symbol};

pub use crate::closure::FnSig;
pub use crate::lang_items::{LangItem, LangItems};
pub use crate::param_env::ParamEnv;
pub use crate::sig::{
    AdtKind, BorrowSource, FieldSig, GenericParamSig, MethodSig, RetBorrows, Storage, Tcx, TypeSig,
    VariantFieldSig, VariantSig,
};
pub use crate::ty::{Subst, Ty};

#[derive(Debug, Default)]
pub struct TypeckResults {
    pub expr_types: HashMap<Span, Ty>,
    pub callees: HashMap<Span, Callee>,
    pub fields: HashMap<Span, FieldSig>,
    pub local_types: HashMap<Span, Ty>,
    pub pats: HashMap<Span, PatRes>,
}

impl TypeckResults {
    fn extend(&mut self, other: TypeckResults) {
        self.expr_types.extend(other.expr_types);
        self.callees.extend(other.callees);
        self.fields.extend(other.fields);
        self.local_types.extend(other.local_types);
        self.pats.extend(other.pats);
    }
}

#[derive(Clone, Debug)]
pub enum PatRes {
    Variant { def: DefId, index: usize },
    Record { def: DefId },
    Type(Ty),
    Const { owner: DefId, name: Symbol, ty: Ty },
}

#[derive(Clone, Debug)]
pub struct Callee {
    pub method: MethodSig,
    pub params: Vec<Ty>,
    pub ret: Ty,
    pub packs_varargs: bool,
    pub subst: Subst,
}

pub struct TypeckOutput<'a> {
    pub tcx: Tcx<'a>,
    pub results: TypeckResults,
}

pub fn check<'a>(
    units: &[CompilationUnit],
    resolved: &'a ResolverOutput,
    dcx: &'a DiagCtxt,
) -> TypeckOutput<'a> {
    let mut tcx = Tcx::new(units, resolved, dcx);
    tcx.break_inheritance_cycles();
    tcx.derive_record_equality();
    tcx.add_record_accessors();
    let results = check::check_units(&tcx, units);
    TypeckOutput { tcx, results }
}
