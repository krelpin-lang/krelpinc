use std::collections::{HashMap, HashSet};

use krelpin_ast::ast::{
    CompilationUnit, ExprKind, FieldStorage, FnRetTy, Ident, ItemKind, Member, MemberKind, Param,
    ReceiverKind, StmtKind,
};
use krelpin_errors::Diagnostic;
use krelpin_span::def_id::DefId;
use krelpin_span::{Span, Symbol};

use crate::TypeckResults;
use crate::exceptions::ExceptionScope;
use crate::param_env::ParamEnv;
use crate::sig::Tcx;
use crate::ty::Ty;

pub(crate) struct FnCtxt<'a, 'tcx> {
    pub(crate) tcx: &'a Tcx<'tcx>,
    pub(crate) owner: DefId,
    pub(crate) self_ty: Ty,
    pub(crate) param_env: ParamEnv,
    pub(crate) ret: Ty,
    pub(crate) locals: HashMap<Span, Ty>,
    pub(crate) narrowed: Vec<HashMap<Span, Ty>>,
    pub(crate) yields: Vec<Vec<Ty>>,
    pub(crate) inferred_returns: Vec<Vec<Ty>>,
    pub(crate) call_expectations: HashMap<Span, Ty>,
    pub(crate) deferrable: std::collections::HashSet<Span>,
    pub(crate) pending_calls: HashMap<Span, crate::call::PendingCall>,
    pub(crate) pending_chains: HashMap<Span, crate::call::PendingChain>,
    pub(crate) exceptions: ExceptionScope,
    pub(crate) results: TypeckResults,
    /// The `this(...)` or `super(...)` call that starts the constructor
    /// being checked, the only place such a call may appear.
    pub(crate) delegation: Option<Span>,
    /// Whether this is the body of an `async` method, where `await` is
    /// allowed. Lambdas inside it aren't.
    pub(crate) in_async: bool,
    pub(crate) in_ctor: bool,
    /// The field an assignment is checking as its target, which reports a
    /// record component as unassignable rather than as private.
    pub(crate) assigning: Option<krelpin_span::Span>,
    pub(crate) explicit_type_args: HashMap<Span, Vec<Ty>>,
}

impl Tcx<'_> {
    pub(crate) fn break_inheritance_cycles(&mut self) {
        for def in (0..self.types.len()).map(DefId::from_index) {
            if !self.reaches(def, def) {
                continue;
            }
            let name = self.sig(def).name;
            self.dcx.emit(
                Diagnostic::error(format!(
                    "cyclic inheritance: `{}` inherits from itself",
                    name.name
                ))
                .with_span(name.span)
                .with_note("a type cannot be its own ancestor"),
            );
            let sig = &mut self.types[def.index()];
            sig.superclass = None;
            sig.interfaces
                .retain(|parent| !matches!(parent, Ty::Adt { .. }));
        }
    }

    fn reaches(&self, from: DefId, target: DefId) -> bool {
        let mut stack = vec![from];
        let mut seen = HashSet::new();
        while let Some(def) = stack.pop() {
            let sig = self.sig(def);
            for parent in sig.superclass.iter().chain(sig.interfaces.iter()) {
                if let Ty::Adt { def: parent, .. } = parent {
                    if *parent == target {
                        return true;
                    }
                    if seen.insert(*parent) {
                        stack.push(*parent);
                    }
                }
            }
        }
        false
    }
}

pub(crate) fn check_units(tcx: &Tcx<'_>, units: &[CompilationUnit]) -> TypeckResults {
    let mut results = TypeckResults::default();

    for (type_def, item) in tcx.items.items(units) {
        let owner = type_def.def;
        tcx.check_item_wf(owner, item);
        tcx.check_inheritance(owner, item);
        tcx.check_field_initialization(owner, item);
        let members: &[Member] = match &item.kind {
            ItemKind::Class(class) => &class.members,
            ItemKind::Record(def) => &def.members,
            ItemKind::Interface(interface) => &interface.members,
            ItemKind::Enum(def) => &def.members,
        };

        for member in members {
            let mut fcx = check_member(tcx, owner, member);
            tcx.check_finals(item, member);
            fcx.report_pending_calls();
            results.extend(fcx.results);
            results.local_types.extend(fcx.locals);
        }
        if let ItemKind::Class(_) = &item.kind
            && !members
                .iter()
                .any(|member| matches!(member.kind, MemberKind::Constructor(_)))
        {
            // A class without constructors still runs its superclass's.
            let mut fcx = FnCtxt::new(tcx, owner, Ty::Void);
            fcx.self_ty = receiver_ty(tcx, owner, ReceiverKind::RefMut);
            fcx.check_implicit_super(item.name, true);
            results.extend(fcx.results);
        }
    }

    results
}

fn check_member<'a, 'tcx>(tcx: &'a Tcx<'tcx>, owner: DefId, member: &Member) -> FnCtxt<'a, 'tcx> {
    match &member.kind {
        MemberKind::Type(_) => FnCtxt::new(tcx, owner, Ty::Void),
        MemberKind::Field(field) => {
            let mut fcx = FnCtxt::new(tcx, owner, Ty::Void);
            if let Some(init) = &field.init {
                let ty = tcx
                    .sig(owner)
                    .fields
                    .get(&field.name.name)
                    .map(|f| f.ty.clone());
                let expected = ty.unwrap_or(Ty::Unknown);
                fcx.self_ty = if matches!(field.storage, FieldStorage::Static(_)) {
                    Ty::Unknown
                } else {
                    receiver_ty(tcx, owner, ReceiverKind::RefMut)
                };
                fcx.check_expr_coerce(init, &expected);
            }
            fcx
        }
        MemberKind::Constructor(ctor) => {
            let mut fcx = FnCtxt::new(tcx, owner, Ty::Void);
            fcx.self_ty = receiver_ty(tcx, owner, ReceiverKind::RefMut);
            fcx.in_ctor = true;
            fcx.exceptions = ExceptionScope::declared(tcx.lower_tys(&ctor.throws));
            fcx.declare_params(&ctor.params);
            fcx.delegation = ctor.body.stmts.first().and_then(|stmt| match &stmt.kind {
                StmtKind::Expr(expr) if matches!(expr.kind, ExprKind::Call { .. }) => {
                    Some(expr.span)
                }
                _ => None,
            });
            if fcx.delegation.is_none() {
                fcx.check_implicit_super(ctor.name, false);
            }
            fcx.check_block(&ctor.body);
            fcx
        }
        MemberKind::Method(method) => {
            let ret = match &method.ret {
                FnRetTy::Void(_) => Ty::Void,
                FnRetTy::Ty(ty) => tcx.lower_ty(ty),
            };
            let mut fcx = FnCtxt::new(tcx, owner, ret.clone());
            fcx.param_env = fcx
                .param_env
                .with_generics(&tcx.generic_params(&method.generics))
                .with_where_bounds(&tcx.where_bounds(&method.where_clause));
            fcx.self_ty = match &method.receiver {
                Some(receiver) => receiver_ty(tcx, owner, receiver.kind),
                None => Ty::Unknown,
            };
            fcx.exceptions = ExceptionScope::declared(tcx.lower_tys(&method.throws));
            fcx.declare_params(&method.params);
            if let Some(span) = method.asyncness {
                fcx.in_async = true;
                fcx.check_async_method(method, span);
            }
            fcx.check_record_accessor(member, method, &ret);
            if let Some(body) = &method.body {
                let diverges = fcx.check_block(body);
                if !diverges {
                    fcx.report_missing_return(body.span, &ret, "method");
                }
            }
            fcx
        }
    }
}

fn receiver_ty(tcx: &Tcx<'_>, owner: DefId, receiver: ReceiverKind) -> Ty {
    let self_ty = tcx.self_ty(owner);
    match receiver {
        ReceiverKind::Owned => self_ty,
        ReceiverKind::Ref | ReceiverKind::RefMut => Ty::Ref {
            mutable: receiver == ReceiverKind::RefMut,
            ty: Box::new(self_ty),
        },
    }
}

impl Tcx<'_> {
    /// The nearest superclass of `owner` that declares constructors, at the
    /// type arguments `owner` inherits it with.
    pub(crate) fn constructing_ancestor(&self, owner: DefId) -> Option<Ty> {
        let mut current = self.sig(owner).superclass.clone()?;
        loop {
            let Ty::Adt { def, args, .. } = &current else {
                return None;
            };
            // Extending anything but a class is reported on its own.
            if self.sig(*def).kind != crate::sig::AdtKind::Class {
                return None;
            }
            if !self.sig(*def).ctors.is_empty() {
                return Some(current);
            }
            let next = self.sig(*def).superclass.clone()?;
            current = next.subst(&self.subst_for(*def, args));
        }
    }
}

impl<'a, 'tcx> FnCtxt<'a, 'tcx> {
    /// Resolves the `super()` that runs before a constructor which doesn't
    /// start with `this(...)` or `super(...)`, or for a class that has no
    /// constructor at all. The call is recorded at `at`.
    pub(crate) fn check_implicit_super(&mut self, at: Ident, no_constructor: bool) {
        let Some(Ty::Adt { def, args, .. }) = self.tcx.constructing_ancestor(self.owner) else {
            return;
        };
        let takes_nothing = self
            .tcx
            .sig(def)
            .ctors
            .iter()
            .any(|ctor| ctor.params.is_empty() || (ctor.variadic && ctor.params.len() == 1));
        if !takes_nothing {
            let parent = self.type_name(def);
            let class = self.type_name(self.owner);
            let help = if no_constructor {
                format!("add a constructor to `{class}` that starts with `super(...)`")
            } else {
                "start the constructor with `super(...)`".to_owned()
            };
            self.emit(
                Diagnostic::error(format!(
                    "`{class}` must call a constructor of `{parent}` first"
                ))
                .with_span(at.span)
                .with_note(format!("every constructor of `{parent}` takes arguments"))
                .with_help(help),
            );
            return;
        }
        let name = Ident::new(self.type_name(def), at.span);
        self.check_ctor_call(def, &args, &[], &[], name);
    }

    pub(crate) fn new(tcx: &'a Tcx<'tcx>, owner: DefId, ret: Ty) -> Self {
        FnCtxt {
            tcx,
            owner,
            self_ty: tcx.self_ty(owner),
            param_env: ParamEnv::default().with_generics(&tcx.sig(owner).generics),
            ret,
            locals: HashMap::new(),
            narrowed: Vec::new(),
            yields: Vec::new(),
            inferred_returns: Vec::new(),
            call_expectations: HashMap::new(),
            deferrable: std::collections::HashSet::new(),
            pending_calls: HashMap::new(),
            pending_chains: HashMap::new(),
            exceptions: ExceptionScope::default(),
            results: TypeckResults::default(),
            delegation: None,
            in_async: false,
            in_ctor: false,
            assigning: None,
            explicit_type_args: HashMap::new(),
        }
    }

    fn declare_params(&mut self, params: &[Param]) {
        for param in params {
            let ty = self.tcx.lower_ty(&param.ty);
            let ty = if param.variadic {
                Ty::Array(Box::new(ty))
            } else {
                ty
            };
            self.locals.insert(param.name.span, ty);
        }
    }

    pub(crate) fn report_missing_return(&self, body: Span, ret: &Ty, what: &str) {
        if matches!(ret, Ty::Void | Ty::Unknown) {
            return;
        }
        let end = body.hi;
        self.emit(
            Diagnostic::error("missing return statement")
                .with_span(Span::new(end - 1, end))
                .with_label(format!("this {what} must return a `{ret}`"))
                .with_help("add a `return` statement, or `throw` an exception"),
        );
    }

    pub(crate) fn lower_ty(&self, ty: &krelpin_ast::ast::Ty) -> Ty {
        self.tcx.check_wf(&self.param_env, ty);
        self.tcx.lower_ty(ty)
    }

    pub(crate) fn is_assignable(&self, from: &Ty, to: &Ty) -> bool {
        self.tcx.is_assignable(&self.param_env, from, to)
    }

    pub(crate) fn local_ty(&self, decl: Span) -> Ty {
        self.narrowed
            .iter()
            .rev()
            .find_map(|scope| scope.get(&decl))
            .or_else(|| self.locals.get(&decl))
            .cloned()
            .unwrap_or(Ty::Unknown)
    }

    pub(crate) fn type_name(&self, def: DefId) -> Symbol {
        match self.tcx.lang_items.primitive_of(def) {
            Some(primitive) => Symbol::intern(primitive.name()),
            None => self.tcx.sig(def).name.name,
        }
    }

    pub(crate) fn emit(&self, diagnostic: Diagnostic) {
        self.tcx.dcx.emit(diagnostic);
    }

    pub(crate) fn error(&self, span: Span, message: impl Into<String>) {
        self.emit(Diagnostic::error(message).with_span(span));
    }

    pub(crate) fn mismatch(&self, span: Span, expected: &Ty, found: &Ty) {
        let diagnostic = Diagnostic::error("mismatched types")
            .with_span(span)
            .with_label(format!("expected `{expected}`, found `{found}`"));

        let diagnostic = match (expected, found) {
            (_, Ty::Null) => diagnostic.with_help(format!(
                "`{expected}` can never be `null`; use `{expected}?` to allow it"
            )),
            (expected, Ty::Nullable(inner)) if self.is_assignable(inner, expected) => diagnostic
                .with_help(
                    "this value may be `null`; use `?:` to give a default, \
                     or check `!= null` first",
                ),
            (Ty::Ref { ty, .. }, found) if self.is_assignable(found, ty) => {
                diagnostic.with_help("borrow the value with `&`")
            }
            _ => diagnostic,
        };
        let diagnostic = diagnostic.with_notes(self.tcx.unmet_conditions(found, expected));
        self.emit(diagnostic);
    }
}

pub(crate) fn plural(count: usize, word: &str) -> String {
    if count == 1 {
        format!("1 {word}")
    } else {
        format!("{count} {word}s")
    }
}
