use krelpin_ast::ast::{Expr, ExprKind, Ident, LambdaBody};
use krelpin_errors::Diagnostic;
use krelpin_span::{Span, Symbol};

use crate::Callee;
use crate::check::{FnCtxt, plural};
use crate::closure::is_closure;
use crate::sig::MethodSig;
use crate::ty::{Subst, Ty};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    Fixed,
    Variadic,
}

impl Phase {
    const ALL: [Phase; 2] = [Phase::Fixed, Phase::Variadic];
}

pub(crate) struct PendingChain {
    pub(crate) base: Expr,
    pub(crate) receiver: Ty,
    pub(crate) name: Ident,
    pub(crate) args: Vec<Expr>,
    pub(crate) safe: bool,
}

pub(crate) struct PendingCall {
    candidate: Candidate,
    probed: Vec<usize>,
    phase: Phase,
    name: Ident,
    what: String,
}

#[derive(Clone)]
struct Candidate {
    method: MethodSig,
    subst: Subst,
    params: Vec<Ty>,
    ret: Ty,
}

impl Candidate {
    fn accepts_arity(&self, args: usize, phase: Phase) -> bool {
        match phase {
            Phase::Fixed => args == self.params.len(),
            Phase::Variadic => self.method.variadic && args + 1 >= self.params.len(),
        }
    }

    fn param(&self, index: usize, phase: Phase) -> Ty {
        let last = self.params.len().saturating_sub(1);
        match (self.params.last(), phase) {
            (Some(Ty::Array(elem)), Phase::Variadic) if index >= last => elem.as_ref().clone(),
            _ => self.params.get(index).cloned().unwrap_or(Ty::Unknown),
        }
    }
}

impl FnCtxt<'_, '_> {
    pub(crate) fn accepts(&self, expr: &Expr, actual: &Ty, expected: &Ty) -> bool {
        match self.closure_fits(expr, expected) {
            Some(fits) => fits,
            None => self.is_assignable(actual, expected),
        }
    }

    fn accepts_exact(&self, expr: &Expr, actual: &Ty, expected: &Ty) -> bool {
        match self.closure_fits(expr, expected) {
            Some(fits) => fits,
            None => self
                .tcx
                .is_assignable_exact(&self.param_env, actual, expected),
        }
    }

    pub(crate) fn call(
        &mut self,
        candidates: Vec<(MethodSig, Subst)>,
        args: &[Expr],
        arg_tys: &[Ty],
        name: Ident,
        what: &str,
    ) -> Ty {
        let ty = self.call_inner(candidates, args, arg_tys, name, what);
        for arg in args {
            self.finish_pending(arg, &Ty::Unknown);
        }
        ty
    }

    pub(crate) fn report_pending_calls(&mut self) {
        let chains: Vec<Span> = self.pending_chains.keys().copied().collect();
        for span in chains {
            if let Some(chain) = self.pending_chains.remove(&span) {
                let expr = Expr {
                    kind: ExprKind::MethodCall {
                        receiver: Some(Box::new(chain.base.clone())),
                        type_args: Vec::new(),
                        name: chain.name,
                        args: chain.args.clone(),
                        safe: chain.safe,
                    },
                    span: chain.name.span,
                };
                self.finish_chain(&expr, chain, &Ty::Unknown);
            }
        }
        let pending: Vec<PendingCall> = self.pending_calls.drain().map(|(_, call)| call).collect();
        for call in pending {
            self.report_unresolved(&call.candidate, call.name);
        }
    }

    pub(crate) fn is_pending(&self, expr: &Expr) -> bool {
        let ExprKind::MethodCall { name, .. } = &expr.kind else {
            return false;
        };
        self.pending_calls.contains_key(&name.span) || self.pending_chains.contains_key(&name.span)
    }

    pub(crate) fn receiver_expectation(
        &self,
        receiver: &Ty,
        name: Ident,
        arg_count: usize,
        expected: &Ty,
    ) -> Option<Ty> {
        if expected.references_unknown() {
            return None;
        }
        let Ty::Adt { def, .. } = receiver.non_null().strip_refs() else {
            return None;
        };
        let vars: Vec<Symbol> = self
            .tcx
            .sig(*def)
            .generics
            .iter()
            .map(|param| param.name)
            .collect();
        if vars.is_empty() {
            return None;
        }
        let own: Vec<Ty> = vars.iter().map(|var| Ty::Param(*var)).collect();
        self.tcx
            .methods_named(*def, &own, name.name)
            .iter()
            .filter(|(method, _)| {
                method.receiver.is_some()
                    && method.params.len() == arg_count
                    && method
                        .generics
                        .iter()
                        .all(|param| !vars.contains(&param.name))
            })
            .find_map(|(method, subst)| {
                let mut inferred = Subst::new();
                self.infer(&method.ret.subst(subst), expected, &vars, &mut inferred);
                let args: Option<Vec<Ty>> =
                    vars.iter().map(|var| inferred.get(var).cloned()).collect();
                Some(self.tcx.def_ty(*def, args?))
            })
    }

    pub(crate) fn chain_placeholder(&self, receiver: &Ty, name: Ident, arg_count: usize) -> Ty {
        let Ty::Adt { def, args, .. } = receiver.non_null().strip_refs() else {
            return Ty::Unknown;
        };
        self.tcx
            .methods_named(*def, args, name.name)
            .iter()
            .find(|(method, _)| method.receiver.is_some() && method.params.len() == arg_count)
            .map_or(Ty::Unknown, |(method, subst)| {
                let mut erased = subst.clone();
                for param in &method.generics {
                    erased.insert(param.name, Ty::Unknown);
                }
                method.ret.subst(&erased)
            })
    }

    pub(crate) fn finish_pending(&mut self, arg: &Expr, expected: &Ty) {
        let ExprKind::MethodCall { name, args, .. } = &arg.kind else {
            return;
        };
        if let Some(chain) = self.pending_chains.remove(&name.span) {
            self.finish_chain(arg, chain, expected);
            return;
        }
        let Some(pending) = self.pending_calls.remove(&name.span) else {
            return;
        };
        let mut candidate = pending.candidate;
        self.infer_from_expectation(&mut candidate, Some(expected));
        let (mut resolved, mut probed) =
            self.infer_from_lambdas(&candidate, args, pending.phase, &pending.probed);
        probed.extend(pending.probed);
        self.infer_from_expectation(&mut resolved, Some(expected));
        self.report_unresolved(&resolved, pending.name);
        let ty = self.finish_call(
            &resolved,
            args,
            &probed,
            pending.phase,
            pending.name,
            &pending.what,
        );
        self.results.expr_types.insert(arg.span, ty);
    }

    fn report_unresolved(&self, resolved: &Candidate, name: Ident) {
        let unresolved: Vec<String> = resolved
            .method
            .generics
            .iter()
            .filter(|param| resolved.subst.get(&param.name).is_none_or(Ty::is_unknown))
            .map(|param| format!("`{}`", param.name))
            .collect();
        if unresolved.is_empty() {
            return;
        }
        self.emit(
            Diagnostic::error(format!(
                "cannot infer {} of `{}`",
                if unresolved.len() == 1 {
                    format!("the type argument {}", unresolved[0])
                } else {
                    format!("the type arguments {}", unresolved.join(", "))
                },
                name.name
            ))
            .with_span(name.span)
            .with_help("give the result a declared type, like `List<String> items = ...`"),
        );
    }

    fn call_inner(
        &mut self,
        candidates: Vec<(MethodSig, Subst)>,
        args: &[Expr],
        arg_tys: &[Ty],
        name: Ident,
        what: &str,
    ) -> Ty {
        let explicit = self.explicit_type_args.get(&name.span).cloned();
        let candidates: Vec<Candidate> = match &explicit {
            Some(explicit) => {
                let fitting: Vec<(MethodSig, Subst)> = candidates
                    .iter()
                    .filter(|(method, _)| method.generics.len() == explicit.len())
                    .cloned()
                    .collect();
                if fitting.is_empty() {
                    let counts: Vec<usize> = candidates
                        .iter()
                        .map(|(method, _)| method.generics.len())
                        .collect();
                    self.report_type_arg_count(name, explicit.len(), &counts);
                    return Ty::Unknown;
                }
                fitting
                    .into_iter()
                    .map(|(method, subst)| self.instantiate_with(method, subst, explicit))
                    .collect()
            }
            None => candidates
                .into_iter()
                .map(|(method, subst)| self.instantiate(method, subst, arg_tys))
                .collect(),
        };
        let arity_ok: Vec<&Candidate> = candidates
            .iter()
            .filter(|candidate| {
                Phase::ALL
                    .iter()
                    .any(|&phase| candidate.accepts_arity(args.len(), phase))
            })
            .collect();
        if arity_ok.is_empty() {
            self.report_arity(&candidates, args.len(), name, what);
            return Ty::Unknown;
        }

        let attempts = Phase::ALL
            .iter()
            .flat_map(|&phase| [(phase, false), (phase, true)]);
        let applicable = attempts.into_iter().find_map(|(phase, copying)| {
            let applicable: Vec<&Candidate> = arity_ok
                .iter()
                .copied()
                .filter(|candidate| self.is_applicable(candidate, args, arg_tys, phase, copying))
                .collect();
            (!applicable.is_empty()).then_some((phase, applicable))
        });
        let Some((phase, applicable)) = applicable else {
            if let [candidate] = arity_ok.as_slice() {
                self.report_arg_mismatches(candidate, args, arg_tys);
                return candidate.ret.clone();
            }
            let found: Vec<String> = arg_tys.iter().map(Ty::to_string).collect();
            self.error(
                name.span,
                format!(
                    "no overload of `{}` accepts arguments of type ({})",
                    name.name,
                    found.join(", ")
                ),
            );
            return Ty::Unknown;
        };

        let Some(chosen) = self.most_specific(&applicable, args.len(), phase) else {
            let unknown_arg = args.iter().zip(arg_tys).any(|(arg, ty)| {
                !is_closure(arg) && !self.is_diamond(arg) && ty.references_unknown()
            });
            if !unknown_arg {
                self.report_ambiguity(&applicable, name);
            }
            return Ty::Unknown;
        };
        let expected = self.call_expectations.remove(&name.span);
        let mut expecting = chosen.clone();
        self.infer_from_expectation(&mut expecting, expected.as_ref());
        let (mut resolved, probed) = self.infer_from_lambdas(&expecting, args, phase, &[]);
        self.infer_from_expectation(&mut resolved, expected.as_ref());
        let unknown_arg = arg_tys
            .iter()
            .zip(args)
            .any(|(ty, arg)| !is_closure(arg) && !self.is_diamond(arg) && ty.references_unknown());
        let unresolved = resolved
            .method
            .generics
            .iter()
            .any(|param| resolved.subst.get(&param.name).is_none_or(Ty::is_unknown));
        if unresolved && self.deferrable.remove(&name.span) {
            let ret = resolved.ret.clone();
            self.pending_calls.insert(
                name.span,
                PendingCall {
                    candidate: resolved,
                    probed,
                    phase,
                    name,
                    what: what.to_owned(),
                },
            );
            return ret;
        }
        for (index, arg) in args.iter().enumerate() {
            let param = resolved.param(index, phase);
            self.finish_pending(arg, &param);
        }
        if !unknown_arg {
            self.report_unresolved(&resolved, name);
        }
        self.finish_call(&resolved, args, &probed, phase, name, what)
    }

    fn finish_call(
        &mut self,
        chosen: &Candidate,
        args: &[Expr],
        probed: &[usize],
        phase: Phase,
        name: Ident,
        what: &str,
    ) -> Ty {
        self.check_call_bounds(chosen, name);
        self.check_vis(chosen.method.vis, chosen.method.owner, false, what, name);
        self.results.callees.insert(
            name.span,
            Callee {
                method: chosen.method.clone(),
                params: chosen.params.clone(),
                ret: chosen.ret.clone(),
                packs_varargs: phase == Phase::Variadic,
                subst: chosen.subst.clone(),
            },
        );
        if chosen.method.output.is_none() {
            for thrown in &chosen.method.throws {
                self.raise(thrown.subst(&chosen.subst), name.span);
            }
        }
        for (index, arg) in args.iter().enumerate() {
            if is_closure(arg) && !probed.contains(&index) {
                self.check_closure(arg, &chosen.param(index, phase));
            } else if self.is_diamond(arg) {
                self.check_expr_coerce(arg, &chosen.param(index, phase));
            }
        }
        chosen.ret.clone()
    }

    fn infer_from_expectation(&self, candidate: &mut Candidate, expected: Option<&Ty>) {
        let Some(expected) = expected.filter(|ty| !ty.references_unknown()) else {
            return;
        };
        let vars: Vec<Symbol> = candidate
            .method
            .generics
            .iter()
            .map(|param| param.name)
            .filter(|name| candidate.subst.get(name).is_none_or(Ty::is_unknown))
            .collect();
        if vars.is_empty() {
            return;
        }
        let mut partial = candidate.subst.clone();
        for var in &vars {
            partial.insert(*var, Ty::Param(*var));
        }
        let mut inferred = Subst::new();
        self.infer(
            &candidate.method.ret.subst(&partial),
            expected,
            &vars,
            &mut inferred,
        );
        if inferred.is_empty() {
            return;
        }
        candidate.subst.extend(inferred);
        candidate.params = candidate
            .method
            .params
            .iter()
            .map(|param| param.subst(&candidate.subst))
            .collect();
        candidate.ret = candidate.method.ret.subst(&candidate.subst);
    }

    fn infer_from_lambdas(
        &mut self,
        chosen: &Candidate,
        args: &[Expr],
        phase: Phase,
        skip: &[usize],
    ) -> (Candidate, Vec<usize>) {
        let mut candidate = chosen.clone();
        let mut probed = Vec::new();
        let unresolved = |candidate: &Candidate| -> Vec<Symbol> {
            candidate
                .method
                .generics
                .iter()
                .map(|param| param.name)
                .filter(|name| candidate.subst.get(name).is_none_or(Ty::is_unknown))
                .collect()
        };
        for (index, arg) in args.iter().enumerate() {
            let vars = unresolved(&candidate);
            if vars.is_empty() {
                break;
            }
            if skip.contains(&index) {
                continue;
            }
            let ExprKind::Lambda { params, body, .. } = &arg.kind else {
                continue;
            };
            let mut partial = candidate.subst.clone();
            for var in &vars {
                partial.insert(*var, Ty::Param(*var));
            }
            let Some(raw) = param_for_inference(&candidate.method, index, args.len(), &Ty::Unknown)
            else {
                continue;
            };
            let expected = raw.subst(&partial);
            let Some(sig) = self.tcx.fn_sig(&expected) else {
                continue;
            };
            let mentions = |ty: &Ty| vars.iter().any(|var| ty.mentions_param(*var));
            if !mentions(&sig.ret) || sig.params.iter().any(mentions) {
                continue;
            }
            let Some(body_ty) = self.probe_lambda(params, body, &sig) else {
                continue;
            };
            probed.push(index);
            let mut inferred = Subst::new();
            self.infer(&sig.ret, &body_ty, &vars, &mut inferred);
            candidate.subst.extend(inferred);
            candidate.params = candidate
                .method
                .params
                .iter()
                .map(|param| param.subst(&candidate.subst))
                .collect();
            candidate.ret = candidate.method.ret.subst(&candidate.subst);
            let final_ty = candidate.param(index, phase);
            if let Some(final_sig) = self.tcx.fn_sig(&final_ty)
                && final_sig.ret != Ty::Void
                && let LambdaBody::Expr(body) = body.as_ref()
            {
                self.require_assignable(body, &body_ty, &final_sig.ret);
            }
            self.results.expr_types.insert(arg.span, final_ty);
        }
        (candidate, probed)
    }

    fn instantiate_with(&self, method: MethodSig, mut subst: Subst, explicit: &[Ty]) -> Candidate {
        for (param, ty) in method.generics.iter().zip(explicit) {
            subst.insert(param.name, ty.clone());
        }
        Candidate {
            params: method
                .params
                .iter()
                .map(|param| param.subst(&subst))
                .collect(),
            ret: method.ret.subst(&subst),
            method,
            subst,
        }
    }

    fn report_type_arg_count(&self, name: Ident, given: usize, counts: &[usize]) {
        let mut counts = counts.to_vec();
        counts.sort_unstable();
        counts.dedup();
        let expected: Vec<String> = counts.iter().map(usize::to_string).collect();
        let diagnostic = Diagnostic::error(format!(
            "`{}` takes {} type argument{}, but {given} {} given",
            name.name,
            expected.join(" or "),
            if counts == [1] { "" } else { "s" },
            if given == 1 { "was" } else { "were" }
        ))
        .with_span(name.span);
        self.emit(if counts == [0] {
            diagnostic
                .with_note(format!("`{}` is not generic", name.name))
                .with_help("remove the type arguments")
        } else {
            diagnostic
        });
    }

    fn instantiate(&self, method: MethodSig, mut subst: Subst, arg_tys: &[Ty]) -> Candidate {
        if !method.generics.is_empty() {
            let vars: Vec<Symbol> = method.generics.iter().map(|param| param.name).collect();
            for var in &vars {
                subst.remove(var);
            }
            let mut inferred = Subst::new();
            for (index, arg) in arg_tys.iter().enumerate() {
                if let Some(param) = param_for_inference(&method, index, arg_tys.len(), arg) {
                    self.infer(&param.subst(&subst), arg, &vars, &mut inferred);
                }
            }
            for var in vars {
                let ty = inferred.remove(&var).unwrap_or(Ty::Unknown);
                subst.insert(var, ty);
            }
        }

        Candidate {
            params: method
                .params
                .iter()
                .map(|param| param.subst(&subst))
                .collect(),
            ret: method.ret.subst(&subst),
            method,
            subst,
        }
    }

    fn infer(&self, param: &Ty, arg: &Ty, vars: &[Symbol], inferred: &mut Subst) {
        match (param, arg) {
            (_, Ty::Unknown | Ty::Null) => {}
            (Ty::Param(name), _) if vars.contains(name) => {
                let merged = match inferred.get(name) {
                    None => Some(arg.clone()),
                    Some(previous) => self.tcx.common_ty(&self.param_env, previous, arg),
                };
                if let Some(merged) = merged {
                    inferred.insert(*name, merged);
                }
            }
            (Ty::Nullable(param), Ty::Nullable(arg))
            | (Ty::Ref { ty: param, .. }, Ty::Ref { ty: arg, .. })
            | (Ty::Array(param), Ty::Array(arg)) => self.infer(param, arg, vars, inferred),
            (Ty::Nullable(param), arg) => self.infer(param, arg, vars, inferred),
            (
                Ty::Adt {
                    def, args: params, ..
                },
                Ty::Adt {
                    def: arg_def,
                    args: arg_args,
                    ..
                },
            ) => {
                if let Some(args) = self.tcx.upcast(*arg_def, arg_args, *def) {
                    for (param, arg) in params.iter().zip(&args) {
                        self.infer(param, arg, vars, inferred);
                    }
                }
            }
            _ => {}
        }
    }

    fn is_applicable(
        &self,
        candidate: &Candidate,
        args: &[Expr],
        arg_tys: &[Ty],
        phase: Phase,
        copying: bool,
    ) -> bool {
        candidate.accepts_arity(args.len(), phase)
            && args
                .iter()
                .zip(arg_tys)
                .enumerate()
                .all(|(index, (arg, ty))| {
                    let expected = candidate.param(index, phase);
                    if copying {
                        self.accepts(arg, ty, &expected)
                    } else {
                        self.accepts_exact(arg, ty, &expected)
                    }
                })
    }

    fn most_specific<'c>(
        &self,
        applicable: &[&'c Candidate],
        arg_count: usize,
        phase: Phase,
    ) -> Option<&'c Candidate> {
        let more_specific = |a: &Candidate, b: &Candidate| {
            (0..arg_count).all(|index| {
                self.tcx.is_assignable(
                    &self.param_env,
                    &a.param(index, phase),
                    &b.param(index, phase),
                )
            })
        };
        applicable
            .iter()
            .copied()
            .find(|a| applicable.iter().all(|b| more_specific(a, b)))
    }

    fn check_call_bounds(&self, candidate: &Candidate, name: Ident) {
        let method = &candidate.method;
        for param in method.generics.iter().chain(&method.where_bounds) {
            match candidate.subst.get(&param.name) {
                Some(Ty::Unknown) | None => {}
                Some(arg) => {
                    self.tcx
                        .check_bound(&self.param_env, param, arg, &candidate.subst, name.span)
                }
            }
        }
    }

    fn report_arity(&self, candidates: &[Candidate], arg_count: usize, name: Ident, what: &str) {
        let message = match candidates {
            [candidate] => format!(
                "this {what} takes {} but {} {} supplied",
                plural_args(candidate.params.len(), candidate.method.variadic),
                plural(arg_count, "argument"),
                if arg_count == 1 { "was" } else { "were" },
            ),
            _ => format!(
                "no overload of `{}` takes {}",
                name.name,
                plural(arg_count, "argument")
            ),
        };
        self.error(name.span, message);
    }

    fn report_arg_mismatches(&mut self, candidate: &Candidate, args: &[Expr], arg_tys: &[Ty]) {
        for (index, (arg, ty)) in args.iter().zip(arg_tys).enumerate() {
            let phases: &[Phase] = if candidate.accepts_arity(args.len(), Phase::Fixed) {
                &[Phase::Fixed, Phase::Variadic]
            } else {
                &[Phase::Variadic]
            };
            let expected: Vec<Ty> = phases
                .iter()
                .filter(|&&phase| candidate.accepts_arity(args.len(), phase))
                .map(|&phase| candidate.param(index, phase))
                .collect();
            let fits = expected
                .iter()
                .any(|expected| self.accepts(arg, ty, expected));
            match (fits, expected.last()) {
                (false, Some(expected)) if is_closure(arg) => {
                    self.check_closure(arg, expected);
                }
                (false, Some(expected)) => self.mismatch(arg.span, expected, ty),
                _ => {}
            }
        }
    }

    fn report_ambiguity(&self, applicable: &[&Candidate], name: Ident) {
        let signatures: Vec<String> = applicable
            .iter()
            .map(|candidate| {
                let params: Vec<String> = candidate.params.iter().map(Ty::to_string).collect();
                format!(
                    "`{}.{}({})`",
                    self.type_name(candidate.method.owner),
                    name.name,
                    params.join(", ")
                )
            })
            .collect();
        self.emit(
            Diagnostic::error(format!("call to `{}` is ambiguous", name.name))
                .with_span(name.span)
                .with_note(format!("it could call {}", signatures.join(" or ")))
                .with_help("cast the arguments to the types of the method you want to call"),
        );
    }
}

fn param_for_inference(method: &MethodSig, index: usize, arg_count: usize, arg: &Ty) -> Option<Ty> {
    let last = method.params.len().checked_sub(1)?;
    match &method.params[last] {
        Ty::Array(elem) if method.variadic && index >= last => {
            let passes_array = index == last && arg_count == method.params.len();
            if passes_array && matches!(arg, Ty::Array(_)) {
                Some(method.params[last].clone())
            } else {
                Some(elem.as_ref().clone())
            }
        }
        _ => method.params.get(index).cloned(),
    }
}

fn plural_args(count: usize, variadic: bool) -> String {
    if variadic {
        format!("at least {}", plural(count.saturating_sub(1), "argument"))
    } else {
        plural(count, "argument")
    }
}

impl FnCtxt<'_, '_> {
    pub(crate) fn infer_diamond(
        &mut self,
        ty: Ty,
        arg_tys: &[Ty],
        span: Span,
        expected: Option<&Ty>,
    ) -> Ty {
        let Ty::Adt { def, name, args } = &ty else {
            return ty;
        };
        let sig = self.tcx.sig(*def);
        if !args.is_empty() || sig.generics.is_empty() {
            return ty;
        }
        let vars: Vec<Symbol> = sig.generics.iter().map(|param| param.name).collect();
        let own: Vec<Ty> = vars.iter().map(|var| Ty::Param(*var)).collect();
        let mut inferred = Subst::new();
        if let Some(Ty::Adt {
            def: expected_def,
            args: expected_args,
            ..
        }) = expected.map(|expected| expected.non_null().strip_refs())
            && let Some(upcast) = self.tcx.upcast(*def, &own, *expected_def)
        {
            for (pattern, actual) in upcast.iter().zip(expected_args) {
                self.infer(pattern, actual, &vars, &mut inferred);
            }
        }
        if vars.iter().any(|var| !inferred.contains_key(var)) {
            let ctors: Vec<MethodSig> = sig
                .ctors
                .iter()
                .filter(|ctor| ctor.params.len() == arg_tys.len())
                .cloned()
                .collect();
            for ctor in ctors {
                let mut from_args = inferred.clone();
                for (param, arg) in ctor.params.iter().zip(arg_tys) {
                    self.infer(param, arg, &vars, &mut from_args);
                }
                if vars.iter().all(|var| from_args.contains_key(var)) {
                    inferred = from_args;
                    break;
                }
            }
        }
        let missing: Vec<String> = vars
            .iter()
            .filter(|var| !inferred.contains_key(var))
            .map(|var| format!("`{var}`"))
            .collect();
        if !missing.is_empty() {
            self.emit(
                Diagnostic::error(format!("cannot infer the type arguments of `{name}<>`"))
                    .with_span(span)
                    .with_note(format!("nothing here decides {}", missing.join(", ")))
                    .with_help(format!(
                        "write them explicitly, like `new {name}<{}>()`",
                        vec!["..."; vars.len()].join(", ")
                    )),
            );
            return Ty::Unknown;
        }
        Ty::Adt {
            def: *def,
            name: *name,
            args: vars
                .iter()
                .map(|var| inferred.remove(var).unwrap_or(Ty::Unknown))
                .collect(),
        }
    }
}
