use krelpin_ast::ast::{CaseLabel, Expr, ExprKind, FieldStorage, Ident, Pat, PatKind, Path, UnOp};
use krelpin_errors::Diagnostic;
use krelpin_span::Span;
use krelpin_span::def_id::DefId;

use crate::PatRes;
use crate::check::FnCtxt;
use crate::sig::AdtKind;
use crate::ty::Ty;
use crate::usefulness::{Ctor, DeconPat, MatchArm, MatchCheck, Witness};

struct VariantRef {
    def: DefId,
    args: Vec<Ty>,
    index: usize,
}

enum PatPath {
    Variant(VariantRef),
    Type(Ty),
    Const(DefId, Ident, Ty),
    Error,
}

pub(crate) enum Coverage<'a> {
    Required(&'a str),
    Optional,
}

impl FnCtxt<'_, '_> {
    pub(crate) fn check_case_label(&mut self, label: &CaseLabel, scrutinee: &Ty) -> Vec<MatchArm> {
        match label {
            CaseLabel::Default(span) => vec![MatchArm {
                pat: DeconPat::wildcard(),
                span: *span,
                has_guard: false,
                has_errors: false,
            }],
            CaseLabel::Case { pats, guard } => {
                let arms = pats
                    .iter()
                    .map(|pat| {
                        let errors = self.tcx.dcx.error_count();
                        let checked = self.check_pat(pat, scrutinee);
                        MatchArm {
                            pat: checked,
                            span: pat.span,
                            has_guard: guard.is_some(),
                            has_errors: self.tcx.dcx.error_count() > errors,
                        }
                    })
                    .collect();
                if let Some(guard) = guard {
                    self.check_expr_coerce(guard, &Ty::BOOLEAN);
                }
                arms
            }
        }
    }

    pub(crate) fn check_match(
        &self,
        scrutinee: &Ty,
        arms: &[MatchArm],
        coverage: Coverage<'_>,
        span: Span,
    ) -> bool {
        if scrutinee.references_unknown() || arms.iter().any(|arm| arm.has_errors) {
            return true;
        }
        let report = MatchCheck::new(self.tcx).analyze(scrutinee, arms);
        for span in report.unreachable {
            self.emit(
                Diagnostic::lint("unreachable_patterns", "unreachable pattern")
                    .with_span(span)
                    .with_label("the cases above already match every value of this pattern"),
            );
        }
        if report.missing.is_empty() {
            return true;
        }
        if let Coverage::Required(what) = coverage {
            self.emit(
                Diagnostic::error(format!("{what} does not cover every case"))
                    .with_span(span)
                    .with_note(format!(
                        "not covered: {}",
                        describe_missing(&report.missing)
                    ))
                    .with_help("add the missing cases, or a `default` case"),
            );
        }
        false
    }

    pub(crate) fn check_pat(&mut self, pat: &Pat, expected: &Ty) -> DeconPat {
        let expected = expected.strip_refs().clone();
        match &pat.kind {
            PatKind::Wild => DeconPat::wildcard(),
            PatKind::Lit(expr) => {
                let ty = self.check_expr(expr);
                if !self.is_assignable(&ty, &expected) {
                    self.mismatch(expr.span, &expected, &ty);
                }
                DeconPat::new(lit_ctor(expr), Vec::new())
            }
            PatKind::Ty { ty, binding } => {
                let tested = self.lower_ty(ty);
                if let Some(binding) = binding {
                    self.locals.insert(binding.span, tested.clone());
                }
                self.results
                    .pats
                    .insert(pat.span, PatRes::Type(tested.clone()));
                self.type_test(&tested, &expected, ty.span)
            }
            PatKind::Path(path) => match self.resolve_pat_path(pat.span, path, &expected) {
                PatPath::Variant(VariantRef { def, index, .. }) => {
                    let arity = self.tcx.sig(def).variants[index].fields.len();
                    if arity > 0 {
                        self.variant_needs_fields(def, index, path, arity);
                    }
                    match self.variant_pat(def, index, &path.to_string(), &expected, path.span) {
                        Some(ctor @ Ctor::Variant(_)) => {
                            DeconPat::new(ctor, vec![DeconPat::wildcard(); arity])
                        }
                        Some(ctor) => DeconPat::new(ctor, Vec::new()),
                        None => DeconPat::wildcard(),
                    }
                }
                PatPath::Type(ty) => self.type_test(&ty, &expected, path.span),
                PatPath::Const(_, _, ty) => {
                    if !self.is_assignable(&ty, &expected) {
                        self.mismatch(path.span, &expected, &ty);
                    }
                    DeconPat::new(Ctor::Opaque(None), Vec::new())
                }
                PatPath::Error => DeconPat::wildcard(),
            },
            PatKind::Variant { path, fields } => {
                match self.resolve_pat_path(pat.span, path, &expected) {
                    PatPath::Variant(variant) => {
                        self.check_variant_fields(&variant, path, fields, &expected, pat.span)
                    }
                    PatPath::Type(Ty::Adt { def, args, .. })
                        if self.tcx.sig(def).kind == AdtKind::Record =>
                    {
                        self.results.pats.insert(pat.span, PatRes::Record { def });
                        self.check_record_fields(def, args, path, fields, &expected)
                    }
                    found => {
                        if matches!(found, PatPath::Type(_) | PatPath::Const(..)) {
                            self.emit(
                                Diagnostic::error(format!(
                                    "`{path}` is not an enum variant or a record"
                                ))
                                .with_span(path.span)
                                .with_label(
                                    "only enum variants and records can be matched with `(...)`",
                                ),
                            );
                        }
                        for field in fields {
                            self.check_pat(field, &Ty::Unknown);
                        }
                        DeconPat::wildcard()
                    }
                }
            }
        }
    }

    fn resolve_pat_path(&mut self, span: Span, path: &Path, expected: &Ty) -> PatPath {
        let found = self.pat_path(path, expected);
        let res = match &found {
            PatPath::Variant(VariantRef { def, index, .. }) => PatRes::Variant {
                def: *def,
                index: *index,
            },
            PatPath::Type(ty) => PatRes::Type(ty.clone()),
            PatPath::Const(owner, name, ty) => PatRes::Const {
                owner: *owner,
                name: name.name,
                ty: ty.clone(),
            },
            PatPath::Error => return found,
        };
        self.results.pats.insert(span, res);
        found
    }

    fn check_record_fields(
        &mut self,
        def: DefId,
        args: Vec<Ty>,
        path: &Path,
        fields: &[Pat],
        expected: &Ty,
    ) -> DeconPat {
        let args = match expected.non_null() {
            Ty::Adt {
                def: expected,
                args,
                ..
            } if *expected == def => args.clone(),
            _ => args,
        };
        let subst = self.tcx.subst_for(def, &args);
        let sig = self.tcx.sig(def);
        let component_tys: Vec<Ty> = sig
            .components
            .iter()
            .map(|name| sig.fields[name].ty.subst(&subst))
            .collect();
        if fields.len() != component_tys.len() {
            self.emit(
                Diagnostic::error(format!(
                    "this pattern has {}, but the record `{}` has {} {}",
                    plural_fields(fields.len()),
                    self.type_name(def),
                    component_tys.len(),
                    if component_tys.len() == 1 {
                        "component"
                    } else {
                        "components"
                    }
                ))
                .with_span(path.span),
            );
            for field in fields {
                self.check_pat(field, &Ty::Unknown);
            }
            return DeconPat::wildcard();
        }

        let fields: Vec<DeconPat> = fields
            .iter()
            .zip(&component_tys)
            .map(|(field, ty)| self.check_pat(field, ty))
            .collect();
        let record_ty = self.tcx.self_ty(def);
        match expected.non_null() {
            Ty::Adt { def: expected, .. } if *expected == def => {
                DeconPat::new(Ctor::Variant(0), fields)
            }
            ty if ty.references_unknown() => DeconPat::wildcard(),
            ty if self.is_assignable(&record_ty, ty) || self.is_interface(ty) => {
                DeconPat::new(Ctor::Opaque(None), Vec::new())
            }
            ty => {
                self.mismatch(path.span, ty, &record_ty);
                DeconPat::wildcard()
            }
        }
    }

    fn check_variant_fields(
        &mut self,
        variant: &VariantRef,
        path: &Path,
        fields: &[Pat],
        expected: &Ty,
        span: Span,
    ) -> DeconPat {
        let VariantRef { def, index, .. } = *variant;
        let subst = self.tcx.subst_for(def, &variant.args);
        let field_tys: Vec<Ty> = self.tcx.sig(def).variants[index]
            .fields
            .iter()
            .map(|field| field.ty.subst(&subst))
            .collect();

        if field_tys.is_empty() {
            self.emit(
                Diagnostic::error(format!(
                    "the variant `{}` has no fields",
                    self.variant_name(def, index)
                ))
                .with_span(span)
                .with_help(format!("write `{path}` without parentheses")),
            );
            for field in fields {
                self.check_pat(field, &Ty::Unknown);
            }
            return DeconPat::wildcard();
        }
        if fields.len() != field_tys.len() {
            self.emit(
                Diagnostic::error(format!(
                    "this pattern has {}, but the variant `{}` has {}",
                    plural_fields(fields.len()),
                    self.variant_name(def, index),
                    plural_fields(field_tys.len())
                ))
                .with_span(path.span)
                .with_label(format!("expected {}", plural_fields(field_tys.len()))),
            );
            for field in fields {
                self.check_pat(field, &Ty::Unknown);
            }
            return DeconPat::wildcard();
        }

        let fields: Vec<DeconPat> = fields
            .iter()
            .zip(&field_tys)
            .map(|(field, ty)| self.check_pat(field, ty))
            .collect();
        match self.variant_pat(def, index, &path.to_string(), expected, path.span) {
            Some(Ctor::Variant(index)) => DeconPat::new(Ctor::Variant(index), fields),
            Some(_) => DeconPat::new(Ctor::Opaque(None), Vec::new()),
            None => DeconPat::wildcard(),
        }
    }

    fn variant_pat(
        &self,
        def: DefId,
        index: usize,
        path: &str,
        expected: &Ty,
        span: Span,
    ) -> Option<Ctor> {
        match expected.non_null() {
            Ty::Adt { def: expected, .. } if *expected == def => Some(Ctor::Variant(index)),
            ty if ty.references_unknown() => None,
            ty => {
                let enum_ty = self.tcx.self_ty(def);
                if self.is_assignable(&enum_ty, ty) {
                    Some(Ctor::Opaque(Some(path.to_owned())))
                } else {
                    self.mismatch(span, ty, &enum_ty);
                    None
                }
            }
        }
    }

    fn variant_needs_fields(&self, def: DefId, index: usize, path: &Path, arity: usize) {
        let blanks = vec!["_"; arity].join(", ");
        self.emit(
            Diagnostic::error(format!(
                "the variant `{}` has fields",
                self.variant_name(def, index)
            ))
            .with_span(path.span)
            .with_help(format!(
                "match its fields with `{path}(...)`, or ignore them with `{path}({blanks})`"
            )),
        );
    }

    fn type_test(&self, tested: &Ty, expected: &Ty, span: Span) -> DeconPat {
        let tested = tested.strip_refs();
        let unknown = |ty: &Ty| ty.references_unknown();
        if unknown(tested) || unknown(expected) {
            return DeconPat::wildcard();
        }
        if tested.primitive().is_some() || expected.primitive().is_some() {
            if tested != expected.non_null() {
                self.mismatch(span, expected, tested);
            }
            return DeconPat::wildcard();
        }
        if self.is_assignable(expected, tested) {
            return DeconPat::wildcard();
        }
        if !self.is_assignable(tested, expected)
            && !self.is_interface(tested)
            && !self.is_interface(expected)
        {
            self.mismatch(span, expected, tested);
            return DeconPat::wildcard();
        }
        DeconPat::new(Ctor::Opaque(Some(tested.to_string())), Vec::new())
    }

    fn pat_path(&mut self, path: &Path, expected: &Ty) -> PatPath {
        match path.segments.as_slice() {
            [name] => self.single_pat_path(*name, expected),
            [.., owner, name] => self.qualified_pat_path(*owner, *name, expected),
            [] => PatPath::Error,
        }
    }

    fn single_pat_path(&mut self, name: Ident, expected: &Ty) -> PatPath {
        let enum_def = self.enum_def(expected);
        let variant = enum_def
            .as_ref()
            .and_then(|(def, args)| Some((*def, args.clone(), self.variant_index(*def, name)?)));
        if let Some((def, args, index)) = variant {
            return PatPath::Variant(VariantRef { def, args, index });
        }
        if let Some(ty) = self.type_of_ident(name) {
            return PatPath::Type(ty);
        }
        let message = match enum_def {
            Some((def, _)) => format!(
                "no variant `{}` in enum `{}`",
                name.name,
                self.type_name(def)
            ),
            None => format!("cannot find value `{}` in this scope", name.name),
        };
        self.error(name.span, message);
        PatPath::Error
    }

    fn qualified_pat_path(&mut self, owner: Ident, name: Ident, expected: &Ty) -> PatPath {
        let Some(Ty::Adt { def, .. }) = self.type_of_ident(owner) else {
            return PatPath::Error;
        };
        if let Some(nested) = self.tcx.nested_type(def, name.name) {
            return PatPath::Type(Ty::Adt {
                def: nested,
                name: name.name,
                args: Vec::new(),
            });
        }
        if let Some(index) = self.variant_index(def, name) {
            let args = match self.enum_def(expected) {
                Some((expected, args)) if expected == def => args,
                _ => Vec::new(),
            };
            return PatPath::Variant(VariantRef { def, args, index });
        }
        match self.static_const(def, name) {
            Some(ty) => PatPath::Const(def, name, ty),
            None => {
                self.error(
                    name.span,
                    format!(
                        "no variant or constant `{}` in `{}`",
                        name.name,
                        self.type_name(def)
                    ),
                );
                PatPath::Error
            }
        }
    }

    fn static_const(&self, def: DefId, name: Ident) -> Option<Ty> {
        let field = self.tcx.sig(def).fields.get(&name.name)?;
        if !matches!(field.storage, FieldStorage::Static(_)) {
            return None;
        }
        self.check_vis(field.vis, field.owner, true, "field", name);
        Some(field.ty.clone())
    }

    fn enum_def(&self, ty: &Ty) -> Option<(DefId, Vec<Ty>)> {
        match ty.strip_refs().non_null() {
            Ty::Adt { def, args, .. } if self.tcx.sig(*def).kind == AdtKind::Enum => {
                Some((*def, args.clone()))
            }
            _ => None,
        }
    }

    pub(crate) fn is_enum(&self, ty: &Ty) -> bool {
        self.enum_def(ty).is_some()
    }

    fn variant_index(&self, def: DefId, name: Ident) -> Option<usize> {
        self.tcx
            .sig(def)
            .variants
            .iter()
            .position(|variant| variant.name.name == name.name)
    }

    fn variant_name(&self, def: DefId, index: usize) -> String {
        format!(
            "{}.{}",
            self.type_name(def),
            self.tcx.sig(def).variants[index].name.name
        )
    }

    fn is_interface(&self, ty: &Ty) -> bool {
        match ty.non_null() {
            Ty::Adt { def, .. } => self.tcx.sig(*def).kind == AdtKind::Interface,
            _ => false,
        }
    }
}

fn lit_ctor(expr: &Expr) -> Ctor {
    match &expr.kind {
        ExprKind::Bool(value) => Ctor::Bool(*value),
        ExprKind::Lit(_) | ExprKind::Null => Ctor::Opaque(Some(expr.to_string())),
        ExprKind::Unary {
            op: UnOp::Neg,
            expr: operand,
        } if matches!(operand.kind, ExprKind::Lit(_)) => Ctor::Opaque(Some(expr.to_string())),
        _ => Ctor::Opaque(None),
    }
}

fn plural_fields(count: usize) -> String {
    match count {
        1 => "1 field".to_owned(),
        count => format!("{count} fields"),
    }
}

fn describe_missing(missing: &[Witness]) -> String {
    const SHOWN: usize = 3;
    if let [Witness::Wild] = missing {
        return "other values".to_owned();
    }
    let shown: Vec<String> = missing
        .iter()
        .take(SHOWN)
        .map(|witness| format!("`{witness}`"))
        .collect();
    match shown.split_last() {
        Some((last, [])) => last.clone(),
        Some((last, rest)) if missing.len() <= SHOWN => format!("{} and {last}", rest.join(", ")),
        _ => format!("{} and {} more", shown.join(", "), missing.len() - SHOWN),
    }
}
