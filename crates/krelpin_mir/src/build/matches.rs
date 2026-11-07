use krelpin_ast::ast::{BinOp, ReceiverKind};
use krelpin_hir::{Arm, ArmBody, Dispatch, Expr, LocalId, Pat, PatKind};
use krelpin_span::def_id::DefId;
use krelpin_span::{Span, Symbol};
use krelpin_typeck::{AdtKind, Callee, LangItem, Ty};

use super::expr::deref;
use super::{Builder, Scope};
use crate::mir::{BasicBlock, Operand, Place, PlaceBase, PlaceElem, Rvalue, TerminatorKind};

pub(super) struct Binding {
    id: LocalId,
    place: Place,
    ty: Ty,
}

enum Compared<'h> {
    Expr(&'h Expr),
    Static { owner: DefId, name: Symbol, ty: Ty },
}

impl<'h> Builder<'_, 'h, '_> {
    pub(super) fn lower_switch(
        &mut self,
        scrutinee: &'h Expr,
        arms: &'h [Arm],
        dest: Option<Place>,
        span: Span,
    ) {
        let place = self.as_place(scrutinee);
        let exit = self.new_block();
        let scope = match &dest {
            Some(dest) => Scope::Value {
                dest: dest.clone(),
                exit,
            },
            None => Scope::Breakable {
                exit,
                label: self.label.take(),
            },
        };
        self.scopes.push(scope);

        for arm in arms {
            let next_arm = self.new_block();
            let matched = self.new_block();
            let mut bindings = Vec::new();
            for (index, pat) in arm.pats.iter().enumerate() {
                let fail = if index + 1 == arm.pats.len() {
                    next_arm
                } else {
                    self.new_block()
                };
                self.test_pat(place.clone(), &scrutinee.ty, pat, fail, &mut bindings);
                self.goto(matched, pat.span);
                self.current = fail;
            }

            self.current = matched;
            self.push_block_scope();
            if let Some(guard) = &arm.guard {
                for binding in &bindings {
                    self.vars.insert(binding.id, binding.place.clone());
                }
                let (pass, fail) = self.lower_cond(guard);
                self.current = fail;
                self.goto(next_arm, guard.span);
                self.current = pass;
            }
            self.bind(bindings, &scrutinee.ty, arm.span);
            match &arm.body {
                ArmBody::Expr(value) => {
                    let dest = dest
                        .clone()
                        .unwrap_or_else(|| unreachable!("a `switch` statement arm has a value"));
                    self.expr_into(dest, value);
                }
                ArmBody::Block(block) => self.lower_block(block),
                ArmBody::Throw(value) => {
                    let value = self.as_operand(value);
                    let unwind = self.unwind();
                    self.diverge(TerminatorKind::Throw { value, unwind }, arm.span);
                }
            }
            self.pop_block_scope(arm.span);
            self.goto(exit, arm.span);
            self.current = next_arm;
        }

        self.scopes.pop();
        if dest.is_some() || self.is_enum(&scrutinee.ty) {
            self.terminate(TerminatorKind::Unreachable, span);
        } else {
            self.goto(exit, span);
        }
        self.current = exit;
    }

    fn is_enum(&self, ty: &Ty) -> bool {
        matches!(
            ty.strip_refs().non_null(),
            Ty::Adt { def, .. } if self.tcx().sig(*def).kind == AdtKind::Enum
        )
    }

    /// Declares the variables a pattern binds. A value that can't be moved
    /// out is bound by reference, a mutable one when the matched value is
    /// reached through `&mut`.
    pub(super) fn bind(&mut self, bindings: Vec<Binding>, scrutinee: &Ty, span: Span) {
        let mutable = matches!(scrutinee.non_null(), Ty::Ref { mutable: true, .. });
        for Binding { id, place, ty } in bindings {
            self.bind_var_as(id, place, &ty, mutable, span);
        }
    }

    pub(super) fn test_pat(
        &mut self,
        place: Place,
        ty: &Ty,
        pat: &'h Pat,
        fail: BasicBlock,
        bindings: &mut Vec<Binding>,
    ) {
        let place = deref(place, ty);
        let ty = ty.strip_refs();
        let span = pat.span;
        match &pat.kind {
            PatKind::Wild => {}
            PatKind::Lit(value) => {
                self.test_equal(place, ty, Compared::Expr(value), fail, span);
            }
            PatKind::Const { owner, name } => {
                let const_ty = self
                    .tcx()
                    .sig(*owner)
                    .fields
                    .get(name)
                    .map_or(Ty::Unknown, |field| field.ty.clone());
                let compared = Compared::Static {
                    owner: *owner,
                    name: *name,
                    ty: const_ty,
                };
                self.test_equal(place, ty, compared, fail, span);
            }
            PatKind::Binding { local, ty: tested } => {
                let view = self.test_type(place, ty, tested, fail, span);
                if let Some(id) = local {
                    bindings.push(Binding {
                        id: *id,
                        place: view,
                        ty: tested.clone(),
                    });
                }
            }
            PatKind::Variant { def, index, fields } => {
                let enum_ty = self.adt_ty(*def, ty);
                let view = self.test_type(place, ty, &enum_ty, fail, span);
                let discriminant = self.temp(&Ty::INT, span);
                self.assign(
                    Place::local(discriminant),
                    Rvalue::Discriminant(view.clone()),
                    span,
                );
                let matched = self.new_block();
                self.terminate(
                    TerminatorKind::SwitchInt {
                        discr: Operand::Move(Place::local(discriminant)),
                        targets: vec![(*index as u64, matched)],
                        otherwise: fail,
                    },
                    span,
                );
                self.current = matched;
                let variant = view.project(PlaceElem::Variant {
                    def: *def,
                    index: *index,
                });
                let tcx = self.tcx();
                let subst = tcx.subst_for(*def, adt_args(&enum_ty));
                let field_sigs = &tcx.sig(*def).variants[*index].fields;
                for (field, sig) in fields.iter().zip(field_sigs) {
                    let field_place = variant.clone().project(PlaceElem::Field {
                        owner: *def,
                        name: sig.name.name,
                    });
                    let field_ty = sig.ty.subst(&subst);
                    self.test_pat(field_place, &field_ty, field, fail, bindings);
                }
            }
            PatKind::Record { def, fields } => {
                let record_ty = self.adt_ty(*def, ty);
                let view = self.test_type(place, ty, &record_ty, fail, span);
                let tcx = self.tcx();
                let sig = tcx.sig(*def);
                let subst = tcx.subst_for(*def, adt_args(&record_ty));
                for (field, name) in fields.iter().zip(&sig.components) {
                    let field_ty = sig
                        .fields
                        .get(name)
                        .map_or(Ty::Unknown, |field| field.ty.subst(&subst));
                    let field_place = view.clone().project(PlaceElem::Field {
                        owner: *def,
                        name: *name,
                    });
                    self.test_pat(field_place, &field_ty, field, fail, bindings);
                }
            }
        }
    }

    fn adt_ty(&self, def: DefId, scrutinee: &Ty) -> Ty {
        match scrutinee.non_null() {
            ty @ Ty::Adt { def: found, .. } if *found == def => ty.clone(),
            _ => self.tcx().self_ty(def),
        }
    }

    fn test_type(
        &mut self,
        place: Place,
        ty: &Ty,
        tested: &Ty,
        fail: BasicBlock,
        span: Span,
    ) -> Place {
        let may_be_null =
            matches!(ty.strip_refs(), Ty::Nullable(_)) && !matches!(tested, Ty::Nullable(_));
        if !may_be_null && self.statically_is(ty, tested) {
            return place;
        }
        let is = self.temp(&Ty::BOOLEAN, span);
        self.assign(
            Place::local(is),
            Rvalue::InstanceOf(place.clone(), tested.clone()),
            span,
        );
        let matched = self.new_block();
        self.terminate(
            TerminatorKind::SwitchInt {
                discr: Operand::Move(Place::local(is)),
                targets: vec![(0, fail)],
                otherwise: matched,
            },
            span,
        );
        self.current = matched;
        place.project(PlaceElem::Subtype(tested.clone()))
    }

    fn test_equal(
        &mut self,
        place: Place,
        ty: &Ty,
        compared: Compared<'h>,
        fail: BasicBlock,
        span: Span,
    ) {
        let equal = self.temp(&Ty::BOOLEAN, span);
        if ty.non_null().primitive().is_some() {
            let value = match compared {
                Compared::Expr(value) => self.as_operand(value),
                Compared::Static { owner, name, .. } => Operand::Copy(static_place(owner, name)),
            };
            self.assign(
                Place::local(equal),
                Rvalue::Binary(BinOp::Eq, Operand::Copy(place), value),
                span,
            );
        } else {
            let (value, value_ty) = match compared {
                Compared::Expr(value) => (self.as_place(value), value.ty.clone()),
                Compared::Static { owner, name, ty } => (static_place(owner, name), ty),
            };
            let callee = self.equals_callee(ty);
            let lhs = self.receiver_operand(place, ty, Some(ReceiverKind::Ref), span);
            let rhs = self.receiver_operand(value, &value_ty, Some(ReceiverKind::Ref), span);
            self.call(
                &callee,
                Dispatch::Virtual,
                vec![lhs, rhs],
                Some(Place::local(equal)),
                span,
            );
        }
        let matched = self.new_block();
        self.terminate(
            TerminatorKind::SwitchInt {
                discr: Operand::Move(Place::local(equal)),
                targets: vec![(0, fail)],
                otherwise: matched,
            },
            span,
        );
        self.current = matched;
    }

    fn equals_callee(&self, ty: &Ty) -> Callee {
        let tcx = self.tcx();
        let equatable = tcx
            .lang_items
            .get(LangItem::Equatable)
            .unwrap_or_else(|| unreachable!("the standard library defines `Equatable`"));
        let method = tcx
            .sig(equatable)
            .methods
            .get(&Symbol::intern("equals"))
            .and_then(|methods| methods.first())
            .cloned()
            .unwrap_or_else(|| unreachable!("`Equatable` declares `equals`"));
        Callee {
            method,
            params: vec![Ty::Ref {
                mutable: false,
                ty: Box::new(ty.non_null().clone()),
            }],
            ret: Ty::BOOLEAN,
            packs_varargs: false,
            subst: tcx.subst_for(equatable, &[ty.non_null().clone()]),
        }
    }
}

fn static_place(owner: DefId, name: Symbol) -> Place {
    Place {
        base: PlaceBase::Static { owner, name },
        projection: Vec::new(),
    }
}

fn adt_args(ty: &Ty) -> &[Ty] {
    match ty {
        Ty::Adt { args, .. } => args,
        _ => &[],
    }
}
