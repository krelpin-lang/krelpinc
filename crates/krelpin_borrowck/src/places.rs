use krelpin_ast::ast::FieldStorage;
use krelpin_mir::{
    Body, CaptureMode, Check, Local, Operand, Place, PlaceBase, PlaceElem, Rvalue, StatementKind,
    TerminatorKind,
};
use krelpin_span::Symbol;
use krelpin_span::def_id::DefId;
use krelpin_typeck::{AdtKind, Tcx, Ty};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Access {
    Read,
    Move,
    Write,
    Borrow { mutable: bool },
}

impl Access {
    pub(crate) fn mutates(self) -> bool {
        matches!(self, Access::Write | Access::Borrow { mutable: true })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum PathElem {
    Field(DefId, Symbol),
    Capture(usize),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct PlacePath {
    pub(crate) local: Local,
    pub(crate) elems: Vec<PathElem>,
    pub(crate) indirect: bool,
}

impl PlacePath {
    pub(crate) fn of(place: &Place) -> Option<PlacePath> {
        let PlaceBase::Local(local) = place.base else {
            return None;
        };
        let mut elems = Vec::new();
        for elem in &place.projection {
            match elem {
                PlaceElem::Field { owner, name } => elems.push(PathElem::Field(*owner, *name)),
                PlaceElem::Capture(index) => elems.push(PathElem::Capture(*index)),
                PlaceElem::Variant { .. } | PlaceElem::Subtype(_) => {}
                PlaceElem::Deref | PlaceElem::Index(_) => {
                    return Some(PlacePath {
                        local,
                        elems,
                        indirect: true,
                    });
                }
            }
        }
        Some(PlacePath {
            local,
            elems,
            indirect: false,
        })
    }

    pub(crate) fn is_prefix_of(&self, other: &PlacePath) -> bool {
        self.local == other.local && other.elems.starts_with(&self.elems)
    }

    pub(crate) fn related(&self, other: &PlacePath) -> bool {
        self.is_prefix_of(other) || other.is_prefix_of(self)
    }
}

pub(crate) fn overlaps(a: &Place, b: &Place) -> bool {
    if a.base != b.base {
        return false;
    }
    let a = significant(a);
    let b = significant(b);
    for (x, y) in a.iter().zip(&b) {
        match (x, y) {
            (PlaceElem::Field { owner, name }, PlaceElem::Field { owner: o, name: n })
                if (owner, name) != (o, n) =>
            {
                return false;
            }
            (PlaceElem::Capture(x), PlaceElem::Capture(y)) if x != y => return false,
            _ => {}
        }
    }
    true
}

fn significant(place: &Place) -> Vec<&PlaceElem> {
    place
        .projection
        .iter()
        .filter(|elem| !matches!(elem, PlaceElem::Variant { .. } | PlaceElem::Subtype(_)))
        .collect()
}

pub(crate) fn has_deref(place: &Place) -> bool {
    place
        .projection
        .iter()
        .any(|elem| matches!(elem, PlaceElem::Deref))
}

pub(crate) fn base_local(place: &Place) -> Option<Local> {
    match place.base {
        PlaceBase::Local(local) => Some(local),
        PlaceBase::Static { .. } => None,
    }
}

pub(crate) fn operand_place(operand: &Operand) -> Option<&Place> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        Operand::Constant(_) => None,
    }
}

fn operand_access(operand: &Operand, out: &mut Vec<(Place, Access)>) {
    match operand {
        Operand::Copy(place) => out.push((place.clone(), Access::Read)),
        Operand::Move(place) => out.push((place.clone(), Access::Move)),
        Operand::Constant(_) => {}
    }
}

pub(crate) fn rvalue_accesses(rvalue: &Rvalue, out: &mut Vec<(Place, Access)>) {
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::Unary(_, operand)
        | Rvalue::Cast(operand, _)
        | Rvalue::NewArray { len: operand, .. } => operand_access(operand, out),
        Rvalue::Binary(_, lhs, rhs) => {
            operand_access(lhs, out);
            operand_access(rhs, out);
        }
        Rvalue::Aggregate(_, operands) => {
            for operand in operands {
                operand_access(operand, out);
            }
        }
        Rvalue::Ref { mutable, place } => {
            out.push((place.clone(), Access::Borrow { mutable: *mutable }))
        }
        Rvalue::Len(place)
        | Rvalue::Discriminant(place)
        | Rvalue::InstanceOf(place, _)
        | Rvalue::IsNull(place) => out.push((place.clone(), Access::Read)),
        Rvalue::New(_) | Rvalue::Caught => {}
    }
}

pub(crate) fn statement_accesses(kind: &StatementKind) -> Vec<(Place, Access)> {
    let mut out = Vec::new();
    match kind {
        StatementKind::Assign(assign) => {
            let (place, rvalue) = assign.as_ref();
            rvalue_accesses(rvalue, &mut out);
            out.push((place.clone(), Access::Write));
        }
        StatementKind::FakeRead(place) => out.push((place.clone(), Access::Read)),
        StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => {}
    }
    out
}

pub(crate) fn terminator_accesses(kind: &TerminatorKind) -> Vec<(Place, Access)> {
    let mut out = Vec::new();
    match kind {
        TerminatorKind::Goto { .. }
        | TerminatorKind::Suspend { .. }
        | TerminatorKind::Return
        | TerminatorKind::Unreachable => {}
        TerminatorKind::SwitchInt { discr, .. } => operand_access(discr, &mut out),
        TerminatorKind::Call { args, dest, .. } => {
            for arg in args {
                operand_access(arg, &mut out);
            }
            if let Some(dest) = dest {
                out.push((dest.clone(), Access::Write));
            }
        }
        TerminatorKind::Throw { value, .. } => operand_access(value, &mut out),
        TerminatorKind::Assert { check, .. } => match check {
            Check::Bounds { index, len } => {
                operand_access(index, &mut out);
                operand_access(len, &mut out);
            }
            Check::NonZero(operand) => operand_access(operand, &mut out),
            Check::InstanceOf { place, .. } => out.push((place.clone(), Access::Read)),
        },
    }
    out
}

pub(crate) struct PlaceTys<'a, 'tcx> {
    pub(crate) tcx: &'a Tcx<'tcx>,
    pub(crate) body: &'a Body,
}

pub(crate) struct Immutable {
    pub(crate) through: Place,
    pub(crate) is_static: bool,
}

impl PlaceTys<'_, '_> {
    pub(crate) fn place_ty(&self, place: &Place) -> Ty {
        self.walk(place, |_, _| {})
    }

    pub(crate) fn immutable_prefix(&self, place: &Place) -> Option<Immutable> {
        if let PlaceBase::Static { owner, name } = place.base {
            let stateless = self
                .tcx
                .sig(owner)
                .fields
                .get(&name)
                .is_some_and(|field| field.stateless);
            if stateless && place.projection.is_empty() {
                return None;
            }
            return Some(Immutable {
                through: place.clone(),
                is_static: true,
            });
        }
        let mut found = None;
        self.walk(place, |prefix, ty| {
            if found.is_none() && matches!(ty, Ty::Ref { mutable: false, .. }) {
                found = Some(prefix.clone());
            }
        });
        found.map(|through| Immutable {
            through,
            is_static: false,
        })
    }

    fn walk(&self, place: &Place, mut before_deref: impl FnMut(&Place, &Ty)) -> Ty {
        let mut ty = match place.base {
            PlaceBase::Local(local) => self.body.local(local).ty.clone(),
            PlaceBase::Static { owner, name } => self
                .tcx
                .sig(owner)
                .fields
                .get(&name)
                .map_or(Ty::Unknown, |field| field.ty.clone()),
        };
        let mut prefix = Place {
            base: place.base,
            projection: Vec::new(),
        };
        let mut variant = None;
        for elem in &place.projection {
            ty = match elem {
                PlaceElem::Deref => {
                    before_deref(&prefix, &ty);
                    match ty.non_null() {
                        Ty::Ref { ty, .. } => ty.as_ref().clone(),
                        _ => Ty::Unknown,
                    }
                }
                PlaceElem::Field { owner, name } => {
                    let field = self.field_ty(&ty, *owner, *name, variant);
                    variant = None;
                    field
                }
                PlaceElem::Index(_) => match ty.non_null() {
                    Ty::Array(elem) => elem.as_ref().clone(),
                    _ => Ty::Unknown,
                },
                PlaceElem::Variant { index, .. } => {
                    variant = Some(*index);
                    ty
                }
                PlaceElem::Subtype(sub) => sub.clone(),
                PlaceElem::Capture(index) => {
                    let capture = &self.body.captures[*index];
                    match capture.mode {
                        CaptureMode::Value => capture.ty.clone(),
                        CaptureMode::Ref | CaptureMode::RefMut => Ty::Ref {
                            mutable: capture.mode == CaptureMode::RefMut,
                            ty: Box::new(capture.ty.clone()),
                        },
                    }
                }
            };
            prefix.projection.push(elem.clone());
        }
        ty
    }

    fn field_ty(&self, base: &Ty, owner: DefId, name: Symbol, variant: Option<usize>) -> Ty {
        let Ty::Adt { def, args, .. } = base.non_null() else {
            return Ty::Unknown;
        };
        let args = self.tcx.upcast(*def, args, owner).unwrap_or_default();
        let subst = self.tcx.subst_for(owner, &args);
        let sig = self.tcx.sig(owner);
        let ty = match variant {
            Some(index) => sig.variants[index]
                .fields
                .iter()
                .find(|field| field.name.name == name)
                .map(|field| field.ty.clone()),
            None => sig.fields.get(&name).map(|field| field.ty.clone()),
        };
        ty.map_or(Ty::Unknown, |ty| ty.subst(&subst))
    }

    pub(crate) fn is_view(&self, ty: &Ty) -> bool {
        matches!(ty.non_null(), Ty::Adt { def, .. } if !self.tcx.sig(*def).borrow_params.is_empty())
    }

    pub(crate) fn may_hold_refs(&self, ty: &Ty) -> bool {
        self.may_hold_refs_inner(ty, &mut Vec::new())
    }

    fn may_hold_refs_inner(&self, ty: &Ty, visiting: &mut Vec<DefId>) -> bool {
        match ty {
            Ty::Ref { .. } | Ty::Param(_) => true,
            Ty::Primitive(_) | Ty::Null | Ty::Void | Ty::Unknown => false,
            Ty::Nullable(inner) | Ty::Array(inner) => self.may_hold_refs_inner(inner, visiting),
            Ty::Adt { def, args, .. } => {
                if args
                    .iter()
                    .any(|arg| self.may_hold_refs_inner(arg, visiting))
                {
                    return true;
                }
                if visiting.contains(def) {
                    return false;
                }
                let sig = self.tcx.sig(*def);
                if !sig.borrow_params.is_empty() {
                    return true;
                }
                if sig.kind == AdtKind::Interface {
                    return self.tcx.fn_receiver(ty).is_some();
                }
                visiting.push(*def);
                let holds = sig
                    .fields
                    .values()
                    .filter(|field| field.storage == FieldStorage::Instance)
                    .map(|field| field.ty.clone())
                    .chain(
                        sig.variants
                            .iter()
                            .flat_map(|variant| &variant.fields)
                            .map(|field| field.ty.clone()),
                    )
                    .chain(sig.superclass.clone())
                    .any(|field| self.may_hold_refs_inner(&field, visiting));
                visiting.pop();
                holds
            }
        }
    }

    pub(crate) fn describe(&self, place: &Place) -> String {
        let mut out = match place.base {
            PlaceBase::Local(local) => self
                .body
                .local(local)
                .name
                .map_or_else(|| "value".to_owned(), |name| name.to_string()),
            PlaceBase::Static { owner, name } => {
                format!("{}.{name}", self.tcx.ty_name(owner))
            }
        };
        for elem in &place.projection {
            match elem {
                PlaceElem::Field { name, .. } => {
                    out.push('.');
                    out.push_str(name.as_str());
                }
                PlaceElem::Index(_) => out.push_str("[..]"),
                PlaceElem::Capture(index) => {
                    out = self.body.captures[*index].name.to_string();
                }
                PlaceElem::Deref | PlaceElem::Variant { .. } | PlaceElem::Subtype(_) => {}
            }
        }
        out
    }

    pub(crate) fn is_capture(&self, place: &Place) -> bool {
        place
            .projection
            .iter()
            .any(|elem| matches!(elem, PlaceElem::Capture(_)))
    }
}
