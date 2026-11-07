use krelpin_ast::ast::PrimitiveTy;
use krelpin_span::def_id::DefId;

use crate::lang_items::LangItem;
use crate::param_env::ParamEnv;
use crate::sig::Tcx;
use crate::ty::{Ty, promote, widens};

impl Tcx<'_> {
    pub fn is_assignable(&self, env: &ParamEnv, from: &Ty, to: &Ty) -> bool {
        self.assignable(env, from, to, true)
    }

    pub fn is_assignable_exact(&self, env: &ParamEnv, from: &Ty, to: &Ty) -> bool {
        self.assignable(env, from, to, false)
    }

    fn assignable(&self, env: &ParamEnv, from: &Ty, to: &Ty, copying: bool) -> bool {
        let assignable = |from, to| self.assignable(env, from, to, copying);
        match (from, to) {
            (Ty::Unknown, _) | (_, Ty::Unknown) => true,
            _ if from == to => true,
            (Ty::Null, Ty::Nullable(_)) => true,
            (Ty::Nullable(from), Ty::Nullable(to)) => {
                let converts_while_lending = match to.as_ref() {
                    Ty::Ref { ty: inner, .. } => {
                        !matches!(from.as_ref(), Ty::Ref { .. })
                            && from != inner
                            && !inner.is_unknown()
                    }
                    _ => false,
                };
                !converts_while_lending && assignable(from, to)
            }
            (Ty::Nullable(_) | Ty::Null, _) => false,
            (from, Ty::Nullable(to)) => assignable(from, to),
            (Ty::Primitive(from), Ty::Primitive(to)) => widens(*from, *to),
            (Ty::Primitive(primitive), Ty::Adt { .. }) => self
                .lang_items
                .primitive_impl(*primitive)
                .is_some_and(|def| self.adt_assignable(env, def, &[], to)),
            (
                Ty::Ref {
                    mutable: from_mut,
                    ty: from,
                },
                Ty::Ref {
                    mutable: to_mut,
                    ty: to,
                },
            ) => {
                if *to_mut {
                    *from_mut && (from == to || from.is_unknown() || to.is_unknown())
                } else {
                    assignable(from, to)
                        || (matches!(from.as_ref(), Ty::Ref { .. })
                            && assignable(
                                from,
                                &Ty::Ref {
                                    mutable: false,
                                    ty: to.clone(),
                                },
                            ))
                }
            }
            (Ty::Ref { ty: inner, .. }, to) if copying && self.is_copy(inner) => {
                assignable(inner, to)
            }
            (
                from,
                Ty::Ref {
                    mutable: false,
                    ty: to,
                },
            ) if copying && !matches!(from, Ty::Ref { .. } | Ty::Null) && self.is_copy(from) => {
                assignable(from, to)
            }
            (Ty::Ref { .. }, _) | (_, Ty::Ref { .. }) => false,
            (Ty::Primitive(_) | Ty::Void, _) | (_, Ty::Primitive(_) | Ty::Void) => false,
            (_, Ty::Adt { def, .. }) if self.lang_items.is(*def, LangItem::Object) => true,
            (Ty::Array(from), Ty::Array(to)) => from == to || from.is_unknown() || to.is_unknown(),
            (Ty::Param(name), to) => env.bounds(*name).iter().any(|bound| assignable(bound, to)),
            (Ty::Adt { def, args, .. }, to) => self.adt_assignable(env, *def, args, to),
            _ => false,
        }
    }

    fn adt_assignable(&self, env: &ParamEnv, def: DefId, args: &[Ty], to: &Ty) -> bool {
        match to {
            Ty::Adt {
                def: target,
                args: target_args,
                ..
            } if *target == def => return args_compatible(args, target_args),
            _ => {}
        }

        let subst = self.subst_for(def, args);
        let sig = self.sig(def);
        sig.superclass
            .iter()
            .chain(sig.interfaces.iter())
            .map(|parent| parent.subst(&subst))
            .any(|parent| {
                self.implementation_holds(env, def, args, &parent)
                    && self.is_assignable(env, &parent, to)
            })
    }

    pub fn common_ty(&self, env: &ParamEnv, a: &Ty, b: &Ty) -> Option<Ty> {
        match (a, b) {
            (Ty::Null, other) | (other, Ty::Null) => Some(other.clone().nullable()),
            (Ty::Primitive(a), Ty::Primitive(b)) if a == b => Some(Ty::Primitive(*a)),
            (Ty::Primitive(a), Ty::Primitive(b))
                if *a != PrimitiveTy::Boolean && *b != PrimitiveTy::Boolean =>
            {
                promote(*a, *b)
            }
            _ if self.is_assignable(env, a, b) => Some(b.clone()),
            _ if self.is_assignable(env, b, a) => Some(a.clone()),
            _ => None,
        }
    }
}

fn args_compatible(a: &[Ty], b: &[Ty]) -> bool {
    a.is_empty()
        || b.is_empty()
        || (a.len() == b.len()
            && a.iter()
                .zip(b)
                .all(|(a, b)| a == b || a.is_unknown() || b.is_unknown()))
}
