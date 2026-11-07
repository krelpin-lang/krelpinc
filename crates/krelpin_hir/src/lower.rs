use std::collections::HashMap;

use krelpin_ast::ast::{
    self, BinOp, CaseLabel, CompilationUnit, FieldStorage, FnRetTy, Ident, ItemKind, LambdaBody,
    LambdaParam, Member, MemberKind, Param, ReceiverKind, SwitchExprBody, UnOp,
};
use krelpin_resolve::{Res, ResolverOutput};
use krelpin_span::def_id::DefId;
use krelpin_span::{Span, Symbol, kw};
use krelpin_typeck::ty::{promote, widens};
use krelpin_typeck::{BorrowSource, Callee, LangItem, PatRes, Tcx, Ty, TypeckResults};

use crate::captures::{captures, expr_captures};

use crate::hir::{
    Arm, ArmBody, Block, Body, BodyKind, BodyValue, Catch, Closure, ClosureBody, ClosureKind,
    Dispatch, Expr, ExprKind, Hir, LocalDecl, LocalId, LoopKind, Pat, PatKind, ReturnSource, Stmt,
    StmtKind, WithField,
};

pub fn lower(
    units: &[CompilationUnit],
    resolved: &ResolverOutput,
    tcx: &Tcx<'_>,
    results: &TypeckResults,
) -> Hir {
    let mut hir = Hir::default();
    for (type_def, item) in resolved.items.items(units) {
        let members: &[Member] = match &item.kind {
            ItemKind::Class(class) => &class.members,
            ItemKind::Record(def) => &def.members,
            ItemKind::Interface(interface) => &interface.members,
            ItemKind::Enum(def) => &def.members,
        };
        for (index, member) in members.iter().enumerate() {
            let cx = LoweringCtxt {
                tcx,
                resolved,
                results,
                owner: type_def.def,
                locals: Vec::new(),
                by_decl: HashMap::new(),
                this: None,
                rets: Vec::new(),
                yields: Vec::new(),
            };
            if let Some(body) = cx.lower_member(index as u32, member) {
                hir.bodies.push(body);
            }
        }
    }
    hir
}

struct LoweringCtxt<'a, 'tcx> {
    tcx: &'a Tcx<'tcx>,
    resolved: &'a ResolverOutput,
    results: &'a TypeckResults,
    owner: DefId,
    locals: Vec<LocalDecl>,
    by_decl: HashMap<Span, LocalId>,
    this: Option<LocalId>,
    rets: Vec<Ty>,
    yields: Vec<Ty>,
}

impl LoweringCtxt<'_, '_> {
    fn lower_member(mut self, index: u32, member: &Member) -> Option<Body> {
        let (name, kind, receiver, params, ret): (_, _, _, &[Param], _) = match &member.kind {
            MemberKind::Type(_) => return None,
            MemberKind::Field(field) => {
                field.init.as_ref()?;
                let receiver =
                    (field.storage == FieldStorage::Instance).then_some(ReceiverKind::RefMut);
                let ret = self.tcx.lower_ty(&field.ty);
                (field.name.name, BodyKind::FieldInit, receiver, &[], ret)
            }
            MemberKind::Constructor(ctor) => (
                ctor.name.name,
                BodyKind::Constructor,
                Some(ReceiverKind::RefMut),
                &ctor.params,
                Ty::Void,
            ),
            MemberKind::Method(method) => {
                method.body.as_ref()?;
                let ret = match &method.ret {
                    FnRetTy::Void(_) => Ty::Void,
                    FnRetTy::Ty(ty) => self.tcx.lower_ty(ty),
                };
                let receiver = method.receiver.map(|receiver| receiver.kind);
                (
                    method.name.name,
                    BodyKind::Method,
                    receiver,
                    &method.params,
                    ret,
                )
            }
        };

        if let Some(receiver) = receiver {
            let self_ty = self.tcx.self_ty(self.owner);
            let ty = match receiver {
                ReceiverKind::Owned => self_ty,
                ReceiverKind::Ref | ReceiverKind::RefMut => Ty::Ref {
                    mutable: receiver == ReceiverKind::RefMut,
                    ty: Box::new(self_ty),
                },
            };
            self.this = Some(self.push_local(kw::This, ty, member.span));
        }
        let member_params = params;
        let params: Vec<LocalId> = params
            .iter()
            .map(|param| self.declare(param.name.name, param.name.span))
            .collect();

        let output = match &member.kind {
            MemberKind::Method(method) if method.asyncness.is_some() => Some(match &ret {
                Ty::Void => self.tcx.lang_ty(LangItem::Unit),
                ty => ty.clone(),
            }),
            _ => None,
        };
        let ret_sources = match &member.kind {
            // An `async` method's future may hold anything it is given.
            MemberKind::Method(method) if method.asyncness.is_some() => None,
            MemberKind::Method(method) => {
                let class_sources = &self.tcx.sig(self.owner).borrow_params;
                let borrows = self.tcx.ret_borrows(method, class_sources);
                borrows.explicit().map(|sources| {
                    sources
                        .iter()
                        .filter_map(|source| match source {
                            BorrowSource::This => self.this.map(ReturnSource::Whole),
                            BorrowSource::Param(index) => {
                                params.get(*index).copied().map(ReturnSource::Whole)
                            }
                            BorrowSource::Class(name) => {
                                self.this.map(|this| ReturnSource::Contents(this, *name))
                            }
                        })
                        .collect()
                })
            }
            _ => None,
        };
        let param_storage = match &member.kind {
            MemberKind::Method(method) => self.tcx.method_param_storage(method),
            MemberKind::Constructor(ctor) => self.tcx.param_storage(member_params, &ctor.keeps),
            MemberKind::Field(_) | MemberKind::Type(_) => Vec::new(),
        };
        self.rets.push(ret.clone());
        let value = match &member.kind {
            MemberKind::Type(_) => return None,
            MemberKind::Field(field) => {
                let init = self.lower_expr(field.init.as_ref()?);
                BodyValue::Expr(coerce(init, &ret))
            }
            MemberKind::Constructor(ctor) => {
                let mut block = self.lower_block(&ctor.body);
                if let Some(call) = self.implicit_super(ctor.name.span) {
                    block.stmts.insert(0, call);
                }
                if ctor.compact {
                    block
                        .stmts
                        .extend(self.assign_components(&params, ctor.body.span));
                }
                BodyValue::Block(block)
            }
            MemberKind::Method(method) => BodyValue::Block(self.lower_block(method.body.as_ref()?)),
        };
        Some(Body {
            owner: self.owner,
            member: index,
            name,
            kind,
            receiver,
            this: self.this,
            params,
            locals: self.locals,
            ret,
            ret_sources,
            param_storage,
            output,
            value,
            span: member.span,
        })
    }

    /// The `super()` the type checker resolved at `span` for a constructor
    /// that doesn't call one itself.
    fn implicit_super(&self, span: Span) -> Option<Stmt> {
        let callee = self.callee(span)?;
        let this = self.this?;
        Some(Stmt {
            kind: StmtKind::Expr(Expr {
                kind: ExprKind::CtorCall {
                    callee,
                    this: Box::new(self.local_expr(this, span)),
                    args: Vec::new(),
                },
                ty: Ty::Void,
                span,
            }),
            span,
        })
    }

    fn assign_components(&self, params: &[LocalId], span: Span) -> Vec<Stmt> {
        let Some(this) = self.this else {
            return Vec::new();
        };
        params
            .iter()
            .map(|&param| {
                let decl = &self.locals[param.index()];
                let field = Expr {
                    kind: ExprKind::Field {
                        base: Box::new(self.local_expr(this, span)),
                        owner: self.owner,
                        name: decl.name,
                        safe: false,
                    },
                    ty: decl.ty.clone(),
                    span,
                };
                let assign = Expr {
                    kind: ExprKind::Assign {
                        op: None,
                        place: Box::new(field),
                        value: Box::new(self.local_expr(param, span)),
                    },
                    ty: decl.ty.clone(),
                    span,
                };
                Stmt {
                    kind: StmtKind::Expr(assign),
                    span,
                }
            })
            .collect()
    }

    fn push_local(&mut self, name: Symbol, ty: Ty, span: Span) -> LocalId {
        let id = LocalId(self.locals.len() as u32);
        self.locals.push(LocalDecl { name, ty, span });
        id
    }

    fn declare(&mut self, name: Symbol, decl: Span) -> LocalId {
        let ty = self
            .results
            .local_types
            .get(&decl)
            .cloned()
            .unwrap_or(Ty::Unknown);
        let id = self.push_local(name, ty, decl);
        self.by_decl.insert(decl, id);
        id
    }

    fn lower_block(&mut self, block: &ast::Block) -> Block {
        Block {
            stmts: block
                .stmts
                .iter()
                .filter_map(|stmt| self.lower_stmt(stmt))
                .collect(),
            span: block.span,
        }
    }

    fn lower_stmt_as_block(&mut self, stmt: &ast::Stmt) -> Block {
        match &stmt.kind {
            ast::StmtKind::Block(block) => self.lower_block(block),
            _ => Block {
                stmts: self.lower_stmt(stmt).into_iter().collect(),
                span: stmt.span,
            },
        }
    }

    fn lower_stmt(&mut self, stmt: &ast::Stmt) -> Option<Stmt> {
        let kind = match &stmt.kind {
            ast::StmtKind::Local(local) => {
                let init = local.init.as_ref().map(|init| self.lower_expr(init));
                let local = self.declare(local.name.name, local.name.span);
                let ty = self.locals[local.index()].ty.clone();
                StmtKind::Let {
                    local,
                    init: init.map(|init| coerce(init, &ty)),
                }
            }
            ast::StmtKind::Expr(expr) => StmtKind::Expr(self.lower_expr(expr)),
            ast::StmtKind::Block(block) => StmtKind::Block(self.lower_block(block)),
            ast::StmtKind::If { cond, then, els } => StmtKind::If {
                cond: deref_all(self.lower_expr(cond)),
                then: self.lower_stmt_as_block(then),
                els: els.as_deref().map(|els| self.lower_stmt_as_block(els)),
            },
            ast::StmtKind::While { cond, body } => StmtKind::Loop {
                kind: LoopKind::While,
                cond: Some(deref_all(self.lower_expr(cond))),
                update: Vec::new(),
                body: self.lower_stmt_as_block(body),
            },
            ast::StmtKind::DoWhile { body, cond } => StmtKind::Loop {
                kind: LoopKind::DoWhile,
                body: self.lower_stmt_as_block(body),
                cond: Some(deref_all(self.lower_expr(cond))),
                update: Vec::new(),
            },
            ast::StmtKind::For {
                init,
                cond,
                update,
                body,
            } => {
                let mut stmts: Vec<Stmt> = init
                    .iter()
                    .filter_map(|stmt| self.lower_stmt(stmt))
                    .collect();
                let cond = cond.as_ref().map(|cond| deref_all(self.lower_expr(cond)));
                let update = update.iter().map(|expr| self.lower_expr(expr)).collect();
                let body = self.lower_stmt_as_block(body);
                stmts.push(Stmt {
                    kind: StmtKind::Loop {
                        kind: LoopKind::While,
                        cond,
                        update,
                        body,
                    },
                    span: stmt.span,
                });
                StmtKind::Block(Block {
                    stmts,
                    span: stmt.span,
                })
            }
            ast::StmtKind::ForEach {
                name, iter, body, ..
            } => StmtKind::ForEach {
                iter: self.lower_expr(iter),
                local: self.declare(name.name, name.span),
                body: self.lower_stmt_as_block(body),
            },
            ast::StmtKind::Switch { scrutinee, arms } => StmtKind::Switch {
                scrutinee: self.lower_expr(scrutinee),
                arms: arms
                    .iter()
                    .map(|arm| {
                        let (pats, guard) = self.lower_label(&arm.label);
                        Arm {
                            pats,
                            guard,
                            body: ArmBody::Block(self.lower_stmt_as_block(&arm.body)),
                            span: arm.span,
                        }
                    })
                    .collect(),
            },
            ast::StmtKind::Try {
                body,
                catches,
                finally,
            } => StmtKind::Try {
                body: self.lower_block(body),
                catches: catches
                    .iter()
                    .map(|catch| Catch {
                        local: self.declare(catch.name.name, catch.name.span),
                        tys: catch.tys.iter().map(|ty| self.tcx.lower_ty(ty)).collect(),
                        body: self.lower_block(&catch.body),
                    })
                    .collect(),
                finally: finally.as_ref().map(|block| self.lower_block(block)),
            },
            ast::StmtKind::Return(value) => {
                let target = self.rets.last().cloned().unwrap_or(Ty::Unknown);
                StmtKind::Return(
                    value
                        .as_ref()
                        .map(|value| coerce(self.lower_expr(value), &target)),
                )
            }
            ast::StmtKind::Yield(value) => {
                let target = self.yields.last().cloned().unwrap_or(Ty::Unknown);
                StmtKind::Yield(coerce(self.lower_expr(value), &target))
            }
            ast::StmtKind::Throw(value) => StmtKind::Throw(self.lower_expr(value)),
            ast::StmtKind::Break(label) => StmtKind::Break(label.map(|label| label.name)),
            ast::StmtKind::Continue(label) => StmtKind::Continue(label.map(|label| label.name)),
            ast::StmtKind::Labeled { label, body } => StmtKind::Labeled {
                label: label.name,
                body: Box::new(self.lower_stmt(body)?),
            },
            ast::StmtKind::Empty => return None,
        };
        Some(Stmt {
            kind,
            span: stmt.span,
        })
    }

    fn lower_label(&mut self, label: &CaseLabel) -> (Vec<Pat>, Option<Expr>) {
        match label {
            CaseLabel::Default(span) => (
                vec![Pat {
                    kind: PatKind::Wild,
                    span: *span,
                }],
                None,
            ),
            CaseLabel::Case { pats, guard } => {
                let pats = pats.iter().map(|pat| self.lower_pat(pat)).collect();
                let guard = guard.as_ref().map(|guard| self.lower_expr(guard));
                (pats, guard)
            }
        }
    }

    fn lower_pat(&mut self, pat: &ast::Pat) -> Pat {
        let res = self.results.pats.get(&pat.span).cloned();
        let kind = match (&pat.kind, res) {
            (ast::PatKind::Wild, _) => PatKind::Wild,
            (ast::PatKind::Lit(expr), _) => PatKind::Lit(self.lower_expr(expr)),
            (ast::PatKind::Ty { binding, .. }, Some(PatRes::Type(ty))) => PatKind::Binding {
                local: binding.map(|binding| self.declare(binding.name, binding.span)),
                ty,
            },
            (ast::PatKind::Path(_), Some(PatRes::Variant { def, index })) => PatKind::Variant {
                def,
                index,
                fields: Vec::new(),
            },
            (ast::PatKind::Variant { fields, .. }, Some(PatRes::Variant { def, index })) => {
                PatKind::Variant {
                    def,
                    index,
                    fields: fields.iter().map(|field| self.lower_pat(field)).collect(),
                }
            }
            (ast::PatKind::Variant { fields, .. }, Some(PatRes::Record { def })) => {
                PatKind::Record {
                    def,
                    fields: fields.iter().map(|field| self.lower_pat(field)).collect(),
                }
            }
            (ast::PatKind::Path(_), Some(PatRes::Type(ty))) => PatKind::Binding { local: None, ty },
            (ast::PatKind::Path(_), Some(PatRes::Const { owner, name, .. })) => {
                PatKind::Const { owner, name }
            }
            _ => PatKind::Wild,
        };
        Pat {
            kind,
            span: pat.span,
        }
    }

    fn expr_ty(&self, expr: &ast::Expr) -> Ty {
        self.results
            .expr_types
            .get(&expr.span)
            .cloned()
            .unwrap_or(Ty::Unknown)
    }

    fn callee(&self, span: Span) -> Option<Box<Callee>> {
        self.results.callees.get(&span).cloned().map(Box::new)
    }

    fn is_type_name(&self, expr: &ast::Expr) -> bool {
        let name = match &expr.kind {
            ast::ExprKind::Name(name) | ast::ExprKind::Field { name, .. } => name,
            _ => return false,
        };
        matches!(
            self.resolved.resolutions.get(name.span),
            Some(Res::Item(_) | Res::TypeParam(_) | Res::PrimTy(_))
        )
    }

    fn lower_exprs(&mut self, exprs: &[ast::Expr]) -> Vec<Expr> {
        exprs.iter().map(|expr| self.lower_expr(expr)).collect()
    }

    fn lower_expr(&mut self, expr: &ast::Expr) -> Expr {
        let ty = self.expr_ty(expr);
        let kind = match &expr.kind {
            ast::ExprKind::Lit(lit) => ExprKind::Lit(*lit),
            ast::ExprKind::Bool(value) => ExprKind::Bool(*value),
            ast::ExprKind::Null => ExprKind::Null,
            ast::ExprKind::This | ast::ExprKind::Super => match self.this {
                Some(this) => return self.local_expr(this, expr.span),
                None => ExprKind::Unresolved,
            },
            ast::ExprKind::Name(name) => match self.resolved.resolutions.get(name.span) {
                Some(Res::Local(decl)) => match self.by_decl.get(&decl) {
                    Some(&local) => ExprKind::Local(local),
                    None => ExprKind::Unresolved,
                },
                _ => ExprKind::Unresolved,
            },
            ast::ExprKind::Field {
                expr: base,
                name,
                safe,
            } => match self.results.fields.get(&name.span) {
                Some(field) if self.is_type_name(base) => ExprKind::Static {
                    owner: field.owner,
                    name: name.name,
                },
                Some(field) => ExprKind::Field {
                    base: Box::new(self.lower_expr(base)),
                    owner: field.owner,
                    name: name.name,
                    safe: *safe,
                },
                None => {
                    let base = self.lower_expr(base);
                    match base.ty.strip_refs() {
                        Ty::Array(_) => ExprKind::Len {
                            array: Box::new(base),
                        },
                        _ => ExprKind::Unresolved,
                    }
                }
            },
            ast::ExprKind::MethodCall {
                receiver,
                name,
                args,
                safe,
                ..
            } => self.lower_method_call(receiver.as_deref(), name.span, args, *safe),
            ast::ExprKind::Call { callee, args } => match self.callee(callee.span) {
                Some(found) => {
                    let this = self.lower_expr(callee);
                    ExprKind::CtorCall {
                        args: self.lower_args(&found, args),
                        callee: found,
                        this: Box::new(this),
                    }
                }
                None => ExprKind::Unresolved,
            },
            ast::ExprKind::Index { expr: base, index } => ExprKind::Index {
                base: Box::new(self.lower_expr(base)),
                index: Box::new(coerce(self.lower_expr(index), &Ty::INT)),
            },
            ast::ExprKind::New { args, .. } => match self.callee(expr.span) {
                Some(found) => ExprKind::New {
                    args: self.lower_args(&found, args),
                    callee: Some(found),
                },
                // A class without constructors runs its superclass's.
                None => ExprKind::New {
                    callee: match &ty {
                        Ty::Adt { def, .. } if args.is_empty() => {
                            self.callee(self.tcx.sig(*def).name.span)
                        }
                        _ => None,
                    },
                    args: self.lower_exprs(args),
                },
            },
            ast::ExprKind::NewArray { len, .. } => ExprKind::NewArray {
                len: Box::new(coerce(self.lower_expr(len), &Ty::INT)),
            },
            ast::ExprKind::ArrayInit { elems, .. } => {
                let elem = match &ty {
                    Ty::Array(elem) => elem.as_ref().clone(),
                    _ => Ty::Unknown,
                };
                ExprKind::Array {
                    elems: elems
                        .iter()
                        .map(|value| coerce(self.lower_expr(value), &elem))
                        .collect(),
                }
            }
            ast::ExprKind::Unary { op, expr: operand } => {
                let operand = self.lower_expr(operand);
                let operand = match op {
                    UnOp::Neg | UnOp::BitNot => coerce(operand, &ty),
                    UnOp::Not => deref_all(operand),
                    UnOp::PreInc | UnOp::PreDec | UnOp::PostInc | UnOp::PostDec => {
                        deref_all(operand)
                    }
                };
                ExprKind::Unary {
                    op: *op,
                    expr: Box::new(operand),
                }
            }
            ast::ExprKind::Borrow {
                mutable,
                expr: operand,
            } => ExprKind::Borrow {
                mutable: *mutable,
                expr: Box::new(self.lower_expr(operand)),
            },
            ast::ExprKind::Binary { op, lhs, rhs } => {
                let lhs = self.lower_expr(lhs);
                let rhs = self.lower_expr(rhs);
                self.lower_binary(*op, lhs, rhs, &ty)
            }
            ast::ExprKind::Assign { op, lhs, rhs } => {
                let place = self.lower_expr(lhs);
                let value = self.lower_expr(rhs);
                let writes_through = match (op, &place.ty) {
                    (None, Ty::Ref { mutable: true, .. }) => {
                        !matches!(value.ty, Ty::Ref { .. } | Ty::Null | Ty::Unknown)
                    }
                    (Some(_), Ty::Ref { .. }) => true,
                    _ => false,
                };
                let place = if writes_through {
                    deref_all(place)
                } else {
                    place
                };
                let value = match (op, &value.ty, &place.ty) {
                    (None, _, _) => coerce(value, &place.ty),
                    (Some(_), Ty::Primitive(from), Ty::Primitive(to)) if widens(*from, *to) => {
                        coerce(value, &place.ty)
                    }
                    (Some(_), _, _) => value,
                };
                ExprKind::Assign {
                    op: *op,
                    place: Box::new(place),
                    value: Box::new(value),
                }
            }
            ast::ExprKind::Ternary { cond, then, els } => ExprKind::If {
                cond: Box::new(deref_all(self.lower_expr(cond))),
                then: Box::new(coerce(self.lower_expr(then), &ty)),
                els: Box::new(coerce(self.lower_expr(els), &ty)),
            },
            ast::ExprKind::InstanceOf { expr: operand, pat } => ExprKind::Is {
                expr: Box::new(self.lower_expr(operand)),
                pat: Box::new(self.lower_pat(pat)),
            },
            ast::ExprKind::Cast { expr: operand, .. } => ExprKind::Cast {
                expr: Box::new(self.lower_expr(operand)),
            },
            ast::ExprKind::Await(operand) => ExprKind::Await {
                expr: Box::new(self.lower_expr(operand)),
            },
            ast::ExprKind::With { base, fields } => {
                let base = self.lower_expr(base);
                let subst = match base.ty.strip_refs() {
                    Ty::Adt { def, args, .. } => self.tcx.subst_for(*def, args),
                    _ => Default::default(),
                };
                let fields = fields
                    .iter()
                    .map(|field| {
                        let value = self.lower_expr(&field.value);
                        let value = match self.results.fields.get(&field.name.span) {
                            Some(sig) => coerce(value, &sig.ty.subst(&subst)),
                            None => value,
                        };
                        WithField {
                            name: field.name.name,
                            value,
                        }
                    })
                    .collect();
                ExprKind::With {
                    base: Box::new(base),
                    fields,
                    callee: self.callee(expr.span),
                }
            }
            ast::ExprKind::Lambda {
                moves,
                params,
                body,
            } => self.lower_lambda(*moves, params, body, &ty),
            ast::ExprKind::MethodRef { expr: target, name } => self.lower_method_ref(target, *name),
            ast::ExprKind::Switch { scrutinee, arms } => ExprKind::Switch {
                scrutinee: Box::new(self.lower_expr(scrutinee)),
                arms: arms
                    .iter()
                    .map(|arm| {
                        let (pats, guard) = self.lower_label(&arm.label);
                        let body = match &arm.body {
                            SwitchExprBody::Expr(value) => {
                                ArmBody::Expr(coerce(self.lower_expr(value), &ty))
                            }
                            SwitchExprBody::Block(block) => {
                                self.yields.push(ty.clone());
                                let block = self.lower_block(block);
                                self.yields.pop();
                                ArmBody::Block(block)
                            }
                            SwitchExprBody::Throw(value) => ArmBody::Throw(self.lower_expr(value)),
                        };
                        Arm {
                            pats,
                            guard,
                            body,
                            span: arm.span,
                        }
                    })
                    .collect(),
            },
        };
        Expr {
            kind,
            ty,
            span: expr.span,
        }
    }

    fn lower_method_call(
        &mut self,
        receiver: Option<&ast::Expr>,
        name: Span,
        args: &[ast::Expr],
        safe: bool,
    ) -> ExprKind {
        let Some(callee) = self.callee(name) else {
            return ExprKind::Unresolved;
        };
        let dispatch = match receiver.map(|receiver| &receiver.kind) {
            Some(ast::ExprKind::Super) => Dispatch::Static,
            _ if callee.method.receiver.is_none() => Dispatch::Static,
            _ => Dispatch::Virtual,
        };
        let receiver = match (receiver, callee.method.receiver) {
            (Some(base), Some(kind)) if !self.is_type_name(base) => {
                let base = self.lower_expr(base);
                Some(Box::new(auto_ref(base, kind)))
            }
            (None, Some(kind)) => self.this.map(|this| {
                let this = self.local_expr(this, name);
                Box::new(auto_ref(this, kind))
            }),
            _ => None,
        };
        ExprKind::Call {
            args: self.lower_args(&callee, args),
            callee,
            receiver,
            dispatch,
            safe,
        }
    }

    fn lower_binary(&mut self, op: BinOp, lhs: Expr, rhs: Expr, ty: &Ty) -> ExprKind {
        let (lhs, rhs) = match op {
            BinOp::Eq | BinOp::Ne => {
                if let Some(callee) = self.equality_callee(&lhs.ty, &rhs.ty) {
                    return ExprKind::Equals {
                        callee,
                        lhs: Box::new(auto_ref(lhs, ReceiverKind::Ref)),
                        rhs: Box::new(auto_ref(rhs, ReceiverKind::Ref)),
                        negated: op == BinOp::Ne,
                    };
                }
                let through = |expr: Expr, other: &Expr| {
                    if matches!(other.ty, Ty::Null)
                        && matches!(expr.ty, Ty::Ref { .. })
                        && matches!(expr.ty.strip_refs(), Ty::Nullable(_))
                    {
                        deref_all(expr)
                    } else {
                        expr
                    }
                };
                let lhs = through(lhs, &rhs);
                let rhs = through(rhs, &lhs);
                promote_operands(lhs, rhs)
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => promote_operands(lhs, rhs),
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Rem
            | BinOp::BitAnd
            | BinOp::BitOr
            | BinOp::BitXor
                if ty.primitive().is_some() =>
            {
                (coerce(lhs, ty), coerce(rhs, ty))
            }
            BinOp::Shl | BinOp::Shr | BinOp::UShr => {
                let amount = rhs.ty.strip_refs().clone();
                (coerce(lhs, ty), coerce(rhs, &amount))
            }
            BinOp::Elvis => {
                let lhs = match &lhs.ty {
                    Ty::Ref { ty: slot, .. }
                        if matches!(slot.as_ref(), Ty::Nullable(_)) && self.tcx.is_copy(slot) =>
                    {
                        deref_all(lhs)
                    }
                    _ => lhs,
                };
                (lhs, coerce(rhs, ty))
            }
            BinOp::And | BinOp::Or => (deref_all(lhs), deref_all(rhs)),
            _ => (lhs, rhs),
        };
        ExprKind::Binary {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }

    fn equality_callee(&self, lhs: &Ty, rhs: &Ty) -> Option<Box<Callee>> {
        if matches!(lhs, Ty::Null) || matches!(rhs, Ty::Null) {
            return None;
        }
        let operand = lhs.strip_refs().non_null();
        if operand.primitive().is_some() || operand.is_unknown() {
            return None;
        }
        let equatable = self.tcx.lang_items.get(LangItem::Equatable)?;
        let method = self
            .tcx
            .sig(equatable)
            .methods
            .get(&Symbol::intern("equals"))?
            .first()?
            .clone();
        Some(Box::new(Callee {
            method,
            params: vec![Ty::Ref {
                mutable: false,
                ty: Box::new(operand.clone()),
            }],
            ret: Ty::BOOLEAN,
            packs_varargs: false,
            subst: self.tcx.subst_for(equatable, std::slice::from_ref(operand)),
        }))
    }

    fn lower_lambda(
        &mut self,
        moves: bool,
        params: &[LambdaParam],
        body: &LambdaBody,
        ty: &Ty,
    ) -> ExprKind {
        let first_inner = LocalId(self.locals.len() as u32);
        let params: Vec<LocalId> = params
            .iter()
            .map(|param| self.declare(param.name.name, param.name.span))
            .collect();
        let ret = self.tcx.fn_sig(ty).map_or(Ty::Unknown, |sig| sig.ret);
        self.rets.push(ret.clone());
        let body = match body {
            LambdaBody::Expr(expr) => ClosureBody::Expr(coerce(self.lower_expr(expr), &ret)),
            LambdaBody::Block(block) => ClosureBody::Block(self.lower_block(block)),
        };
        self.rets.pop();
        let captures = captures(&body, first_inner);
        ExprKind::Closure(Box::new(Closure {
            kind: ClosureKind::Lambda {
                moves,
                params,
                ret,
                body,
            },
            captures,
        }))
    }

    fn lower_method_ref(&mut self, target: &ast::Expr, name: Ident) -> ExprKind {
        let callee = self.callee(name.span);
        let receiver = callee.as_ref().and_then(|callee| callee.method.receiver);
        let bound = match receiver {
            Some(kind) if !self.is_type_name(target) => {
                Some(Box::new(auto_ref(self.lower_expr(target), kind)))
            }
            _ => None,
        };
        let captures = bound.as_deref().map_or_else(Vec::new, |bound| {
            expr_captures(bound, LocalId(self.locals.len() as u32))
        });
        ExprKind::Closure(Box::new(Closure {
            kind: ClosureKind::MethodRef {
                callee,
                bound,
                constructs: name.name == kw::New,
            },
            captures,
        }))
    }

    fn local_expr(&self, local: LocalId, span: Span) -> Expr {
        Expr {
            kind: ExprKind::Local(local),
            ty: self.locals[local.index()].ty.clone(),
            span,
        }
    }

    fn lower_args(&mut self, callee: &Callee, args: &[ast::Expr]) -> Vec<Expr> {
        let fixed = if callee.packs_varargs {
            callee.params.len().saturating_sub(1)
        } else {
            callee.params.len()
        };
        let mut lowered: Vec<Expr> = args
            .iter()
            .enumerate()
            .map(|(index, arg)| {
                let arg = self.lower_expr(arg);
                match callee.params.get(index) {
                    Some(param) if index < fixed => coerce(arg, param),
                    _ => arg,
                }
            })
            .collect();
        if !callee.packs_varargs {
            return lowered;
        }
        let elem = match callee.params.last() {
            Some(Ty::Array(elem)) => elem.as_ref().clone(),
            _ => Ty::Unknown,
        };
        let rest: Vec<Expr> = lowered
            .split_off(fixed.min(lowered.len()))
            .into_iter()
            .map(|arg| coerce(arg, &elem))
            .collect();
        let span = match (rest.first(), rest.last()) {
            (Some(first), Some(last)) => first.span.to(last.span),
            _ => lowered
                .last()
                .map_or(Span::DUMMY, |arg| arg.span.shrink_to_hi()),
        };
        lowered.push(Expr {
            kind: ExprKind::Array { elems: rest },
            ty: callee.params.last().cloned().unwrap_or(Ty::Unknown),
            span,
        });
        lowered
    }
}

fn coerce(expr: Expr, target: &Ty) -> Expr {
    // A value passed as `(&T)?` is lent the same way as one passed as `&T`.
    if let Ty::Nullable(reference) = target
        && matches!(reference.as_ref(), Ty::Ref { mutable: false, .. })
        && !matches!(
            expr.ty,
            Ty::Ref { .. } | Ty::Nullable(_) | Ty::Null | Ty::Unknown
        )
    {
        let lent = coerce(expr, reference);
        return Expr {
            ty: target.clone(),
            span: lent.span,
            kind: ExprKind::Cast {
                expr: Box::new(lent),
            },
        };
    }
    if let (Ty::Nullable(reference), Ty::Nullable(value)) = (target, &expr.ty)
        && let Ty::Ref {
            mutable: false,
            ty: wanted,
        } = reference.as_ref()
        && !matches!(value.as_ref(), Ty::Ref { .. })
        && value.as_ref() == wanted.as_ref()
    {
        let slot = expr.ty.clone();
        let lent = Expr {
            ty: Ty::Ref {
                mutable: false,
                ty: Box::new(slot),
            },
            span: expr.span,
            kind: ExprKind::Borrow {
                mutable: false,
                expr: Box::new(expr),
            },
        };
        return Expr {
            ty: target.clone(),
            span: lent.span,
            kind: ExprKind::Cast {
                expr: Box::new(lent),
            },
        };
    }
    if let Ty::Ref {
        mutable: false,
        ty: inner,
    } = target
    {
        // `&int` passed as `&&int` is lent too: the outer reference points
        // at a temporary holding the inner one.
        let lends =
            !matches!(expr.ty, Ty::Null | Ty::Unknown) && ref_depth(&expr.ty) < ref_depth(target);
        if lends && !inner.is_unknown() {
            let value = coerce(expr, inner);
            return Expr {
                ty: target.clone(),
                span: value.span,
                kind: ExprKind::Borrow {
                    mutable: false,
                    expr: Box::new(value),
                },
            };
        }
    }
    let expr = copy_through_ref(expr, target);
    let converts = match (&expr.ty, target) {
        (Ty::Primitive(from), Ty::Primitive(to)) => from != to,
        (Ty::Primitive(from), Ty::Nullable(to)) => **to != Ty::Primitive(*from),
        (Ty::Primitive(_), Ty::Adt { .. }) => true,
        _ => false,
    };
    if !converts {
        return expr;
    }
    Expr {
        ty: target.clone(),
        span: expr.span,
        kind: ExprKind::Cast {
            expr: Box::new(expr),
        },
    }
}

fn ref_depth(mut ty: &Ty) -> usize {
    let mut depth = 0;
    while let Ty::Ref { ty: inner, .. } = ty {
        depth += 1;
        ty = inner;
    }
    depth
}

fn deref_all(mut expr: Expr) -> Expr {
    while let Ty::Ref { ty, .. } = &expr.ty {
        let inner = ty.as_ref().clone();
        expr = Expr {
            ty: inner,
            span: expr.span,
            kind: ExprKind::Deref {
                expr: Box::new(expr),
                safe: false,
            },
        };
    }
    expr
}

fn copy_through_ref(mut expr: Expr, target: &Ty) -> Expr {
    let is_ref = |ty: &Ty| matches!(ty, Ty::Ref { .. });
    if matches!(target, Ty::Ref { mutable: false, .. }) {
        while ref_depth(&expr.ty) > ref_depth(target) {
            let Ty::Ref { ty, .. } = &expr.ty else {
                break;
            };
            let inner = ty.as_ref().clone();
            expr = Expr {
                ty: inner,
                span: expr.span,
                kind: ExprKind::Deref {
                    expr: Box::new(expr),
                    safe: false,
                },
            };
        }
        return expr;
    }
    let (inner, safe) = match (&expr.ty, target) {
        // A value is wanted, so read through every level: `&&int` to `int`.
        (Ty::Ref { .. }, target) if !is_ref(target.non_null()) && !target.is_unknown() => {
            return deref_all(expr);
        }
        (Ty::Nullable(nullable), Ty::Nullable(target)) if !is_ref(target) => {
            match nullable.as_ref() {
                Ty::Ref { ty, .. } => (ty.as_ref().clone().nullable(), true),
                _ => return expr,
            }
        }
        _ => return expr,
    };
    Expr {
        ty: inner,
        span: expr.span,
        kind: ExprKind::Deref {
            expr: Box::new(expr),
            safe,
        },
    }
}

fn promote_operands(lhs: Expr, rhs: Expr) -> (Expr, Expr) {
    let target = match (lhs.ty.strip_refs(), rhs.ty.strip_refs()) {
        (Ty::Primitive(a), Ty::Primitive(b)) => promote(*a, *b),
        _ => None,
    };
    match target {
        Some(target) => (coerce(lhs, &target), coerce(rhs, &target)),
        None => (lhs, rhs),
    }
}

fn auto_ref(expr: Expr, receiver: ReceiverKind) -> Expr {
    let mutable = match receiver {
        ReceiverKind::Owned => return expr,
        ReceiverKind::Ref => false,
        ReceiverKind::RefMut => true,
    };
    if let Ty::Ref { .. } = expr.ty {
        return expr;
    }
    Expr {
        ty: Ty::Ref {
            mutable,
            ty: Box::new(expr.ty.clone()),
        },
        span: expr.span,
        kind: ExprKind::Borrow {
            mutable,
            expr: Box::new(expr),
        },
    }
}
