mod asyncness;
mod expr;
mod matches;
mod stmt;

use std::collections::{HashMap, HashSet};

use krelpin_ast::ast::ReceiverKind;
use krelpin_hir::{self as hir, BodyKind, BodyValue, ClosureBody, LocalId};
use krelpin_span::def_id::DefId;
use krelpin_span::{Span, Symbol};
use krelpin_typeck::{LangItem, Storage, Tcx, Ty};

use crate::mir::{
    AsyncBody, BasicBlock, BasicBlockData, Body, BodyId, BodySource, CaptureInfo, CaptureMode,
    Local, LocalDecl, Mir, Place, PlaceElem, ReturnSource, Rvalue, Statement, StatementKind,
    Terminator, TerminatorKind, Unwind,
};
use crate::visit::for_each_local_mut;

pub fn build(hir: &hir::Hir, tcx: &Tcx<'_>) -> Mir {
    let mut cx = MirCtxt {
        tcx,
        constructed: hir
            .bodies
            .iter()
            .filter(|body| body.kind == BodyKind::Constructor)
            .map(|body| body.owner)
            .collect(),
        bodies: Vec::new(),
    };
    for body in &hir.bodies {
        Builder::build_item(&mut cx, body);
    }
    Mir {
        bodies: cx
            .bodies
            .into_iter()
            .map(|body| body.expect("every reserved body is built"))
            .collect(),
    }
}

struct MirCtxt<'a, 'tcx> {
    tcx: &'a Tcx<'tcx>,
    constructed: HashSet<DefId>,
    bodies: Vec<Option<Body>>,
}

impl MirCtxt<'_, '_> {
    fn reserve(&mut self) -> BodyId {
        let id = BodyId(self.bodies.len() as u32);
        self.bodies.push(None);
        id
    }
}

enum Scope<'h> {
    Block {
        locals: Vec<Local>,
    },
    Loop {
        exit: BasicBlock,
        next: BasicBlock,
        label: Option<Symbol>,
    },
    Breakable {
        exit: BasicBlock,
        label: Option<Symbol>,
    },
    Try {
        finally: Option<&'h hir::Block>,
        handler: Option<BasicBlock>,
    },
    Value {
        dest: Place,
        exit: BasicBlock,
    },
}

struct BlockBuilder {
    statements: Vec<Statement>,
    terminator: Option<Terminator>,
}

struct Builder<'a, 'h, 'tcx> {
    cx: &'a mut MirCtxt<'h, 'tcx>,
    hir: &'h hir::Body,
    id: BodyId,
    ret: Ty,
    locals: Vec<LocalDecl>,
    blocks: Vec<BlockBuilder>,
    current: BasicBlock,
    vars: HashMap<LocalId, Place>,
    scopes: Vec<Scope<'h>>,
    label: Option<Symbol>,
    closures: usize,
    asyncness: Option<AsyncState>,
}

/// What building the poll of an `async` body needs.
#[derive(Clone)]
struct AsyncState {
    body: AsyncBody,
    /// `Poll<output>`, the return type.
    poll: Ty,
    /// Where `return` puts its value before wrapping it in `Poll.Ready`.
    value: Local,
}

impl<'a, 'h, 'tcx> Builder<'a, 'h, 'tcx> {
    fn new(cx: &'a mut MirCtxt<'h, 'tcx>, hir: &'h hir::Body, ret: Ty) -> Self {
        let id = cx.reserve();
        let mut builder = Builder {
            cx,
            hir,
            id,
            ret: ret.clone(),
            locals: Vec::new(),
            blocks: Vec::new(),
            current: BasicBlock::START,
            vars: HashMap::new(),
            scopes: Vec::new(),
            label: None,
            closures: 0,
            asyncness: None,
        };
        builder.push_local(None, ret, hir.span);
        builder.current = builder.new_block();
        builder
    }

    fn build_item(cx: &'a mut MirCtxt<'h, 'tcx>, body: &'h hir::Body) {
        let poll = body
            .output
            .as_ref()
            .map(|output| cx.tcx.poll_of(output.clone()));
        let ret = poll.clone().unwrap_or_else(|| body.ret.clone());
        let mut builder = Builder::new(cx, body, ret);
        for &local in body.this.iter().chain(&body.params) {
            builder.declare_arg(local);
        }
        let arg_count = builder.locals.len() - 1;
        if let (Some(output), Some(poll)) = (&body.output, poll) {
            let context = Ty::Ref {
                mutable: true,
                ty: Box::new(builder.tcx().lang_ty(LangItem::Context)),
            };
            let cx = builder.push_local(None, context, body.span);
            let value = builder.temp(output, body.span);
            builder.asyncness = Some(AsyncState {
                body: AsyncBody {
                    cx,
                    output: output.clone(),
                },
                poll,
                value,
            });
        }
        let ret_sources = body.ret_sources.as_ref().map(|sources| {
            sources
                .iter()
                .filter_map(|source| match *source {
                    hir::ReturnSource::Whole(id) => {
                        builder.var(id).as_local().map(ReturnSource::Whole)
                    }
                    hir::ReturnSource::Contents(id, name) => builder
                        .var(id)
                        .as_local()
                        .map(|local| ReturnSource::Contents(local, name)),
                })
                .collect()
        });
        match &body.value {
            BodyValue::Block(block) => builder.lower_block(block),
            BodyValue::Expr(expr) => {
                builder.expr_into(Place::local(Local::RETURN), expr);
                builder.terminate(TerminatorKind::Return, expr.span);
            }
        }
        let source = match body.kind {
            BodyKind::Method => BodySource::Method,
            BodyKind::Constructor => BodySource::Constructor,
            BodyKind::FieldInit => BodySource::FieldInit,
        };
        let arg_storage = body
            .this
            .map(|_| Storage::default())
            .into_iter()
            .chain(body.param_storage.iter().copied())
            .collect();
        builder.finish(source, arg_count, Vec::new(), ret_sources, arg_storage);
    }

    #[allow(clippy::too_many_arguments)]
    fn build_closure(
        &mut self,
        closure: &'h hir::Closure,
        captures: Vec<CaptureInfo>,
        params: &[LocalId],
        ret: &Ty,
        body: &'h ClosureBody,
        ty: &Ty,
        span: Span,
    ) -> BodyId {
        let parent = self.id;
        let env_ty = match self.tcx().fn_receiver(ty) {
            Some(ReceiverKind::Owned) => ty.clone(),
            Some(ReceiverKind::RefMut) => Ty::Ref {
                mutable: true,
                ty: Box::new(ty.clone()),
            },
            Some(ReceiverKind::Ref) | None => Ty::Ref {
                mutable: false,
                ty: Box::new(ty.clone()),
            },
        };
        let mut builder = Builder::new(self.cx, self.hir, ret.clone());
        let env = builder.push_local(None, env_ty.clone(), span);
        let env_place = expr::deref(Place::local(env), &env_ty);
        for (index, (capture, info)) in closure.captures.iter().zip(&captures).enumerate() {
            let place = env_place.clone().project(PlaceElem::Capture(index));
            let place = match info.mode {
                CaptureMode::Value => place,
                CaptureMode::Ref | CaptureMode::RefMut => place.project(PlaceElem::Deref),
            };
            builder.vars.insert(capture.local, place);
        }
        for &param in params {
            builder.declare_arg(param);
        }
        let arg_count = builder.locals.len() - 1;
        match body {
            ClosureBody::Expr(expr) => {
                builder.expr_into(Place::local(Local::RETURN), expr);
                builder.terminate(TerminatorKind::Return, expr.span);
            }
            ClosureBody::Block(block) => builder.lower_block(block),
        }
        let source = BodySource::Closure {
            parent,
            index: self.closures,
        };
        self.closures += 1;
        builder.finish(source, arg_count, captures, None, Vec::new())
    }

    fn finish(
        mut self,
        source: BodySource,
        arg_count: usize,
        captures: Vec<CaptureInfo>,
        ret_sources: Option<Vec<ReturnSource>>,
        arg_storage: Vec<Storage>,
    ) -> BodyId {
        if self.hir.ret == Ty::Void && self.asyncness.is_some() {
            self.async_return(None, self.hir.span);
        }
        let fallthrough = if self.ret == Ty::Void {
            TerminatorKind::Return
        } else {
            TerminatorKind::Unreachable
        };
        self.terminate(fallthrough, self.hir.span);
        let mut blocks = simplify(self.blocks);
        // The context of an `async` body comes right after the arguments.
        let kept = arg_count + usize::from(self.asyncness.is_some());
        let locals = remove_unused_locals(self.locals, kept, &mut blocks);
        let member = match source {
            BodySource::Closure { .. } => None,
            _ => Some(self.hir.member),
        };
        let body = Body {
            owner: self.hir.owner,
            member,
            name: self.hir.name,
            source,
            locals,
            arg_count,
            ret_sources,
            arg_storage,
            captures,
            blocks,
            asyncness: self.asyncness.map(|state| state.body),
            span: self.hir.span,
        };
        self.cx.bodies[self.id.index()] = Some(body);
        self.id
    }

    fn tcx(&self) -> &'a Tcx<'tcx> {
        self.cx.tcx
    }

    fn push_local(&mut self, name: Option<Symbol>, ty: Ty, span: Span) -> Local {
        let local = Local(self.locals.len() as u32);
        self.locals.push(LocalDecl { name, ty, span });
        local
    }

    fn temp(&mut self, ty: &Ty, span: Span) -> Local {
        self.push_local(None, ty.clone(), span)
    }

    fn declare_arg(&mut self, id: LocalId) -> Local {
        let decl = self.hir.local(id);
        let local = self.push_local(Some(decl.name), decl.ty.clone(), decl.span);
        self.vars.insert(id, Place::local(local));
        local
    }

    fn declare_var(&mut self, id: LocalId) -> Local {
        let ty = self.hir.local(id).ty.clone();
        let local = self.declare_var_as(id, ty);
        self.vars.insert(id, Place::local(local));
        local
    }

    fn declare_var_as(&mut self, id: LocalId, ty: Ty) -> Local {
        let decl = self.hir.local(id);
        let local = self.push_local(Some(decl.name), ty, decl.span);
        self.push(StatementKind::StorageLive(local), decl.span);
        let scope = self.scopes.iter_mut().rev().find_map(|scope| match scope {
            Scope::Block { locals } => Some(locals),
            _ => None,
        });
        if let Some(locals) = scope {
            locals.push(local);
        }
        local
    }

    fn bind_var(&mut self, id: LocalId, place: Place, ty: &Ty, span: Span) {
        self.bind_var_as(id, place, ty, false, span);
    }

    fn bind_var_as(&mut self, id: LocalId, place: Place, ty: &Ty, mutable: bool, span: Span) {
        if self.is_copy(ty) || is_movable(&place) {
            let local = self.declare_var(id);
            let value = self.operand_from_place(place, ty, span);
            self.assign(Place::local(local), Rvalue::Use(value), span);
            return;
        }
        let ref_ty = Ty::Ref {
            mutable,
            ty: Box::new(ty.clone()),
        };
        let local = self.declare_var_as(id, ref_ty);
        self.assign(Place::local(local), Rvalue::Ref { mutable, place }, span);
        self.vars
            .insert(id, Place::local(local).project(PlaceElem::Deref));
    }

    fn var(&self, id: LocalId) -> Place {
        self.vars
            .get(&id)
            .cloned()
            .unwrap_or_else(|| unreachable!("local {id:?} is used before it is declared"))
    }

    fn new_block(&mut self) -> BasicBlock {
        let block = BasicBlock(self.blocks.len() as u32);
        self.blocks.push(BlockBuilder {
            statements: Vec::new(),
            terminator: None,
        });
        block
    }

    fn push(&mut self, kind: StatementKind, span: Span) {
        let block = &mut self.blocks[self.current.index()];
        if block.terminator.is_none() {
            block.statements.push(Statement { kind, span });
        }
    }

    fn assign(&mut self, place: Place, rvalue: Rvalue, span: Span) {
        self.push(StatementKind::Assign(Box::new((place, rvalue))), span);
    }

    fn terminate(&mut self, kind: TerminatorKind, span: Span) {
        let block = &mut self.blocks[self.current.index()];
        if block.terminator.is_none() {
            block.terminator = Some(Terminator { kind, span });
        }
    }

    fn goto(&mut self, target: BasicBlock, span: Span) {
        self.terminate(TerminatorKind::Goto { target }, span);
    }

    fn goto_new(&mut self, span: Span) -> BasicBlock {
        let next = self.new_block();
        self.goto(next, span);
        self.current = next;
        next
    }

    fn diverge(&mut self, kind: TerminatorKind, span: Span) {
        self.terminate(kind, span);
        self.current = self.new_block();
    }

    fn unwind(&self) -> Unwind {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| match scope {
                Scope::Try {
                    handler: Some(handler),
                    ..
                } => Some(Unwind::Handler(*handler)),
                _ => None,
            })
            .unwrap_or(Unwind::Resume)
    }

    fn push_block_scope(&mut self) {
        self.scopes.push(Scope::Block { locals: Vec::new() });
    }

    fn pop_block_scope(&mut self, span: Span) {
        if let Some(Scope::Block { locals }) = self.scopes.pop() {
            for local in locals.into_iter().rev() {
                self.push(StatementKind::StorageDead(local), span);
            }
        }
    }

    fn exit_scopes(&mut self, depth: usize, span: Span) {
        let mut index = self.scopes.len();
        while index > depth {
            index -= 1;
            match &self.scopes[index] {
                Scope::Block { locals } => {
                    for local in locals.clone().into_iter().rev() {
                        self.push(StatementKind::StorageDead(local), span);
                    }
                }
                Scope::Try {
                    finally: Some(finally),
                    ..
                } => {
                    let finally = *finally;
                    let saved = self.scopes.split_off(index);
                    self.lower_block(finally);
                    self.scopes.extend(saved);
                }
                Scope::Loop { .. }
                | Scope::Breakable { .. }
                | Scope::Try { finally: None, .. }
                | Scope::Value { .. } => {}
            }
        }
    }

    fn is_copy(&self, ty: &Ty) -> bool {
        self.tcx().is_copy(ty)
    }
}

fn simplify(blocks: Vec<BlockBuilder>) -> Vec<BasicBlockData> {
    let mut blocks: Vec<BasicBlockData> = blocks
        .into_iter()
        .map(|block| BasicBlockData {
            statements: block.statements,
            terminator: block.terminator.unwrap_or(Terminator {
                kind: TerminatorKind::Unreachable,
                span: Span::DUMMY,
            }),
        })
        .collect();

    let forwards: Vec<BasicBlock> = (0..blocks.len())
        .map(|index| skip_empty_gotos(&blocks, BasicBlock(index as u32)))
        .collect();
    for block in &mut blocks {
        for target in block.terminator.kind.successors_mut() {
            *target = forwards[target.index()];
        }
    }

    let mut reachable = vec![false; blocks.len()];
    let mut stack = vec![BasicBlock::START];
    while let Some(block) = stack.pop() {
        if std::mem::replace(&mut reachable[block.index()], true) {
            continue;
        }
        stack.extend(blocks[block.index()].terminator.kind.successors());
    }

    let mut renumbered = vec![None; blocks.len()];
    let mut next = 0;
    for (index, live) in reachable.iter().enumerate() {
        if *live {
            renumbered[index] = Some(BasicBlock(next));
            next += 1;
        }
    }
    let mut kept = Vec::with_capacity(next as usize);
    for (index, mut block) in blocks.drain(..).enumerate() {
        if !reachable[index] {
            continue;
        }
        for target in block.terminator.kind.successors_mut() {
            *target = renumbered[target.index()].expect("successors of live blocks are live");
        }
        kept.push(block);
    }
    kept
}

fn skip_empty_gotos(blocks: &[BasicBlockData], mut block: BasicBlock) -> BasicBlock {
    for _ in 0..blocks.len() {
        let data = &blocks[block.index()];
        match data.terminator.kind {
            TerminatorKind::Goto { target } if data.statements.is_empty() && target != block => {
                block = target;
            }
            _ => break,
        }
    }
    block
}

fn remove_unused_locals(
    locals: Vec<LocalDecl>,
    arg_count: usize,
    blocks: &mut [BasicBlockData],
) -> Vec<LocalDecl> {
    let mut used = vec![false; locals.len()];
    for flag in used.iter_mut().take(arg_count + 1) {
        *flag = true;
    }
    for_each_local_mut(blocks, &mut |local| used[local.index()] = true);

    let mut renumbered = vec![None; locals.len()];
    let mut kept = Vec::with_capacity(locals.len());
    for (index, decl) in locals.into_iter().enumerate() {
        if used[index] {
            renumbered[index] = Some(Local(kept.len() as u32));
            kept.push(decl);
        }
    }
    for_each_local_mut(blocks, &mut |local| {
        *local = renumbered[local.index()].expect("every mentioned local is kept");
    });
    kept
}

fn is_movable(place: &Place) -> bool {
    matches!(place.base, crate::mir::PlaceBase::Local(_))
        && place
            .projection
            .iter()
            .all(|elem| !matches!(elem, PlaceElem::Deref | PlaceElem::Index(_)))
}
