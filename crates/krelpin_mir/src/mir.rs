use std::fmt;

use krelpin_ast::ast::{BinOp, PrimitiveTy};
use krelpin_ast::token::Lit;
use krelpin_hir::Dispatch;
use krelpin_span::def_id::DefId;
use krelpin_span::{Span, Symbol};
use krelpin_typeck::{Callee, Storage, Ty};

#[derive(Debug, Default)]
pub struct Mir {
    pub bodies: Vec<Body>,
}

impl Mir {
    pub fn body(&self, id: BodyId) -> &Body {
        &self.bodies[id.index()]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BodyId(pub u32);

impl BodyId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BodySource {
    Method,
    Constructor,
    FieldInit,
    Closure { parent: BodyId, index: usize },
}

#[derive(Debug)]
pub struct Body {
    pub owner: DefId,
    pub member: Option<u32>,
    pub name: Symbol,
    pub source: BodySource,
    pub locals: Vec<LocalDecl>,
    pub arg_count: usize,
    pub ret_sources: Option<Vec<ReturnSource>>,
    pub arg_storage: Vec<Storage>,
    pub captures: Vec<CaptureInfo>,
    pub blocks: Vec<BasicBlockData>,
    /// Set when this is the body of an `async` method. The body is then
    /// the `poll` of the method's future: it returns `Poll<output>`, and
    /// `Suspend` leaves it until the next poll.
    pub asyncness: Option<AsyncBody>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct AsyncBody {
    /// The `&mut Context` the future is polled with. It is the local right
    /// after the arguments, and isn't one of them.
    pub cx: Local,
    pub output: Ty,
}

impl Body {
    pub fn local(&self, local: Local) -> &LocalDecl {
        &self.locals[local.index()]
    }

    pub fn block(&self, block: BasicBlock) -> &BasicBlockData {
        &self.blocks[block.index()]
    }

    pub fn args(&self) -> impl Iterator<Item = Local> {
        (1..=self.arg_count).map(|index| Local(index as u32))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReturnSource {
    Whole(Local),
    Contents(Local, Symbol),
}

#[derive(Clone, Debug)]
pub struct CaptureInfo {
    pub name: Symbol,
    pub ty: Ty,
    pub mode: CaptureMode,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CaptureMode {
    Value,
    Ref,
    RefMut,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Local(pub u32);

impl fmt::Debug for Local {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}", self.0)
    }
}

impl Local {
    pub const RETURN: Local = Local(0);

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Debug)]
pub struct LocalDecl {
    pub name: Option<Symbol>,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BasicBlock(pub u32);

impl fmt::Debug for BasicBlock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bb{}", self.0)
    }
}

impl BasicBlock {
    pub const START: BasicBlock = BasicBlock(0);

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug)]
pub struct BasicBlockData {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

#[derive(Debug)]
pub struct Statement {
    pub kind: StatementKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum StatementKind {
    Assign(Box<(Place, Rvalue)>),
    StorageLive(Local),
    StorageDead(Local),
    FakeRead(Place),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Place {
    pub base: PlaceBase,
    pub projection: Vec<PlaceElem>,
}

impl Place {
    pub fn local(local: Local) -> Place {
        Place {
            base: PlaceBase::Local(local),
            projection: Vec::new(),
        }
    }

    pub fn project(mut self, elem: PlaceElem) -> Place {
        self.projection.push(elem);
        self
    }

    pub fn as_local(&self) -> Option<Local> {
        match self.base {
            PlaceBase::Local(local) if self.projection.is_empty() => Some(local),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlaceBase {
    Local(Local),
    Static { owner: DefId, name: Symbol },
}

#[derive(Clone, Debug, PartialEq)]
pub enum PlaceElem {
    Deref,
    Field { owner: DefId, name: Symbol },
    Index(Local),
    Variant { def: DefId, index: usize },
    Subtype(Ty),
    Capture(usize),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Constant),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Constant {
    Lit(Lit),
    Int { value: i64, ty: PrimitiveTy },
    Bool(bool),
    Null,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
    BitNot,
}

#[derive(Debug)]
pub enum Rvalue {
    Use(Operand),
    Ref { mutable: bool, place: Place },
    Binary(BinOp, Operand, Operand),
    Unary(UnaryOp, Operand),
    Cast(Operand, Ty),
    Len(Place),
    Discriminant(Place),
    InstanceOf(Place, Ty),
    IsNull(Place),
    New(Ty),
    NewArray { elem: Ty, len: Operand },
    Aggregate(Box<AggregateKind>, Vec<Operand>),
    Caught,
}

#[derive(Debug)]
pub enum AggregateKind {
    Array(Ty),
    Record { def: DefId, ty: Ty },
    Variant { def: DefId, index: usize, ty: Ty },
    Closure(ClosureTarget),
}

#[derive(Debug)]
pub enum ClosureTarget {
    Lambda(BodyId),
    MethodRef {
        callee: Option<Box<Callee>>,
        constructs: bool,
    },
}

#[derive(Debug)]
pub struct Terminator {
    pub kind: TerminatorKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Unwind {
    Resume,
    Handler(BasicBlock),
}

#[derive(Debug)]
pub enum Check {
    Bounds { index: Operand, len: Operand },
    NonZero(Operand),
    InstanceOf { place: Place, ty: Ty },
}

#[derive(Debug)]
pub enum TerminatorKind {
    Goto {
        target: BasicBlock,
    },
    SwitchInt {
        discr: Operand,
        targets: Vec<(u64, BasicBlock)>,
        otherwise: BasicBlock,
    },
    Return,
    Unreachable,
    /// Returns `Poll.Pending` (already in the return place) from the poll
    /// of an `async` body, keeping every local. The next poll continues at
    /// `resume`.
    Suspend {
        resume: BasicBlock,
    },
    Call {
        callee: Box<Callee>,
        dispatch: Dispatch,
        args: Vec<Operand>,
        dest: Option<Place>,
        target: BasicBlock,
        unwind: Unwind,
    },
    Throw {
        value: Operand,
        unwind: Unwind,
    },
    Assert {
        check: Check,
        target: BasicBlock,
        unwind: Unwind,
    },
}

impl TerminatorKind {
    pub fn successors(&self) -> Vec<BasicBlock> {
        let unwind = |unwind: &Unwind| match unwind {
            Unwind::Resume => None,
            Unwind::Handler(block) => Some(*block),
        };
        match self {
            TerminatorKind::Goto { target } | TerminatorKind::Suspend { resume: target } => {
                vec![*target]
            }
            TerminatorKind::SwitchInt {
                targets, otherwise, ..
            } => targets
                .iter()
                .map(|(_, target)| *target)
                .chain([*otherwise])
                .collect(),
            TerminatorKind::Return | TerminatorKind::Unreachable => Vec::new(),
            TerminatorKind::Call {
                target,
                unwind: on_unwind,
                ..
            }
            | TerminatorKind::Assert {
                target,
                unwind: on_unwind,
                ..
            } => std::iter::once(*target).chain(unwind(on_unwind)).collect(),
            TerminatorKind::Throw {
                unwind: on_unwind, ..
            } => unwind(on_unwind).into_iter().collect(),
        }
    }

    pub(crate) fn successors_mut(&mut self) -> Vec<&mut BasicBlock> {
        fn unwind(unwind: &mut Unwind) -> Option<&mut BasicBlock> {
            match unwind {
                Unwind::Resume => None,
                Unwind::Handler(block) => Some(block),
            }
        }
        match self {
            TerminatorKind::Goto { target } | TerminatorKind::Suspend { resume: target } => {
                vec![target]
            }
            TerminatorKind::SwitchInt {
                targets, otherwise, ..
            } => targets
                .iter_mut()
                .map(|(_, target)| target)
                .chain([otherwise])
                .collect(),
            TerminatorKind::Return | TerminatorKind::Unreachable => Vec::new(),
            TerminatorKind::Call {
                target,
                unwind: on_unwind,
                ..
            }
            | TerminatorKind::Assert {
                target,
                unwind: on_unwind,
                ..
            } => std::iter::once(target).chain(unwind(on_unwind)).collect(),
            TerminatorKind::Throw {
                unwind: on_unwind, ..
            } => unwind(on_unwind).into_iter().collect(),
        }
    }
}
