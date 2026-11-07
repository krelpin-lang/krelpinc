use krelpin_ast::ast::{BinOp, ReceiverKind, UnOp};
use krelpin_ast::token::Lit;
use krelpin_span::def_id::DefId;
use krelpin_span::{Span, Symbol};
use krelpin_typeck::{Callee, Storage, Ty};

#[derive(Debug, Default)]
pub struct Hir {
    pub bodies: Vec<Body>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalId(pub u32);

impl LocalId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Debug)]
pub struct LocalDecl {
    pub name: Symbol,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BodyKind {
    Method,
    Constructor,
    FieldInit,
}

#[derive(Debug)]
pub struct Body {
    pub owner: DefId,
    pub member: u32,
    pub name: Symbol,
    pub kind: BodyKind,
    pub receiver: Option<ReceiverKind>,
    pub this: Option<LocalId>,
    pub params: Vec<LocalId>,
    pub locals: Vec<LocalDecl>,
    pub ret: Ty,
    pub ret_sources: Option<Vec<ReturnSource>>,
    pub param_storage: Vec<Storage>,
    /// For an `async` method, the type its future produces: `ret`, or
    /// `Unit` when `ret` is `void`.
    pub output: Option<Ty>,
    pub value: BodyValue,
    pub span: Span,
}

impl Body {
    pub fn local(&self, id: LocalId) -> &LocalDecl {
        &self.locals[id.index()]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReturnSource {
    Whole(LocalId),
    Contents(LocalId, Symbol),
}

#[derive(Debug)]
pub enum BodyValue {
    Block(Block),
    Expr(Expr),
}

#[derive(Debug)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LoopKind {
    While,
    DoWhile,
}

#[derive(Debug)]
pub enum StmtKind {
    Let {
        local: LocalId,
        init: Option<Expr>,
    },
    Expr(Expr),
    Block(Block),
    If {
        cond: Expr,
        then: Block,
        els: Option<Block>,
    },
    Loop {
        kind: LoopKind,
        cond: Option<Expr>,
        update: Vec<Expr>,
        body: Block,
    },
    ForEach {
        local: LocalId,
        iter: Expr,
        body: Block,
    },
    Switch {
        scrutinee: Expr,
        arms: Vec<Arm>,
    },
    Try {
        body: Block,
        catches: Vec<Catch>,
        finally: Option<Block>,
    },
    Return(Option<Expr>),
    Yield(Expr),
    Throw(Expr),
    Break(Option<Symbol>),
    Continue(Option<Symbol>),
    Labeled {
        label: Symbol,
        body: Box<Stmt>,
    },
}

#[derive(Debug)]
pub struct Catch {
    pub local: LocalId,
    pub tys: Vec<Ty>,
    pub body: Block,
}

#[derive(Debug)]
pub struct Arm {
    pub pats: Vec<Pat>,
    pub guard: Option<Expr>,
    pub body: ArmBody,
    pub span: Span,
}

#[derive(Debug)]
pub enum ArmBody {
    Expr(Expr),
    Block(Block),
    Throw(Expr),
}

#[derive(Debug)]
pub struct Pat {
    pub kind: PatKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum PatKind {
    Wild,
    Lit(Expr),
    Binding {
        local: Option<LocalId>,
        ty: Ty,
    },
    Variant {
        def: DefId,
        index: usize,
        fields: Vec<Pat>,
    },
    Record {
        def: DefId,
        fields: Vec<Pat>,
    },
    Const {
        owner: DefId,
        name: Symbol,
    },
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dispatch {
    Virtual,
    Static,
}

#[derive(Debug)]
pub enum ExprKind {
    Lit(Lit),
    Bool(bool),
    Null,
    Local(LocalId),
    Field {
        base: Box<Expr>,
        owner: DefId,
        name: Symbol,
        safe: bool,
    },
    Static {
        owner: DefId,
        name: Symbol,
    },
    Call {
        callee: Box<Callee>,
        receiver: Option<Box<Expr>>,
        args: Vec<Expr>,
        dispatch: Dispatch,
        safe: bool,
    },
    New {
        callee: Option<Box<Callee>>,
        args: Vec<Expr>,
    },
    CtorCall {
        callee: Box<Callee>,
        this: Box<Expr>,
        args: Vec<Expr>,
    },
    Index {
        base: Box<Expr>,
        index: Box<Expr>,
    },
    NewArray {
        len: Box<Expr>,
    },
    Len {
        array: Box<Expr>,
    },
    Array {
        elems: Vec<Expr>,
    },
    Unary {
        op: UnOp,
        expr: Box<Expr>,
    },
    Borrow {
        mutable: bool,
        expr: Box<Expr>,
    },
    Binary {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Assign {
        op: Option<BinOp>,
        place: Box<Expr>,
        value: Box<Expr>,
    },
    If {
        cond: Box<Expr>,
        then: Box<Expr>,
        els: Box<Expr>,
    },
    Is {
        expr: Box<Expr>,
        pat: Box<Pat>,
    },
    Cast {
        expr: Box<Expr>,
    },
    /// Waits for the future `expr`; the expression's type is its value.
    Await {
        expr: Box<Expr>,
    },
    Deref {
        expr: Box<Expr>,
        safe: bool,
    },
    Switch {
        scrutinee: Box<Expr>,
        arms: Vec<Arm>,
    },
    With {
        base: Box<Expr>,
        fields: Vec<WithField>,
        /// The record's compact constructor, which checks the new copy.
        callee: Option<Box<Callee>>,
    },
    Equals {
        callee: Box<Callee>,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        negated: bool,
    },
    Closure(Box<Closure>),
    Unresolved,
}

#[derive(Debug)]
pub struct WithField {
    pub name: Symbol,
    pub value: Expr,
}

#[derive(Debug)]
pub struct Closure {
    pub kind: ClosureKind,
    pub captures: Vec<Capture>,
}

#[derive(Debug)]
pub enum ClosureKind {
    Lambda {
        moves: bool,
        params: Vec<LocalId>,
        ret: Ty,
        body: ClosureBody,
    },
    MethodRef {
        callee: Option<Box<Callee>>,
        bound: Option<Box<Expr>>,
        constructs: bool,
    },
}

#[derive(Debug)]
pub enum ClosureBody {
    Expr(Expr),
    Block(Block),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Capture {
    pub local: LocalId,
    pub mutable: bool,
}
