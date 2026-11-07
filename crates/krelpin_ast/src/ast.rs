use std::fmt;
use std::sync::Arc;

use krelpin_span::{Span, Symbol, kw};

use crate::token::{Lit, Token};

mod display;

#[cfg(test)]
mod tests;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Ident {
    pub name: Symbol,
    pub span: Span,
}

impl Ident {
    pub fn new(name: Symbol, span: Span) -> Ident {
        Ident { name, span }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Path {
    pub segments: Vec<Ident>,
    pub span: Span,
}

impl Path {
    pub fn new(segments: Vec<Ident>) -> Path {
        let span = match (segments.first(), segments.last()) {
            (Some(first), Some(last)) => first.span.to(last.span),
            _ => Span::DUMMY,
        };
        Path { segments, span }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompilationUnit {
    pub docs: Vec<Symbol>,
    pub package: Option<Path>,
    pub imports: Vec<Import>,
    pub items: Vec<Item>,
    pub macros: Vec<MacroDef>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MacroDef {
    pub docs: Vec<Symbol>,
    pub annotations: Vec<Annotation>,
    pub name: Ident,
    pub body: Option<MacroBody>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MacroBody {
    pub params: Vec<Param>,
    pub body: Block,
    pub span: Span,
}

#[derive(Clone, Default, PartialEq, Eq)]
pub struct CapturedTokens(Option<Arc<[Token]>>);

impl CapturedTokens {
    pub fn new(tokens: &[Token]) -> CapturedTokens {
        CapturedTokens(Some(tokens.into()))
    }

    pub fn tokens(&self) -> Option<&[Token]> {
        self.0.as_deref()
    }
}

impl fmt::Debug for CapturedTokens {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.tokens() {
            Some(tokens) => write!(f, "CapturedTokens({})", tokens.len()),
            None => f.write_str("CapturedTokens(None)"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Import {
    pub path: Path,
    pub glob: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Annotation {
    pub path: Path,
    pub args: Option<Unparsed>,
    pub span: Span,
}

impl Annotation {
    pub fn is(&self, name: &str) -> bool {
        matches!(self.path.segments.as_slice(), [segment] if segment.name.as_str() == name)
    }
}

pub fn is_intrinsic(annotations: &[Annotation]) -> bool {
    annotations
        .iter()
        .any(|annotation| annotation.is("Intrinsic"))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Visibility {
    Default,
    Public(Span),
    Protected(Span),
    Private(Span),
}

impl Visibility {
    pub fn span(self) -> Option<Span> {
        match self {
            Visibility::Default => None,
            Visibility::Public(span) | Visibility::Protected(span) | Visibility::Private(span) => {
                Some(span)
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FieldStorage {
    Instance,
    Static(Span),
}

#[derive(Clone, PartialEq, Eq)]
pub struct Item {
    pub docs: Vec<Symbol>,
    pub annotations: Vec<Annotation>,
    pub vis: Visibility,
    pub inheritance: Inheritance,
    pub name: Ident,
    pub kind: ItemKind,
    pub span: Span,
    pub tokens: CapturedTokens,
}

impl fmt::Debug for Item {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Item")
            .field("docs", &self.docs)
            .field("annotations", &self.annotations)
            .field("vis", &self.vis)
            .field("inheritance", &self.inheritance)
            .field("name", &self.name)
            .field("kind", &self.kind)
            .field("span", &self.span)
            .finish()
    }
}

impl Item {
    pub fn generics(&self) -> &Generics {
        match &self.kind {
            ItemKind::Class(class) => &class.generics,
            ItemKind::Record(record) => &record.generics,
            ItemKind::Interface(interface) => &interface.generics,
            ItemKind::Enum(def) => &def.generics,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ItemKind {
    Class(Class),
    Record(Record),
    Interface(Interface),
    Enum(Enum),
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Inheritance {
    pub abstract_kw: Option<Span>,
    pub final_kw: Option<Span>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Class {
    pub generics: Generics,
    pub extends: Option<Ty>,
    pub implements: Vec<Ty>,
    pub members: Vec<Member>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Record {
    pub generics: Generics,
    pub components: Vec<Param>,
    pub implements: Vec<Ty>,
    pub members: Vec<Member>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Interface {
    pub generics: Generics,
    pub extends: Vec<Ty>,
    pub members: Vec<Member>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Enum {
    pub generics: Generics,
    pub implements: Vec<Ty>,
    pub variants: Vec<Variant>,
    pub members: Vec<Member>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Variant {
    pub docs: Vec<Symbol>,
    pub annotations: Vec<Annotation>,
    pub name: Ident,
    pub fields: Vec<VariantField>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VariantField {
    pub ty: Ty,
    pub name: Ident,
}

#[derive(Clone, PartialEq, Eq)]
pub struct Member {
    pub docs: Vec<Symbol>,
    pub annotations: Vec<Annotation>,
    pub vis: Visibility,
    pub inheritance: Inheritance,
    pub kind: MemberKind,
    pub span: Span,
    pub tokens: CapturedTokens,
}

impl fmt::Debug for Member {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Member")
            .field("docs", &self.docs)
            .field("annotations", &self.annotations)
            .field("vis", &self.vis)
            .field("inheritance", &self.inheritance)
            .field("kind", &self.kind)
            .field("span", &self.span)
            .finish()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MemberKind {
    Field(Field),
    Constructor(Constructor),
    Method(Method),
    Type(Box<Item>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Field {
    pub storage: FieldStorage,
    pub final_kw: Option<Span>,
    pub ty: Ty,
    pub name: Ident,
    pub init: Option<Expr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constructor {
    pub compact: bool,
    pub name: Ident,
    pub params: Vec<Param>,
    pub keeps: Vec<Ident>,
    pub throws: Vec<Ty>,
    pub body: Block,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Method {
    /// The `async` keyword: calling the method returns a `Future` of its
    /// return type, and its body may `await`.
    pub asyncness: Option<Span>,
    pub generics: Generics,
    pub ret: FnRetTy,
    pub name: Ident,
    pub receiver: Option<Receiver>,
    pub params: Vec<Param>,
    pub borrows: Vec<Ident>,
    pub keeps: Vec<Ident>,
    pub throws: Vec<Ty>,
    pub where_clause: Vec<WherePredicate>,
    pub body: Option<Block>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WherePredicate {
    pub param: Ident,
    pub bounds: Vec<Ty>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FnRetTy {
    Void(Span),
    Ty(Ty),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Receiver {
    pub kind: ReceiverKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ReceiverKind {
    Owned,
    Ref,
    RefMut,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Param {
    pub final_kw: Option<Span>,
    pub ty: Ty,
    pub name: Ident,
    pub variadic: bool,
    pub span: Span,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Generics {
    pub params: Vec<GenericParam>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GenericParam {
    pub name: Ident,
    pub kind: GenericParamKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GenericParamKind {
    Type { bounds: Vec<Ty> },
    BorrowSource,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TyKind {
    Primitive(PrimitiveTy),
    Path { path: Path, args: Vec<Ty> },
    Ref { mutable: bool, ty: Box<Ty> },
    Nullable(Box<Ty>),
    Array(Box<Ty>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PrimitiveTy {
    Boolean,
    Byte,
    Short,
    Int,
    Long,
    Char,
    Float,
    Double,
}

impl PrimitiveTy {
    pub fn from_symbol(symbol: Symbol) -> Option<PrimitiveTy> {
        let primitive = match symbol {
            kw::Boolean => PrimitiveTy::Boolean,
            kw::Byte => PrimitiveTy::Byte,
            kw::Short => PrimitiveTy::Short,
            kw::Int => PrimitiveTy::Int,
            kw::Long => PrimitiveTy::Long,
            kw::Char => PrimitiveTy::Char,
            kw::Float => PrimitiveTy::Float,
            kw::Double => PrimitiveTy::Double,
            _ => return None,
        };
        Some(primitive)
    }

    pub fn name(self) -> &'static str {
        match self {
            PrimitiveTy::Boolean => "boolean",
            PrimitiveTy::Byte => "byte",
            PrimitiveTy::Short => "short",
            PrimitiveTy::Int => "int",
            PrimitiveTy::Long => "long",
            PrimitiveTy::Char => "char",
            PrimitiveTy::Float => "float",
            PrimitiveTy::Double => "double",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Unparsed {
    pub tokens: Vec<Token>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StmtKind {
    Local(Local),
    Expr(Expr),
    Block(Block),
    If {
        cond: Expr,
        then: Box<Stmt>,
        els: Option<Box<Stmt>>,
    },
    While {
        cond: Expr,
        body: Box<Stmt>,
    },
    DoWhile {
        body: Box<Stmt>,
        cond: Expr,
    },
    For {
        init: Vec<Stmt>,
        cond: Option<Expr>,
        update: Vec<Expr>,
        body: Box<Stmt>,
    },
    ForEach {
        final_kw: Option<Span>,
        ty: Ty,
        name: Ident,
        iter: Expr,
        body: Box<Stmt>,
    },
    Switch {
        scrutinee: Expr,
        arms: Vec<SwitchArm>,
    },
    Try {
        body: Block,
        catches: Vec<Catch>,
        finally: Option<Block>,
    },
    Return(Option<Expr>),
    Yield(Expr),
    Throw(Expr),
    Break,
    Continue,
    Empty,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Local {
    pub final_kw: Option<Span>,
    pub ty: Ty,
    pub name: Ident,
    pub init: Option<Expr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SwitchArm {
    pub label: CaseLabel,
    pub body: Box<Stmt>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CaseLabel {
    Default(Span),
    Case { pats: Vec<Pat>, guard: Option<Expr> },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pat {
    pub kind: PatKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PatKind {
    Wild,
    Lit(Expr),
    Path(Path),
    Ty { ty: Ty, binding: Option<Ident> },
    Variant { path: Path, fields: Vec<Pat> },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Catch {
    pub final_kw: Option<Span>,
    pub tys: Vec<Ty>,
    pub name: Ident,
    pub body: Block,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprKind {
    Lit(Lit),
    Bool(bool),
    Null,
    This,
    Super,
    Name(Ident),
    Field {
        expr: Box<Expr>,
        name: Ident,
        safe: bool,
    },
    MethodCall {
        receiver: Option<Box<Expr>>,
        name: Ident,
        args: Vec<Expr>,
        safe: bool,
    },
    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
    },
    Index {
        expr: Box<Expr>,
        index: Box<Expr>,
    },
    New {
        ty: Ty,
        args: Vec<Expr>,
    },
    NewArray {
        elem: Ty,
        len: Box<Expr>,
    },
    ArrayInit {
        ty: Option<Ty>,
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
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Ternary {
        cond: Box<Expr>,
        then: Box<Expr>,
        els: Box<Expr>,
    },
    InstanceOf {
        expr: Box<Expr>,
        pat: Box<Pat>,
    },
    Cast {
        ty: Ty,
        expr: Box<Expr>,
    },
    Await(Box<Expr>),
    Lambda {
        moves: bool,
        params: Vec<LambdaParam>,
        body: Box<LambdaBody>,
    },
    MethodRef {
        expr: Box<Expr>,
        name: Ident,
    },
    Switch {
        scrutinee: Box<Expr>,
        arms: Vec<SwitchExprArm>,
    },
    With {
        base: Box<Expr>,
        fields: Vec<FieldInit>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldInit {
    pub name: Ident,
    pub value: Expr,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SwitchExprArm {
    pub label: CaseLabel,
    pub body: SwitchExprBody,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SwitchExprBody {
    Expr(Expr),
    Block(Block),
    Throw(Expr),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
    BitNot,
    PreInc,
    PreDec,
    PostInc,
    PostDec,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Or,
    And,
    BitOr,
    BitXor,
    BitAnd,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Elvis,
    Shl,
    Shr,
    UShr,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

impl BinOp {
    pub fn as_str(self) -> &'static str {
        match self {
            BinOp::Or => "||",
            BinOp::And => "&&",
            BinOp::BitOr => "|",
            BinOp::BitXor => "^",
            BinOp::BitAnd => "&",
            BinOp::Eq => "==",
            BinOp::Ne => "!=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::Elvis => "?:",
            BinOp::Shl => "<<",
            BinOp::Shr => ">>",
            BinOp::UShr => ">>>",
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Rem => "%",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LambdaParam {
    pub ty: Option<Ty>,
    pub name: Ident,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LambdaBody {
    Expr(Expr),
    Block(Block),
}
