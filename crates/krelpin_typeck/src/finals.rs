use std::collections::{HashMap, HashSet};

use krelpin_ast::ast::{
    BinOp, Block, CaseLabel, Expr, ExprKind, FieldStorage, Item, ItemKind, LambdaBody, Member,
    MemberKind, Param, Stmt, StmtKind, SwitchExprBody, UnOp,
};
use krelpin_errors::Diagnostic;
use krelpin_resolve::Res;
use krelpin_span::{Span, Symbol};

use crate::sig::Tcx;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Target {
    Field(Symbol),
    Local(Span),
}

#[derive(Clone, Copy)]
enum Origin {
    Declared,
    Blank,
    Delegated,
}

struct Var {
    name: Symbol,
    decl: Span,
    origin: Origin,
    loop_depth: usize,
    lambda_depth: usize,
}

#[derive(Clone)]
struct Flow {
    live: bool,
    maybe: HashSet<Target>,
    definite: HashSet<Target>,
}

impl Flow {
    fn start() -> Flow {
        Flow {
            live: true,
            maybe: HashSet::new(),
            definite: HashSet::new(),
        }
    }

    fn dead() -> Flow {
        Flow {
            live: false,
            ..Flow::start()
        }
    }

    fn join(self, other: Flow) -> Flow {
        match (self.live, other.live) {
            (false, _) => other,
            (_, false) => self,
            _ => Flow {
                live: true,
                maybe: self.maybe.union(&other.maybe).copied().collect(),
                definite: self
                    .definite
                    .intersection(&other.definite)
                    .copied()
                    .collect(),
            },
        }
    }

    fn assign(&mut self, target: Target) {
        self.maybe.insert(target);
        self.definite.insert(target);
    }

    fn after_attempt(&self, touched: &[Target]) -> Flow {
        let mut flow = self.clone();
        flow.live = true;
        flow.maybe.extend(touched.iter().copied());
        flow
    }
}

struct Ctor {
    name: Span,
    fields: Vec<Target>,
}

struct Checker<'a, 'tcx> {
    tcx: &'a Tcx<'tcx>,
    vars: HashMap<Target, Var>,
    flow: Flow,
    loop_depth: usize,
    lambda_depth: usize,
    breaks: Vec<(Option<Symbol>, Vec<Flow>)>,
    label: Option<Symbol>,
    yields: Vec<Vec<Flow>>,
    touched: Vec<Target>,
    ctor: Option<Ctor>,
    missing: HashSet<Target>,
}

impl Tcx<'_> {
    pub(crate) fn check_finals(&self, item: &Item, member: &Member) {
        let mut checker = Checker {
            tcx: self,
            vars: HashMap::new(),
            flow: Flow::start(),
            loop_depth: 0,
            lambda_depth: 0,
            breaks: Vec::new(),
            label: None,
            yields: Vec::new(),
            touched: Vec::new(),
            ctor: None,
            missing: HashSet::new(),
        };
        match &member.kind {
            MemberKind::Constructor(ctor) => {
                checker.params(&ctor.params);
                if let ItemKind::Class(class) = &item.kind
                    && !ctor.compact
                {
                    let delegates = crate::init::delegates(&ctor.body);
                    let mut fields = Vec::new();
                    for member in &class.members {
                        let MemberKind::Field(field) = &member.kind else {
                            continue;
                        };
                        if field.final_kw.is_none()
                            || !matches!(field.storage, FieldStorage::Instance)
                        {
                            continue;
                        }
                        let target = Target::Field(field.name.name);
                        let origin = if field.init.is_some() {
                            Origin::Declared
                        } else if delegates {
                            Origin::Delegated
                        } else {
                            fields.push(target);
                            Origin::Blank
                        };
                        if !matches!(origin, Origin::Blank) {
                            checker.flow.assign(target);
                        }
                        checker.declare(target, field.name.name, field.name.span, origin);
                    }
                    checker.ctor = Some(Ctor {
                        name: ctor.name.span,
                        fields,
                    });
                }
                checker.block(&ctor.body);
                checker.leave_ctor();
            }
            MemberKind::Method(method) => {
                checker.params(&method.params);
                if let Some(body) = &method.body {
                    checker.block(body);
                }
            }
            MemberKind::Field(field) => {
                if let Some(init) = &field.init {
                    checker.expr(init);
                }
            }
            MemberKind::Type(_) => {}
        }
    }
}

impl Checker<'_, '_> {
    fn declare(&mut self, target: Target, name: Symbol, decl: Span, origin: Origin) {
        self.vars.insert(
            target,
            Var {
                name,
                decl,
                origin,
                loop_depth: self.loop_depth,
                lambda_depth: self.lambda_depth,
            },
        );
    }

    fn declare_local(&mut self, final_kw: Option<Span>, name: Symbol, decl: Span, init: bool) {
        if final_kw.is_none() {
            return;
        }
        let target = Target::Local(decl);
        let origin = if init {
            self.flow.assign(target);
            Origin::Declared
        } else {
            Origin::Blank
        };
        self.declare(target, name, decl, origin);
    }

    fn params(&mut self, params: &[Param]) {
        for param in params {
            self.declare_local(param.final_kw, param.name.name, param.name.span, true);
        }
    }

    fn block(&mut self, block: &Block) {
        for stmt in &block.stmts {
            self.stmt(stmt);
        }
    }

    fn branch(&mut self, entry: &Flow, run: impl FnOnce(&mut Self)) -> Flow {
        self.flow = entry.clone();
        run(self);
        std::mem::replace(&mut self.flow, entry.clone())
    }

    fn looped(&mut self, label: Option<Symbol>, run: impl FnOnce(&mut Self)) -> Vec<Flow> {
        self.loop_depth += 1;
        self.breaks.push((label, Vec::new()));
        run(self);
        self.loop_depth -= 1;
        self.breaks
            .pop()
            .map(|(_, flows)| flows)
            .unwrap_or_default()
    }

    fn stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Local(local) => {
                if let Some(init) = &local.init {
                    self.expr(init);
                }
                self.declare_local(
                    local.final_kw,
                    local.name.name,
                    local.name.span,
                    local.init.is_some(),
                );
            }
            StmtKind::Expr(expr) => self.expr(expr),
            StmtKind::Block(block) => self.block(block),
            StmtKind::If { cond, then, els } => {
                self.expr(cond);
                let entry = self.flow.clone();
                let then = self.branch(&entry, |this| this.stmt(then));
                let els = match els {
                    Some(els) => self.branch(&entry, |this| this.stmt(els)),
                    None => entry,
                };
                self.flow = then.join(els);
            }
            StmtKind::While { cond, body } => {
                let label = self.label.take();
                self.expr(cond);
                let entry = self.flow.clone();
                let breaks = self.looped(label, |this| this.stmt(body));
                let exit = if is_true(cond) { Flow::dead() } else { entry };
                self.flow = breaks.into_iter().fold(exit, Flow::join);
            }
            StmtKind::DoWhile { body, cond } => {
                let label = self.label.take();
                let breaks = self.looped(label, |this| {
                    this.stmt(body);
                    this.expr(cond);
                });
                let exit = if is_true(cond) {
                    Flow::dead()
                } else {
                    self.flow.clone()
                };
                self.flow = breaks.into_iter().fold(exit, Flow::join);
            }
            StmtKind::For {
                init,
                cond,
                update,
                body,
            } => {
                let label = self.label.take();
                for stmt in init {
                    self.stmt(stmt);
                }
                if let Some(cond) = cond {
                    self.expr(cond);
                }
                let entry = self.flow.clone();
                let breaks = self.looped(label, |this| {
                    this.stmt(body);
                    for expr in update {
                        this.expr(expr);
                    }
                });
                let exit = if cond.as_ref().is_none_or(is_true) {
                    Flow::dead()
                } else {
                    entry
                };
                self.flow = breaks.into_iter().fold(exit, Flow::join);
            }
            StmtKind::ForEach {
                final_kw,
                name,
                iter,
                body,
                ..
            } => {
                let label = self.label.take();
                self.expr(iter);
                let entry = self.flow.clone();
                let breaks = self.looped(label, |this| {
                    this.declare_local(*final_kw, name.name, name.span, true);
                    this.stmt(body);
                });
                self.flow = breaks.into_iter().fold(entry, Flow::join);
            }
            StmtKind::Switch { scrutinee, arms } => {
                let label = self.label.take();
                self.expr(scrutinee);
                let entry = self.flow.clone();
                self.breaks.push((label, Vec::new()));
                let mut exit = if arms
                    .iter()
                    .any(|arm| matches!(arm.label, CaseLabel::Default(_)))
                {
                    Flow::dead()
                } else {
                    entry.clone()
                };
                for arm in arms {
                    let flow = self.branch(&entry, |this| {
                        this.label(&arm.label);
                        this.stmt(&arm.body);
                    });
                    exit = exit.join(flow);
                }
                let breaks = self
                    .breaks
                    .pop()
                    .map(|(_, flows)| flows)
                    .unwrap_or_default();
                self.flow = breaks.into_iter().fold(exit, Flow::join);
            }
            StmtKind::Try {
                body,
                catches,
                finally,
            } => {
                let entry = self.flow.clone();
                let mark = self.touched.len();
                self.block(body);
                let attempt = entry.after_attempt(&self.touched[mark..]);
                let mut exit = self.flow.clone();
                for catch in catches {
                    let flow = self.branch(&attempt, |this| {
                        this.declare_local(catch.final_kw, catch.name.name, catch.name.span, true);
                        this.block(&catch.body);
                    });
                    exit = exit.join(flow);
                }
                self.flow = exit;
                if let Some(finally) = finally {
                    let normal = std::mem::replace(
                        &mut self.flow,
                        entry.after_attempt(&self.touched[mark..]),
                    );
                    let before = self.flow.definite.clone();
                    self.block(finally);
                    if !self.flow.live || !normal.live {
                        self.flow = Flow::dead();
                    } else {
                        let mut flow = normal;
                        flow.maybe.extend(self.flow.maybe.iter().copied());
                        flow.definite
                            .extend(self.flow.definite.difference(&before).copied());
                        self.flow = flow;
                    }
                }
            }
            StmtKind::Return(value) => {
                if let Some(value) = value {
                    self.expr(value);
                }
                self.check_fields(Some(stmt.span));
                self.flow = Flow::dead();
            }
            StmtKind::Yield(value) => {
                self.expr(value);
                let flow = std::mem::replace(&mut self.flow, Flow::dead());
                if let Some(yields) = self.yields.last_mut() {
                    yields.push(flow);
                }
            }
            StmtKind::Throw(value) => {
                self.expr(value);
                self.flow = Flow::dead();
            }
            StmtKind::Break(label) => {
                let flow = std::mem::replace(&mut self.flow, Flow::dead());
                let target = match label {
                    Some(label) => self
                        .breaks
                        .iter_mut()
                        .rev()
                        .find(|(name, _)| *name == Some(label.name)),
                    None => self.breaks.last_mut(),
                };
                if let Some((_, breaks)) = target {
                    breaks.push(flow);
                }
            }
            StmtKind::Continue(_) => self.flow = Flow::dead(),
            StmtKind::Labeled { label, body } => {
                self.label = Some(label.name);
                self.stmt(body);
                self.label = None;
            }
            StmtKind::Empty => {}
        }
    }

    fn label(&mut self, label: &CaseLabel) {
        if let CaseLabel::Case {
            guard: Some(guard), ..
        } = label
        {
            self.expr(guard);
        }
    }

    fn expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Lit(_)
            | ExprKind::Bool(_)
            | ExprKind::Null
            | ExprKind::This
            | ExprKind::Super
            | ExprKind::Name(_) => {}
            ExprKind::Field { expr, .. }
            | ExprKind::Borrow { expr, .. }
            | ExprKind::Cast { expr, .. }
            | ExprKind::Await(expr)
            | ExprKind::MethodRef { expr, .. }
            | ExprKind::InstanceOf { expr, .. } => self.expr(expr),
            ExprKind::NewArray { len, .. } => self.expr(len),
            ExprKind::MethodCall { receiver, args, .. } => {
                if let Some(receiver) = receiver {
                    self.expr(receiver);
                }
                self.exprs(args);
            }
            ExprKind::Call { callee, args } => {
                self.expr(callee);
                self.exprs(args);
            }
            ExprKind::Index { expr, index } => {
                self.expr(expr);
                self.expr(index);
            }
            ExprKind::New { args, .. } => self.exprs(args),
            ExprKind::ArrayInit { elems, .. } => self.exprs(elems),
            ExprKind::Unary { op, expr: operand } => {
                if matches!(
                    op,
                    UnOp::PreInc | UnOp::PreDec | UnOp::PostInc | UnOp::PostDec
                ) {
                    self.place_parts(operand);
                    self.assign(operand);
                } else {
                    self.expr(operand);
                }
            }
            ExprKind::Binary { op, lhs, rhs } => {
                self.expr(lhs);
                if matches!(op, BinOp::And | BinOp::Or | BinOp::Elvis) {
                    let entry = self.flow.clone();
                    self.expr(rhs);
                    self.flow = std::mem::replace(&mut self.flow, Flow::dead()).join(entry);
                } else {
                    self.expr(rhs);
                }
            }
            ExprKind::Assign { lhs, rhs, .. } => {
                self.place_parts(lhs);
                self.expr(rhs);
                self.assign(lhs);
            }
            ExprKind::Ternary { cond, then, els } => {
                self.expr(cond);
                let entry = self.flow.clone();
                let then = self.branch(&entry, |this| this.expr(then));
                let els = self.branch(&entry, |this| this.expr(els));
                self.flow = then.join(els);
            }
            ExprKind::Lambda { body, .. } => {
                let entry = self.flow.clone();
                let breaks = std::mem::take(&mut self.breaks);
                let yields = std::mem::take(&mut self.yields);
                let ctor = self.ctor.take();
                self.lambda_depth += 1;
                match body.as_ref() {
                    LambdaBody::Expr(body) => self.expr(body),
                    LambdaBody::Block(body) => self.block(body),
                }
                self.lambda_depth -= 1;
                self.ctor = ctor;
                self.yields = yields;
                self.breaks = breaks;
                self.flow = entry;
            }
            ExprKind::Switch { scrutinee, arms } => {
                self.expr(scrutinee);
                let entry = self.flow.clone();
                let mut exit = Flow::dead();
                for arm in arms {
                    let flow = self.branch(&entry, |this| {
                        this.label(&arm.label);
                        match &arm.body {
                            SwitchExprBody::Expr(value) => this.expr(value),
                            SwitchExprBody::Block(block) => {
                                this.yields.push(Vec::new());
                                this.block(block);
                                let yields = this.yields.pop().unwrap_or_default();
                                let end = std::mem::replace(&mut this.flow, Flow::dead());
                                this.flow = yields.into_iter().fold(end, Flow::join);
                            }
                            SwitchExprBody::Throw(value) => {
                                this.expr(value);
                                this.flow = Flow::dead();
                            }
                        }
                    });
                    exit = exit.join(flow);
                }
                self.flow = exit;
            }
            ExprKind::With { base, fields } => {
                self.expr(base);
                for field in fields {
                    self.expr(&field.value);
                }
            }
        }
    }

    fn exprs(&mut self, exprs: &[Expr]) {
        for expr in exprs {
            self.expr(expr);
        }
    }

    fn place_parts(&mut self, place: &Expr) {
        match &place.kind {
            ExprKind::Field { expr, .. } => self.expr(expr),
            ExprKind::Index { expr, index } => {
                self.expr(expr);
                self.expr(index);
            }
            ExprKind::Name(_) => {}
            _ => self.expr(place),
        }
    }

    fn target(&self, place: &Expr) -> Option<Target> {
        match &place.kind {
            ExprKind::Name(name) => match self.tcx.resolutions.get(name.span) {
                Some(Res::Local(decl)) => Some(Target::Local(decl)),
                _ => None,
            },
            ExprKind::Field { expr, name, .. } if matches!(expr.kind, ExprKind::This) => {
                Some(Target::Field(name.name))
            }
            _ => None,
        }
    }

    fn assign(&mut self, place: &Expr) {
        let Some(target) = self.target(place) else {
            return;
        };
        let Some(var) = self.vars.get(&target) else {
            return;
        };
        let at = match &place.kind {
            ExprKind::Field { name, .. } => name.span,
            _ => place.span,
        };
        let field = matches!(target, Target::Field(_));
        let what = if field { "field" } else { "variable" };
        let name = var.name;
        let error = if var.lambda_depth < self.lambda_depth {
            Some(
                Diagnostic::error(format!(
                    "cannot assign to `final` {what} `{name}` inside a lambda"
                ))
                .with_span(at)
                .with_secondary(var.decl, format!("`{name}` is declared `final` here"))
                .with_note("a lambda can run any number of times, after the code around it"),
            )
        } else if self.flow.maybe.contains(&target) {
            Some(match var.origin {
                Origin::Declared => {
                    Diagnostic::error(format!("cannot assign twice to `final` {what} `{name}`"))
                        .with_span(at)
                        .with_secondary(var.decl, format!("`{name}` is given its value here"))
                        .with_help(format!("remove `final` from `{name}` to change it"))
                }
                Origin::Delegated => Diagnostic::error(format!(
                    "`final` field `{name}` is already given its value by `this(...)`"
                ))
                .with_span(at)
                .with_secondary(var.decl, format!("`{name}` is declared `final` here"))
                .with_note("the constructor called with `this(...)` assigns every field"),
                Origin::Blank => Diagnostic::error(format!(
                    "`final` {what} `{name}` might already have been assigned"
                ))
                .with_span(at)
                .with_secondary(var.decl, format!("`{name}` is declared `final` here"))
                .with_note(format!("a `final` {what} is assigned exactly once")),
            })
        } else if var.loop_depth < self.loop_depth {
            Some(
                Diagnostic::error(format!(
                    "`final` {what} `{name}` might be assigned in a loop"
                ))
                .with_span(at)
                .with_secondary(var.decl, format!("`{name}` is declared `final` here"))
                .with_note(format!("a `final` {what} is assigned exactly once")),
            )
        } else {
            None
        };
        if let Some(error) = error {
            self.tcx.dcx.emit(error);
        }
        self.flow.assign(target);
        self.touched.push(target);
    }

    fn check_fields(&mut self, at: Option<Span>) {
        let Some(ctor) = &self.ctor else {
            return;
        };
        if !self.flow.live {
            return;
        }
        let span = at.unwrap_or(ctor.name);
        for target in &ctor.fields {
            if self.flow.definite.contains(target) || !self.missing.insert(*target) {
                continue;
            }
            let var = &self.vars[target];
            self.tcx.dcx.emit(
                Diagnostic::error(format!(
                    "this constructor doesn't always give `final` field `{}` a value",
                    var.name
                ))
                .with_span(span)
                .with_secondary(var.decl, format!("`{}` is declared `final` here", var.name))
                .with_help(format!(
                    "assign `this.{} = ...` on every path through the constructor",
                    var.name
                )),
            );
        }
    }

    fn leave_ctor(&mut self) {
        self.check_fields(None);
    }
}

fn is_true(cond: &Expr) -> bool {
    matches!(cond.kind, ExprKind::Bool(true))
}
