use std::collections::HashMap;

use krelpin_ast::ast::{
    Block, CaseLabel, CompilationUnit, Constructor, Expr, ExprKind, Field, FieldStorage, FnRetTy,
    GenericParamKind, Generics, Ident, ItemKind, LambdaBody, Member, MemberKind, Method, Param,
    Pat, PatKind, Path, PrimitiveTy, Stmt, StmtKind, SwitchExprBody, Ty, TyKind, WherePredicate,
};
use krelpin_errors::{DiagCtxt, Diagnostic};
use krelpin_span::def_id::DefId;
use krelpin_span::{Span, Symbol, kw};

use crate::collect::{ItemTable, TypeDef, UnitScope};
use crate::{PackagePath, Res, Resolutions};

#[derive(Clone, Copy, PartialEq, Eq)]
enum StaticContext {
    Method,
    StaticField,
}

#[derive(Clone, Copy, Default)]
struct Jumps {
    loops: u32,
    breakable: u32,
    switch_exprs: u32,
}

struct Resolver<'a> {
    table: &'a ItemTable,
    dcx: &'a DiagCtxt,
    resolutions: Resolutions,
    prelude: Vec<PackagePath>,
    scope: &'a UnitScope,
    owner: &'a TypeDef,
    class_type_params: Vec<(Symbol, Span)>,
    type_params: Vec<(Symbol, Span)>,
    borrow_sources: Vec<(Symbol, Span)>,
    scopes: Vec<HashMap<Symbol, Span>>,
    static_context: Option<StaticContext>,
    jumps: Jumps,
}

pub(crate) fn resolve_bodies(
    units: &[CompilationUnit],
    table: &ItemTable,
    dcx: &DiagCtxt,
) -> Resolutions {
    let Some(first) = table.defs.first() else {
        return Resolutions::default();
    };
    let mut resolver = Resolver {
        table,
        dcx,
        resolutions: Resolutions::default(),
        prelude: PackagePath::prelude(),
        scope: &table.scopes[first.unit],
        owner: first,
        class_type_params: Vec::new(),
        type_params: Vec::new(),
        borrow_sources: Vec::new(),
        scopes: Vec::new(),
        static_context: None,
        jumps: Jumps::default(),
    };

    for (type_def, item) in table.items(units) {
        resolver.owner = type_def;
        resolver.scope = &table.scopes[type_def.unit];
        match &item.kind {
            ItemKind::Class(class) => {
                resolver.enter_type(&class.generics);
                resolver.resolve_tys(class.extends.iter());
                resolver.resolve_tys(class.implements.iter());
                resolver.resolve_members(&class.members);
            }
            ItemKind::Record(def) => {
                resolver.enter_type(&def.generics);
                resolver.resolve_tys(def.components.iter().map(|component| &component.ty));
                resolver.resolve_tys(def.implements.iter());
                resolver.resolve_members(&def.members);
            }
            ItemKind::Interface(interface) => {
                resolver.enter_type(&interface.generics);
                resolver.resolve_tys(interface.extends.iter());
                resolver.resolve_members(&interface.members);
            }
            ItemKind::Enum(enum_def) => {
                resolver.enter_type(&enum_def.generics);
                resolver.resolve_tys(enum_def.implements.iter());
                for variant in &enum_def.variants {
                    resolver.resolve_tys(variant.fields.iter().map(|field| &field.ty));
                }
                resolver.resolve_members(&enum_def.members);
            }
        }
    }

    resolver.resolutions
}

impl<'a> Resolver<'a> {
    fn enter_type(&mut self, generics: &Generics) {
        self.class_type_params.clear();
        self.type_params.clear();
        self.borrow_sources.clear();
        self.static_context = None;

        let mut seen = HashMap::new();
        for param in &generics.params {
            if seen.insert(param.name.name, param.name.span).is_some() {
                self.report_duplicate_generic(param.name);
                continue;
            }
            let entry = (param.name.name, param.name.span);
            match &param.kind {
                GenericParamKind::Type { bounds } => {
                    self.class_type_params.push(entry);
                    self.type_params.push(entry);
                    self.resolve_tys(bounds.iter());
                }
                GenericParamKind::BorrowSource => self.borrow_sources.push(entry),
            }
        }
    }

    fn resolve_members(&mut self, members: &[Member]) {
        let class_type_params = self.class_type_params.clone();
        let class_borrow_sources = self.borrow_sources.clone();

        for member in members {
            let static_context = member_static_context(&member.kind);
            self.static_context = static_context;
            self.type_params = if static_context.is_some() {
                Vec::new()
            } else {
                class_type_params.clone()
            };
            self.borrow_sources = if static_context.is_some() {
                Vec::new()
            } else {
                class_borrow_sources.clone()
            };
            self.scopes.clear();
            self.jumps = Jumps::default();

            match &member.kind {
                MemberKind::Field(field) => self.resolve_field(field),
                MemberKind::Constructor(constructor) => self.resolve_constructor(constructor),
                MemberKind::Method(method) => self.resolve_method(method),
                MemberKind::Type(_) => {}
            }
        }
    }

    fn resolve_field(&mut self, field: &Field) {
        self.resolve_ty(&field.ty);
        if let Some(init) = &field.init {
            self.resolve_expr(init);
        }
    }

    fn resolve_constructor(&mut self, constructor: &Constructor) {
        self.resolve_kept(&constructor.params, &constructor.keeps);
        self.resolve_signature(&constructor.params, &constructor.throws);
        self.resolve_block(&constructor.body);
    }

    fn resolve_method(&mut self, method: &Method) {
        let mut seen = HashMap::new();
        for param in &method.generics.params {
            if seen.insert(param.name.name, param.name.span).is_some() {
                self.report_duplicate_generic(param.name);
                continue;
            }
            let entry = (param.name.name, param.name.span);
            match &param.kind {
                GenericParamKind::Type { .. } => self.type_params.push(entry),
                GenericParamKind::BorrowSource => self.borrow_sources.push(entry),
            }
        }
        for param in &method.generics.params {
            if let GenericParamKind::Type { bounds } = &param.kind {
                self.resolve_tys(bounds.iter());
            }
        }
        for predicate in &method.where_clause {
            self.resolve_where_predicate(predicate);
        }

        if let Some(receiver) = method.receiver {
            self.borrow_sources.push((kw::This, receiver.span));
        }
        for param in &method.params {
            self.borrow_sources.push((param.name.name, param.name.span));
        }

        if let FnRetTy::Ty(ty) = &method.ret {
            self.resolve_ty(ty);
        }
        for source in &method.borrows {
            self.resolve_borrow_source(*source);
        }
        self.resolve_kept(&method.params, &method.keeps);
        self.resolve_signature(&method.params, &method.throws);
        if let Some(body) = &method.body {
            self.resolve_block(body);
        }
    }

    fn resolve_where_predicate(&mut self, predicate: &WherePredicate) {
        let param = predicate.param;
        let found = self
            .type_params
            .iter()
            .rev()
            .find(|&&(name, _)| name == param.name);
        let Some(&(_, span)) = found else {
            self.emit(
                Diagnostic::error(format!("cannot find generic parameter `{}`", param.name))
                    .with_span(param.span)
                    .with_help(
                        "a `where` clause can only constrain the generic parameters in scope",
                    ),
            );
            return;
        };
        self.resolutions.record(param.span, Res::TypeParam(span));
        self.resolve_tys(predicate.bounds.iter());
    }

    fn resolve_signature(&mut self, params: &[Param], throws: &[Ty]) {
        self.scopes.push(HashMap::new());
        for param in params {
            self.resolve_ty(&param.ty);
            self.declare(param.name);
        }
        self.resolve_tys(throws.iter());
    }

    fn resolve_tys<'t>(&mut self, tys: impl Iterator<Item = &'t Ty>) {
        for ty in tys {
            self.resolve_ty(ty);
        }
    }

    fn resolve_ty(&mut self, ty: &Ty) {
        match &ty.kind {
            TyKind::Primitive(_) => {}
            TyKind::Path { path, args } => {
                match path.segments.as_slice() {
                    [segment] => self.resolve_type_name(*segment),
                    segments => {
                        self.resolve_type_path(segments);
                    }
                }
                self.resolve_tys(args.iter());
            }
            TyKind::Ref { ty, .. } => self.resolve_ty(ty),
            TyKind::Nullable(ty) | TyKind::Array(ty) => self.resolve_ty(ty),
        }
    }

    fn resolve_type_name(&mut self, name: Ident) {
        if let Some(res) = self.lookup_type(name.name) {
            self.resolutions.record(name.span, res);
            return;
        }

        let is_class_param = self
            .class_type_params
            .iter()
            .any(|&(param, _)| param == name.name);
        if is_class_param {
            self.emit(
                Diagnostic::error(format!(
                    "generic parameter `{}` cannot be used here",
                    name.name
                ))
                .with_span(name.span)
                .with_note(
                    "static fields, const fields and static methods belong to the \
                     class, not to a specific instance",
                ),
            );
            return;
        }

        let mut diagnostic =
            Diagnostic::error(format!("cannot find type `{}` in this scope", name.name))
                .with_span(name.span)
                .with_label("not found in this scope");
        let mut candidates: Vec<String> = self
            .table
            .packages
            .iter()
            .filter(|(_, types)| types.contains_key(&name.name))
            .map(|(package, _)| format!("`import {package}.{};`", name.name))
            .collect();
        candidates.sort();
        if !candidates.is_empty() {
            diagnostic =
                diagnostic.with_help(format!("import it with {}", candidates.join(" or ")));
        }
        self.emit(diagnostic);
    }

    fn resolve_kept(&mut self, params: &[Param], keeps: &[Ident]) {
        for kept in keeps {
            match params.iter().find(|param| param.name.name == kept.name) {
                Some(param) => self
                    .resolutions
                    .record(kept.span, Res::BorrowSource(param.name.span)),
                None => self.emit(
                    Diagnostic::error(format!("cannot find parameter `{}` to keep", kept.name))
                        .with_span(kept.span)
                        .with_help("`keeps` names the parameters that the method may store"),
                ),
            }
        }
    }

    fn resolve_borrow_source(&mut self, source: Ident) {
        let found = self
            .borrow_sources
            .iter()
            .rev()
            .find(|&&(name, _)| name == source.name);
        match found {
            Some(&(_, span)) => self
                .resolutions
                .record(source.span, Res::BorrowSource(span)),
            None => {
                self.emit(
                    Diagnostic::error(format!("cannot find borrow source `{}`", source.name))
                        .with_span(source.span)
                        .with_help(
                            "a borrow source must name a parameter of the method, `this`, \
                             or a borrow source of the class, like `text` in \
                             `class Parser borrows text`",
                        ),
                );
            }
        }
    }

    fn lookup_type(&self, name: Symbol) -> Option<Res> {
        if let Some(primitive) = PrimitiveTy::from_symbol(name) {
            return Some(Res::PrimTy(primitive));
        }
        if let Some(&(_, span)) = self.type_params.iter().rev().find(|&&(p, _)| p == name) {
            return Some(Res::TypeParam(span));
        }
        let mut enclosing = Some(self.owner.def);
        while let Some(def) = enclosing {
            if let Some(nested) = self.table.nested(def, name) {
                return Some(Res::Item(nested));
            }
            enclosing = self.table.def(def).parent;
        }
        if let Some(&res) = self.scope.imports.get(&name) {
            return Some(res);
        }
        std::iter::once(&self.scope.package)
            .chain(&self.scope.globs)
            .chain(&self.prelude)
            .find_map(|package| self.table.lookup(package, name))
            .map(Res::Item)
    }

    fn lookup_local(&self, name: Symbol) -> Option<Span> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(&name).copied())
    }

    fn declare(&mut self, name: Ident) {
        if self.lookup_local(name.name).is_some() {
            self.emit(
                Diagnostic::error(format!(
                    "a variable named `{}` is already defined in this scope",
                    name.name
                ))
                .with_span(name.span)
                .with_help("choose a different name"),
            );
            return;
        }
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name.name, name.span);
        }
    }

    fn with_scope(&mut self, f: impl FnOnce(&mut Self)) {
        self.scopes.push(HashMap::new());
        f(self);
        self.scopes.pop();
    }

    fn resolve_block(&mut self, block: &Block) {
        self.with_scope(|this| {
            for stmt in &block.stmts {
                this.resolve_stmt(stmt);
            }
        });
    }

    fn resolve_stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Local(local) => {
                self.resolve_ty(&local.ty);
                if let Some(init) = &local.init {
                    self.resolve_expr(init);
                }
                self.declare(local.name);
            }
            StmtKind::Expr(expr) => self.resolve_expr(expr),
            StmtKind::Block(block) => self.resolve_block(block),
            StmtKind::If { cond, then, els } => {
                self.with_scope(|this| {
                    this.resolve_expr(cond);
                    this.with_scope(|this| this.resolve_stmt(then));
                });
                if let Some(els) = els {
                    self.with_scope(|this| this.resolve_stmt(els));
                }
            }
            StmtKind::While { cond, body } => self.with_scope(|this| {
                this.resolve_expr(cond);
                this.resolve_loop_body(body);
            }),
            StmtKind::DoWhile { body, cond } => {
                self.resolve_loop_body(body);
                self.resolve_expr(cond);
            }
            StmtKind::For {
                init,
                cond,
                update,
                body,
            } => self.with_scope(|this| {
                for stmt in init {
                    this.resolve_stmt(stmt);
                }
                if let Some(cond) = cond {
                    this.resolve_expr(cond);
                }
                for expr in update {
                    this.resolve_expr(expr);
                }
                this.resolve_loop_body(body);
            }),
            StmtKind::ForEach {
                ty,
                name,
                iter,
                body,
                ..
            } => {
                self.resolve_expr(iter);
                self.with_scope(|this| {
                    this.resolve_ty(ty);
                    this.declare(*name);
                    this.resolve_loop_body(body);
                });
            }
            StmtKind::Switch { scrutinee, arms } => {
                self.resolve_expr(scrutinee);
                self.jumps.breakable += 1;
                for arm in arms {
                    self.with_scope(|this| {
                        this.resolve_case_label(&arm.label);
                        this.resolve_stmt(&arm.body);
                    });
                }
                self.jumps.breakable -= 1;
            }
            StmtKind::Try {
                body,
                catches,
                finally,
            } => {
                self.resolve_block(body);
                for catch in catches {
                    self.with_scope(|this| {
                        this.resolve_tys(catch.tys.iter());
                        this.declare(catch.name);
                        this.resolve_block(&catch.body);
                    });
                }
                if let Some(finally) = finally {
                    self.resolve_block(finally);
                }
            }
            StmtKind::Return(value) => {
                if self.jumps.switch_exprs > 0 {
                    self.emit(
                        Diagnostic::error("cannot `return` from inside a switch expression")
                            .with_span(stmt.span)
                            .with_help("use `yield` to produce the value of this case"),
                    );
                }
                if let Some(value) = value {
                    self.resolve_expr(value);
                }
            }
            StmtKind::Yield(value) => {
                if self.jumps.switch_exprs == 0 {
                    self.emit(
                        Diagnostic::error("`yield` outside of a switch expression")
                            .with_span(stmt.span)
                            .with_help(
                                "`yield` gives the value of a `case` block in a switch expression",
                            ),
                    );
                }
                self.resolve_expr(value);
            }
            StmtKind::Throw(value) => self.resolve_expr(value),
            StmtKind::Break => {
                if self.jumps.breakable == 0 {
                    self.emit(
                        Diagnostic::error("`break` outside of a loop or switch")
                            .with_span(stmt.span),
                    );
                }
            }
            StmtKind::Continue => {
                if self.jumps.loops == 0 {
                    self.emit(
                        Diagnostic::error("`continue` outside of a loop").with_span(stmt.span),
                    );
                }
            }
            StmtKind::Empty => {}
        }
    }

    fn resolve_loop_body(&mut self, body: &Stmt) {
        self.jumps.loops += 1;
        self.jumps.breakable += 1;
        self.with_scope(|this| this.resolve_stmt(body));
        self.jumps.loops -= 1;
        self.jumps.breakable -= 1;
    }

    fn resolve_case_label(&mut self, label: &CaseLabel) {
        let CaseLabel::Case { pats, guard } = label else {
            return;
        };
        for pat in pats {
            self.resolve_pat(pat);
        }
        if pats.len() > 1 {
            for binding in pats.iter().filter_map(first_binding) {
                self.emit(
                    Diagnostic::error("a case with several patterns cannot bind variables")
                        .with_span(binding.span)
                        .with_help("give each pattern its own `case`"),
                );
            }
        }
        if let Some(guard) = guard {
            self.resolve_expr(guard);
        }
    }

    fn resolve_pat(&mut self, pat: &Pat) {
        match &pat.kind {
            PatKind::Wild => {}
            PatKind::Lit(expr) => self.resolve_expr(expr),
            PatKind::Path(path) => self.resolve_pat_path(path),
            PatKind::Ty { ty, binding } => {
                self.resolve_ty(ty);
                if let Some(binding) = binding {
                    self.declare(*binding);
                }
            }
            PatKind::Variant { path, fields } => {
                self.resolve_pat_path(path);
                for field in fields {
                    self.resolve_pat(field);
                }
            }
        }
    }

    fn resolve_pat_path(&mut self, path: &Path) {
        match path.segments.as_slice() {
            [name] => {
                if let Some(res) = self.lookup_type(name.name) {
                    self.resolutions.record(name.span, res);
                }
            }
            [owner @ .., _] => {
                self.resolve_type_path(owner);
            }
            [] => {}
        }
    }

    fn resolve_type_path(&mut self, segments: &[Ident]) -> Option<DefId> {
        let (first, rest) = segments.split_first()?;
        let def = match self.lookup_type(first.name) {
            Some(Res::Item(def)) => {
                self.resolutions.record(first.span, Res::Item(def));
                def
            }
            Some(res) if rest.is_empty() => {
                self.resolutions.record(first.span, res);
                return None;
            }
            _ if rest.is_empty() => {
                self.resolve_type_name(*first);
                return None;
            }
            _ => return self.resolve_qualified_type(segments),
        };
        self.resolve_nested_types(def, rest)
    }

    fn resolve_qualified_type(&mut self, segments: &[Ident]) -> Option<DefId> {
        let found = (1..segments.len()).find_map(|len| {
            let package = PackagePath::from_idents(&segments[..len]);
            self.table
                .lookup(&package, segments[len].name)
                .map(|def| (len, def))
        });
        let Some((package_len, def)) = found else {
            self.report_unresolved_path(segments);
            return None;
        };
        self.resolutions
            .record(segments[package_len].span, Res::Item(def));
        self.resolve_nested_types(def, &segments[package_len + 1..])
    }

    /// Reports a dotted path that names no type: either its package doesn't
    /// exist or the package has no such type.
    fn report_unresolved_path(&mut self, segments: &[Ident]) {
        let (Some(first), Some(last)) = (segments.first(), segments.last()) else {
            return;
        };
        let package_len = (1..segments.len()).rev().find(|&len| {
            let package = PackagePath::from_idents(&segments[..len]);
            self.table.packages.contains_key(&package)
        });
        let diagnostic = match package_len {
            Some(len) => {
                let package = PackagePath::from_idents(&segments[..len]);
                let name = segments[len];
                Diagnostic::error(format!(
                    "cannot find type `{}` in package `{package}`",
                    name.name
                ))
                .with_span(name.span)
                .with_label("not found in this package")
            }
            None => {
                let path: Vec<String> = segments.iter().map(|s| s.name.to_string()).collect();
                Diagnostic::error(format!("cannot find type `{}`", path.join(".")))
                    .with_span(first.span.to(last.span))
                    .with_label("no package or type has this name")
            }
        };
        self.emit(diagnostic);
    }

    fn resolve_nested_types(&mut self, mut def: DefId, rest: &[Ident]) -> Option<DefId> {
        for segment in rest {
            let Some(nested) = self.table.nested(def, segment.name) else {
                self.emit(
                    Diagnostic::error(format!(
                        "cannot find type `{}` in `{}`",
                        segment.name,
                        self.table.def(def).name.name
                    ))
                    .with_span(segment.span)
                    .with_label("not found in this type"),
                );
                return None;
            };
            self.resolutions.record(segment.span, Res::Item(nested));
            def = nested;
        }
        Some(def)
    }

    fn resolve_qualified_expr(&mut self, expr: &Expr) -> bool {
        let mut segments = Vec::new();
        let mut current = expr;
        loop {
            match &current.kind {
                ExprKind::Field { expr, name, .. } => {
                    segments.push(*name);
                    current = expr;
                }
                ExprKind::Name(name) => {
                    segments.push(*name);
                    break;
                }
                _ => return false,
            }
        }
        segments.reverse();
        let root = segments[0].name;
        if self.lookup_local(root).is_some()
            || self.lookup_type(root).is_some()
            || self.owner.fields.contains_key(&root)
        {
            return false;
        }
        let Some((package_len, mut def)) = (1..segments.len()).find_map(|len| {
            let package = PackagePath::from_idents(&segments[..len]);
            self.table
                .lookup(&package, segments[len].name)
                .map(|def| (len, def))
        }) else {
            return false;
        };
        let mut resolved = vec![(segments[package_len].span, def)];
        for segment in &segments[package_len + 1..] {
            let Some(nested) = self.table.nested(def, segment.name) else {
                return false;
            };
            resolved.push((segment.span, nested));
            def = nested;
        }
        for (span, def) in resolved {
            self.resolutions.record(span, Res::Item(def));
        }
        true
    }

    fn type_def_of_expr(&self, expr: &Expr) -> Option<DefId> {
        let span = match &expr.kind {
            ExprKind::Name(name) => name.span,
            ExprKind::Field { name, .. } => name.span,
            _ => return None,
        };
        match self.resolutions.get(span) {
            Some(Res::Item(def)) => Some(def),
            _ => None,
        }
    }

    fn resolve_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Lit(_) | ExprKind::Bool(_) | ExprKind::Null => {}
            ExprKind::This | ExprKind::Super => self.check_this(expr),
            ExprKind::Name(name) => self.resolve_value_name(*name),
            ExprKind::Field {
                expr: inner, name, ..
            } => {
                if self.resolve_qualified_expr(expr) {
                    return;
                }
                let expr = inner;
                self.resolve_expr(expr);
                let nested = self
                    .type_def_of_expr(expr)
                    .and_then(|owner| self.table.nested(owner, name.name));
                if let Some(nested) = nested {
                    self.resolutions.record(name.span, Res::Item(nested));
                }
            }
            ExprKind::MethodCall {
                receiver,
                name,
                args,
                ..
            } => {
                match receiver {
                    Some(receiver) => self.resolve_expr(receiver),
                    None => self.resolve_unqualified_call(*name),
                }
                self.resolve_exprs(args);
            }
            ExprKind::Call { callee, args } => {
                self.resolve_expr(callee);
                self.resolve_exprs(args);
            }
            ExprKind::Index { expr, index } => {
                self.resolve_expr(expr);
                self.resolve_expr(index);
            }
            ExprKind::New { ty, args } => {
                self.resolve_ty(ty);
                self.resolve_exprs(args);
            }
            ExprKind::NewArray { elem, len } => {
                self.resolve_ty(elem);
                self.resolve_expr(len);
            }
            ExprKind::ArrayInit { ty, elems } => {
                if let Some(ty) = ty {
                    self.resolve_ty(ty);
                }
                self.resolve_exprs(elems);
            }
            ExprKind::Unary { expr, .. }
            | ExprKind::Borrow { expr, .. }
            | ExprKind::Await(expr) => {
                self.resolve_expr(expr);
            }
            ExprKind::Binary { lhs, rhs, .. } | ExprKind::Assign { lhs, rhs, .. } => {
                self.resolve_expr(lhs);
                self.resolve_expr(rhs);
            }
            ExprKind::Ternary { cond, then, els } => {
                self.resolve_expr(cond);
                self.resolve_expr(then);
                self.resolve_expr(els);
            }
            ExprKind::InstanceOf { expr, pat } => {
                self.resolve_expr(expr);
                self.resolve_pat(pat);
            }
            ExprKind::Cast { ty, expr } => {
                self.resolve_ty(ty);
                self.resolve_expr(expr);
            }
            ExprKind::Lambda { params, body, .. } => {
                let outer_jumps = std::mem::take(&mut self.jumps);
                self.with_scope(|this| {
                    for param in params {
                        if let Some(ty) = &param.ty {
                            this.resolve_ty(ty);
                        }
                        this.declare(param.name);
                    }
                    match body.as_ref() {
                        LambdaBody::Expr(expr) => this.resolve_expr(expr),
                        LambdaBody::Block(block) => this.resolve_block(block),
                    }
                });
                self.jumps = outer_jumps;
            }
            ExprKind::MethodRef { expr, .. } => self.resolve_expr(expr),
            ExprKind::With { base, fields } => {
                self.resolve_expr(base);
                for field in fields {
                    self.resolve_expr(&field.value);
                }
            }
            ExprKind::Switch { scrutinee, arms } => {
                self.resolve_expr(scrutinee);
                let outer_jumps = self.jumps;
                self.jumps = Jumps {
                    switch_exprs: outer_jumps.switch_exprs + 1,
                    ..Jumps::default()
                };
                for arm in arms {
                    self.with_scope(|this| {
                        this.resolve_case_label(&arm.label);
                        match &arm.body {
                            SwitchExprBody::Expr(expr) | SwitchExprBody::Throw(expr) => {
                                this.resolve_expr(expr);
                            }
                            SwitchExprBody::Block(block) => this.resolve_block(block),
                        }
                    });
                }
                self.jumps = outer_jumps;
            }
        }
    }

    fn resolve_exprs(&mut self, exprs: &[Expr]) {
        for expr in exprs {
            self.resolve_expr(expr);
        }
    }

    fn resolve_value_name(&mut self, name: Ident) {
        if let Some(span) = self.lookup_local(name.name) {
            self.resolutions.record(name.span, Res::Local(span));
            return;
        }
        if let Some(res) = self.lookup_type(name.name) {
            self.resolutions.record(name.span, res);
            return;
        }
        let mut diagnostic =
            Diagnostic::error(format!("cannot find value `{}` in this scope", name.name))
                .with_span(name.span)
                .with_label("not found in this scope");

        if let Some(field) = self.owner.fields.get(&name.name) {
            let owner = self.owner.name.name;
            diagnostic = if field.is_instance {
                diagnostic.with_help(format!(
                    "to use the field of this object, write `this.{}`",
                    name.name
                ))
            } else {
                diagnostic.with_help(format!(
                    "to use the field of the class, write `{owner}.{}`",
                    name.name
                ))
            };
        }
        self.emit(diagnostic);
    }

    fn resolve_unqualified_call(&mut self, name: Ident) {
        let Some(methods) = self.owner.methods.get(&name.name) else {
            self.emit(
                Diagnostic::error(format!("cannot find method `{}` in this scope", name.name))
                    .with_span(name.span)
                    .with_label("not found in this scope"),
            );
            return;
        };

        let has_static = methods.iter().any(|method| !method.has_receiver);
        if has_static {
            return;
        }

        let diagnostic = Diagnostic::error(format!(
            "method `{}` needs an object to be called on",
            name.name
        ))
        .with_span(name.span);
        let diagnostic = if self.static_context.is_none() {
            diagnostic.with_help(format!("call it on this object: `this.{}(...)`", name.name))
        } else {
            diagnostic.with_note(format!(
                "`{}` is not `static`, so it needs an object",
                name.name
            ))
        };
        self.emit(diagnostic);
    }

    fn check_this(&mut self, expr: &Expr) {
        let keyword = if expr.kind == ExprKind::This {
            "this"
        } else {
            "super"
        };
        let help = match self.static_context {
            None => return,
            Some(StaticContext::Method) => "remove `static` from the method to use `this` in it",
            Some(StaticContext::StaticField) => {
                "a `static` field belongs to the class, not to a specific object"
            }
        };
        self.emit(
            Diagnostic::error(format!("`{keyword}` is not available here"))
                .with_span(expr.span)
                .with_help(help),
        );
    }

    fn report_duplicate_generic(&self, name: Ident) {
        self.emit(
            Diagnostic::error(format!(
                "the generic parameter `{}` is declared multiple times",
                name.name
            ))
            .with_span(name.span),
        );
    }

    fn emit(&self, diagnostic: Diagnostic) {
        self.dcx.emit(diagnostic);
    }
}

fn member_static_context(kind: &MemberKind) -> Option<StaticContext> {
    match kind {
        MemberKind::Field(field) => match field.storage {
            FieldStorage::Instance => None,
            FieldStorage::Static(_) => Some(StaticContext::StaticField),
        },
        MemberKind::Constructor(_) | MemberKind::Type(_) => None,
        MemberKind::Method(method) => method.receiver.is_none().then_some(StaticContext::Method),
    }
}

fn first_binding(pat: &Pat) -> Option<Ident> {
    match &pat.kind {
        PatKind::Ty { binding, .. } => *binding,
        PatKind::Variant { fields, .. } => fields.iter().find_map(first_binding),
        PatKind::Wild | PatKind::Lit(_) | PatKind::Path(_) => None,
    }
}
