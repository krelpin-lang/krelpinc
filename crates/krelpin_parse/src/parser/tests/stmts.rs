use krelpin_ast::ast::{CaseLabel, Stmt, StmtKind};

use super::{body, body_errors, parse_str};

fn kinds(stmts: &[Stmt]) -> Vec<&'static str> {
    stmts.iter().map(|stmt| kind_name(&stmt.kind)).collect()
}

fn kind_name(kind: &StmtKind) -> &'static str {
    match kind {
        StmtKind::Local(_) => "local",
        StmtKind::Expr(_) => "expr",
        StmtKind::Block(_) => "block",
        StmtKind::If { .. } => "if",
        StmtKind::While { .. } => "while",
        StmtKind::DoWhile { .. } => "do",
        StmtKind::For { .. } => "for",
        StmtKind::ForEach { .. } => "foreach",
        StmtKind::Switch { .. } => "switch",
        StmtKind::Try { .. } => "try",
        StmtKind::Return(_) => "return",
        StmtKind::Yield(_) => "yield",
        StmtKind::Throw(_) => "throw",
        StmtKind::Break(_) => "break",
        StmtKind::Continue(_) => "continue",
        StmtKind::Labeled { .. } => "labeled",
        StmtKind::Empty => "empty",
    }
}

fn local_decls(src: &str) -> Vec<String> {
    body(src)
        .iter()
        .map(|stmt| match &stmt.kind {
            StmtKind::Local(local) => format!("{} {}", local.ty, local.name.name),
            other => panic!("expected a local, found {other:?}"),
        })
        .collect()
}

#[test]
fn local_declarations() {
    assert_eq!(
        local_decls(
            "int x = 1; long y = 2; List<String> names = new ArrayList<>(); \
             &String r = &name; String? n = null; int[] xs = {1}; \
             Map<String, List<Integer>> m; &mut Buffer b = &mut buffer;"
        ),
        [
            "int x",
            "long y",
            "List<String> names",
            "&String r",
            "String? n",
            "int[] xs",
            "Map<String, List<Integer>> m",
            "&mut Buffer b",
        ]
    );
}

#[test]
fn expression_statements() {
    assert_eq!(
        kinds(&body("x = 5; a.b.c(); i++; --j; new Thread(); this(1);")),
        ["expr", "expr", "expr", "expr", "expr", "expr"]
    );
}

#[test]
fn if_else_chains() {
    let stmts = body("if (a) b(); else if (c) d(); else { e(); }");
    let StmtKind::If { els: Some(els), .. } = &stmts[0].kind else {
        panic!("expected if with else");
    };
    let StmtKind::If {
        els: Some(last), ..
    } = &els.kind
    else {
        panic!("expected else if");
    };
    assert_eq!(kind_name(&last.kind), "block");
}

#[test]
fn loops() {
    assert_eq!(
        kinds(&body(
            "while (running) step(); \
             do { tick(); } while (busy); \
             for (int i = 0; i < n; i++, j--) {} \
             for (;;) break; \
             for (String s : names) print(s); \
             for (&String s : &names) {}"
        )),
        ["while", "do", "for", "for", "foreach", "foreach"]
    );
}

#[test]
fn classic_for_parts() {
    let stmts = body("for (i = 0, j = 1; i < j; i++, j--) {}");
    let StmtKind::For {
        init, cond, update, ..
    } = &stmts[0].kind
    else {
        panic!("expected for");
    };
    assert_eq!(init.len(), 2);
    assert_eq!(cond.as_ref().unwrap().to_string(), "(i < j)");
    assert_eq!(update.len(), 2);
}

#[test]
fn switch_with_arrows() {
    let stmts = body("switch (x) { case 1, 2 -> a(); case 3 -> { b(); } default -> c(); }");
    let StmtKind::Switch { arms, .. } = &stmts[0].kind else {
        panic!("expected switch");
    };
    let labels: Vec<Option<usize>> = arms
        .iter()
        .map(|arm| match &arm.label {
            CaseLabel::Case { pats, .. } => Some(pats.len()),
            CaseLabel::Default(_) => None,
        })
        .collect();
    assert_eq!(labels, [Some(2), Some(1), None]);
}

#[test]
fn try_catch_finally() {
    let stmts = body(
        "try { read(); } catch (IOException | ParseException e) { log(e); } \
         catch (Error e) {} finally { close(); }",
    );
    let StmtKind::Try {
        catches, finally, ..
    } = &stmts[0].kind
    else {
        panic!("expected try");
    };
    assert_eq!(catches[0].tys.len(), 2);
    assert_eq!(catches.len(), 2);
    assert!(finally.is_some());
}

#[test]
fn jumps() {
    assert_eq!(
        kinds(&body(
            "return; return x + 1; throw new Error(); break; continue; ;"
        )),
        ["return", "return", "throw", "break", "continue", "empty"]
    );
}

#[test]
fn missing_semicolon_is_recovered() {
    let parsed = parse_str("class A { static void f() { int x = 1\n int y = 2; } }");
    assert_eq!(parsed.errors, ["expected `;`, found keyword `int`"]);
    assert_eq!(super::class(&parsed.unit, 0).members.len(), 1);
}

#[test]
fn statement_errors() {
    assert_eq!(body_errors("x + 1;"), ["expression is not a statement"]);
    assert_eq!(
        body_errors("switch (x) { case 1: a(); }"),
        ["switch cases must use `->`"]
    );
    assert_eq!(
        body_errors("try { }"),
        ["`try` without `catch` or `finally`"]
    );
    assert_eq!(body_errors("if x {}"), ["expected `(`, found `x`"]);
    assert_eq!(body_errors("int x = ;"), ["expected expression, found `;`"]);
}

#[test]
fn unclosed_nested_block_reports_once() {
    assert_eq!(
        super::errors("class A { void f() { if (x) { y(); }"),
        ["this file contains an unclosed delimiter"]
    );
}

#[test]
fn yield_statements() {
    assert_eq!(kinds(&body("yield 1;")), ["yield"]);
}

#[test]
fn var_is_not_a_declaration() {
    assert_eq!(
        body_errors("var x = 1; int y = 2;"),
        ["invalid variable declaration"]
    );
    assert_eq!(
        body_errors("for (var s : names) {}"),
        ["invalid variable declaration"]
    );
    assert_eq!(
        body_errors("int var = 1; var = var + 1;"),
        Vec::<String>::new()
    );
}
