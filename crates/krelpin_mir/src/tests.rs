use std::path::Path;

use krelpin_errors::{DiagCtxt, DiagnosticBuffer};
use krelpin_parse::{lexer, parser};
use krelpin_span::SourceMap;
use krelpin_sysroot::Sysroot;

use crate::BodyId;

fn build_str(src: &str) -> String {
    let source_map = SourceMap::new();
    let buffer = DiagnosticBuffer::default();
    let dcx = DiagCtxt::new(buffer.clone());
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut units = Sysroot::new(root)
        .expect("the workspace is a sysroot")
        .load_std(&source_map, &dcx);
    let file = source_map.new_source_file("test.kr", src.to_owned());
    units.push(parser::parse(lexer::lex(&file, &dcx), &dcx));
    krelpin_expand::expand(&mut units, &source_map, &dcx);
    let resolved = krelpin_resolve::resolve(&units, &dcx);
    let typeck = krelpin_typeck::check(&units, &resolved, &dcx);
    assert_eq!(buffer.messages(), Vec::<String>::new(), "errors in {src:?}");

    let hir = krelpin_hir::lower(&units, &resolved, &typeck.tcx, &typeck.results);
    let mir = crate::build(&hir, &typeck.tcx);
    for body in &mir.bodies {
        for block in &body.blocks {
            for target in block.terminator.kind.successors() {
                assert!(
                    target.index() < body.blocks.len(),
                    "dangling edge in {}",
                    body.name
                );
            }
        }
    }
    let user_unit = units.len() - 1;
    let bodies: Vec<BodyId> = (0..mir.bodies.len())
        .map(|index| BodyId(index as u32))
        .filter(|&id| resolved.items.def(mir.body(id).owner).unit == user_unit)
        .collect();
    crate::print(&mir, bodies, &typeck.tcx)
}

fn assert_builds_to(src: &str, expected: &[&str]) {
    let printed = build_str(src);
    for line in expected {
        assert!(
            printed.lines().any(|printed| printed.trim() == *line),
            "missing `{line}` in\n{printed}"
        );
    }
}

fn assert_lacks(src: &str, unexpected: &[&str]) {
    let printed = build_str(src);
    for line in unexpected {
        assert!(!printed.contains(line), "unexpected `{line}` in\n{printed}");
    }
}

#[test]
fn mutable_receivers_are_reborrowed() {
    assert_builds_to(
        "class Counter {\n\
         \x20   int count;\n\
         \x20   mut void bump() { this.count++; }\n\
         \x20   mut void twice() { this.bump(); this.bump(); }\n\
         }",
        &[
            "fn Counter.twice(_1: &mut Counter) -> void {",
            "_2 = &mut (*_1);",
            "Counter::bump(move _2) -> [return: bb1, unwind continue];",
            "_3 = &mut (*_1);",
            "(*_1).count = Add(copy (*_1).count, const 1_int);",
        ],
    );
}

#[test]
fn values_are_copied_or_moved_by_type() {
    assert_builds_to(
        "record Point(int x, int y) {}\n\
         record Bag(int[] items) {}\n\
         class A { static void f(Point p, Bag n, String s) {\n\
         \x20   Point q = p; Point r = p; Bag m = n; String t = s;\n\
         } }",
        &[
            "_4 = copy _1;",
            "_5 = copy _1;",
            "_6 = move _2;",
            "_7 = copy _3;",
        ],
    );
}

#[test]
fn finally_runs_on_every_exit() {
    assert_builds_to(
        "class A { static int f(int x) {\n\
         \x20   while (true) {\n\
         \x20       try {\n\
         \x20           if (x > 1) { return x; }\n\
         \x20           if (x > 2) { break; }\n\
         \x20       } finally {\n\
         \x20           x = 0;\n\
         \x20       }\n\
         \x20   }\n\
         \x20   return -1;\n\
         } }",
        &["_0 = copy _1;", "_1 = const 0;", "return;"],
    );
    let printed = build_str(
        "class A { static int f(int x) {\n\
         \x20   try { return x; } finally { x = 0; }\n\
         } }",
    );
    let resets = printed.matches("_1 = const 0;").count();
    assert_eq!(resets, 1, "{printed}");
}

#[test]
fn exceptions_flow_to_handlers() {
    assert_builds_to(
        "import std.io.IOException;\n\
         class A {\n\
         \x20   static void risky() throws IOException {}\n\
         \x20   static int f() {\n\
         \x20       try { A.risky(); return 1; }\n\
         \x20       catch (IOException error) { return 2; }\n\
         \x20       finally { A.risky2(); }\n\
         \x20   }\n\
         \x20   static void risky2() {}\n\
         }",
        &[
            "A::risky() -> [return: bb2, unwind: bb1];",
            "_1 = caught;",
            "_2 = _1 instanceof IOException;",
            "_3 = move (_1 as IOException);",
            "A::risky2() -> [return: bb7, unwind continue];",
            "throw(move _1) -> [unwind continue];",
        ],
    );
}

#[test]
fn exhaustive_switches_match_variants() {
    assert_builds_to(
        "enum Shape { Circle(double radius), Dot;\n\
         \x20   double area() {\n\
         \x20       return switch (this) {\n\
         \x20           case Circle(double r) when r > 1.0 -> r;\n\
         \x20           case Circle(double r) -> 1.0;\n\
         \x20           case Dot -> 0.0;\n\
         \x20       };\n\
         \x20   }\n\
         }",
        &[
            "_2 = discriminant((*_1));",
            "switchInt(move _2) -> [0: bb3, otherwise: bb2];",
            "_3 = Gt(copy ((*_1) as Circle).radius, const 1.0);",
            "_4 = copy ((*_1) as Circle).radius;",
            "unreachable;",
        ],
    );
}

#[test]
fn type_patterns_test_and_bind() {
    assert_builds_to(
        "record Point(double x, double y) {}\n\
         class A { static double f(Object any) {\n\
         \x20   if (any instanceof Point(double x, _)) { return x; }\n\
         \x20   return 0.0;\n\
         } }",
        &["_2 = _1 instanceof Point;", "_3 = copy (_1 as Point).x;"],
    );
}

#[test]
fn records_are_built_from_components() {
    assert_builds_to(
        "record User(String name, long visits) {}\n\
         class A {\n\
         \x20   static User make() { return new User(\"ada\", 1L); }\n\
         \x20   static User visit(User user) { return user with { visits = 2L }; }\n\
         }",
        &[
            "_0 = User { name: const \"ada\", visits: const 1L };",
            "_0 = User { name: copy _1.name, visits: const 2L };",
        ],
    );
}

#[test]
fn records_with_compact_constructors_call_them() {
    assert_builds_to(
        "record Age(int years) {\n\
         \x20   Age { if (years < 0) { throw new IllegalArgumentException(\"age\"); } }\n\
         }\n\
         class A { static Age make() { return new Age(3); } }",
        &[
            "_1 = new Age;",
            "Age::Age(move _2, const 3) -> [return: bb1, unwind continue];",
            "(*_1).years = copy _2;",
        ],
    );
}

#[test]
fn checks_guard_indexing_division_and_casts() {
    assert_builds_to(
        "class A { static int f(int[] values, int index, Object any) {\n\
         \x20   String text = (String) any;\n\
         \x20   return values[index] / index + values[0] / 2;\n\
         } }",
        &[
            "assert(_3 instanceof String) -> [success: bb1, unwind continue];",
            "assert(copy _2 < move _6) -> [success: bb2, unwind continue];",
            "assert(copy _2 != 0) -> [success: bb3, unwind continue];",
        ],
    );
    assert_lacks(
        "class A { static int f(int value) { return value / 2; } }",
        &["!= 0"],
    );
}

#[test]
fn iterables_use_their_iterator() {
    assert_builds_to(
        "import std.util.List;\n\
         class A { static int f(List<String> names) {\n\
         \x20   int count = 0;\n\
         \x20   for (String name : names) { count++; }\n\
         \x20   return count;\n\
         } }",
        &[
            "_3 = &_1;",
            "_4 = Iterable::iterator(copy _3) -> [return: bb1, unwind continue];",
            "FakeRead(_3);",
            "_5 = Iterator::hasNext(move _6) -> [return: bb2, unwind continue];",
            "_7 = Iterator::next(move _8) -> [return: bb5, unwind continue];",
            "_9 = copy (*_7);",
        ],
    );
}

#[test]
fn closures_capture_what_they_need() {
    assert_builds_to(
        "import std.function.Function;\n\
         import std.function.Supplier;\n\
         class A {\n\
         \x20   static Function<int, int> f(int base, String name) {\n\
         \x20       int calls = 0;\n\
         \x20       return (int value) -> { calls++; return value + base + name.length(); };\n\
         \x20   }\n\
         \x20   static Supplier<String> g(String name) { return move () -> name; }\n\
         }",
        &[
            "_0 = A.f::closure#0 [copy _1, copy _2, move _4];",
            "fn A.f::closure#0(_1: &mut Function<int, int>, _2: int) -> int {",
            "capture base: int;",
            "capture calls: &mut int;",
            "(*(*_1).calls) = Add(copy (*(*_1).calls), const 1_int);",
            "_3 = Add(copy _2, copy (*_1).base);",
            "_0 = A.g::closure#0 [copy _1];",
            "capture name: String;",
        ],
    );
}

#[test]
fn null_checks_do_not_move() {
    assert_builds_to(
        "class A { static int f(String? text) {\n\
         \x20   int? size = text?.length();\n\
         \x20   if (text == null) { return size ?: 0; }\n\
         \x20   return 1;\n\
         } }",
        &[
            "_3 = IsNull(_1);",
            "_4 = &_1;",
            "_2 = String::length(move _4) -> [return: bb3, unwind continue];",
            "_5 = IsNull(_1);",
            "_0 = copy _2;",
        ],
    );
}

#[test]
fn dead_code_is_removed() {
    let printed = build_str(
        "class A { static int f(int x) {\n\
         \x20   try { return x + 1; } finally { x = 0; }\n\
         } }",
    );
    assert!(!printed.contains("caught"), "{printed}");
    assert!(!printed.contains("Throwable"), "{printed}");
    assert!(!printed.contains("goto -> bb"), "{printed}");
}

#[test]
fn every_body_ends_in_a_terminator() {
    let printed = build_str(
        "import std.function.Supplier;\n\
         class A {\n\
         \x20   static final int limit = 3;\n\
         \x20   static Supplier<int> f() { return () -> 1; }\n\
         }",
    );
    assert!(printed.contains("field A.limit() -> int {"), "{printed}");
    assert!(!printed.contains("unreachable"), "{printed}");
}
