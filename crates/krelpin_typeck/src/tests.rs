use std::path::Path;

use krelpin_errors::{DiagCtxt, Diagnostic, DiagnosticBuffer};
use krelpin_parse::{lexer, parser};
use krelpin_span::SourceMap;
use krelpin_sysroot::Sysroot;

fn test_sysroot() -> Sysroot {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    Sysroot::new(root).expect("the workspace is a sysroot")
}

fn diagnostics(src: &str) -> Vec<Diagnostic> {
    check_str(src).1
}

fn check_str(src: &str) -> (crate::TypeckResults, Vec<Diagnostic>, SourceMap) {
    let source_map = SourceMap::new();
    let src = format!("import std.sync.*;\nimport std.util.*;\n{src}");
    let file = source_map.new_source_file("test.kr", src.clone());
    let buffer = DiagnosticBuffer::default();
    let dcx = DiagCtxt::new(buffer.clone());

    let unit = parser::parse(lexer::lex(&file, &dcx), &dcx);
    let mut units = test_sysroot().load_std(&source_map, &dcx);
    units.push(unit);
    krelpin_expand::expand(&mut units, &source_map, &dcx);
    let resolved = krelpin_resolve::resolve(&units, &dcx);
    assert_eq!(
        buffer.messages(),
        Vec::<String>::new(),
        "parse, expansion or resolve errors in {src:?}"
    );

    let results = crate::check(&units, &resolved, &dcx).results;
    (results, buffer.diagnostics(), source_map)
}

fn errors(src: &str) -> Vec<String> {
    diagnostics(src).into_iter().map(|d| d.message).collect()
}

fn labels(src: &str) -> Vec<String> {
    diagnostics(src)
        .into_iter()
        .filter_map(|d| d.label)
        .collect()
}

fn helps(src: &str) -> Vec<String> {
    diagnostics(src)
        .into_iter()
        .flat_map(|d| d.children.into_iter().map(|child| child.message))
        .collect()
}

fn body(code: &str) -> String {
    format!(
        "class Point {{\n\
         \x20   int x;\n\
         \x20   public int y;\n\
         \x20   Point(int x, int y) {{ this.x = x; this.y = y; }}\n\
         \x20   int sum() {{ return this.x + this.y; }}\n\
         \x20   int scaled(int factor) {{ return this.sum() * factor; }}\n\
         }}\n\
         class Main {{\n\
         \x20   void run() {{ {code} }}\n\
         }}"
    )
}

fn in_body(code: &str) -> Vec<String> {
    errors(&body(code))
}

fn ok(src: &str) {
    assert_eq!(
        errors(src),
        Vec::<String>::new(),
        "unexpected errors for {src:?}"
    );
}

fn body_ok(code: &str) {
    ok(&body(code));
}

#[test]
fn hello_world() {
    ok("class Main { static void main() { Console.println(\"Hello World!\"); } }");
}

#[test]
fn literal_and_local_types() {
    body_ok(
        "int a = 1; long b = 2L; double c = 1.5; float d = 1.5f; char e = 'x'; \
             boolean f = true; String g = \"text\"; byte h = 10; long i = a; double j = a;",
    );

    assert_eq!(in_body("int a = \"text\";"), ["mismatched types"]);
    assert_eq!(
        labels(&body("int a = \"text\";")),
        ["expected `int`, found `String`"]
    );
    assert_eq!(in_body("int a = 1L;"), ["mismatched types"]);
    assert_eq!(in_body("boolean b = 1;"), ["mismatched types"]);
}

#[test]
fn null_safety() {
    assert_eq!(in_body("String s = null;"), ["mismatched types"]);
    assert_eq!(
        helps(&body("String s = null;")),
        ["`String` can never be `null`; use `String?` to allow it"]
    );

    body_ok("Point? p = null; int? a = p?.y; int b = p?.sum() ?: 0;");
    assert_eq!(
        in_body("Point? p = null; int a = p.sum();"),
        ["value of type `Point?` may be null"]
    );
    assert_eq!(
        in_body("Point? p = null; int a = p?.sum();"),
        ["mismatched types"]
    );
}

#[test]
fn null_checks_narrow_types() {
    body_ok("Point? p = null; if (p != null) { int a = p.sum(); }");
    body_ok("Point? p = null; if (p == null) { return; } int a = p.sum();");
    body_ok("Point? p = null; boolean big = p != null && p.sum() > 10;");
    body_ok("Point? p = null; boolean empty = p == null || p.sum() == 0;");
    body_ok("Point? p = null; int a = p != null ? p.sum() : 0;");
    body_ok("Point? p = null; if (p == null) { return; } else { int a = p.sum(); }");
    body_ok("while (true) { Point? p = null; if (p == null) { break; } int a = p.sum(); }");
    body_ok("while (true) { Point? p = null; if (p == null) { continue; } int a = p.sum(); }");

    assert_eq!(
        in_body("Point? p = null; if (p != null) { p = null; int a = p.sum(); }"),
        ["value of type `Point?` may be null"]
    );
    assert_eq!(
        in_body("Point? p = null; if (p != null) {} int a = p.sum();"),
        ["value of type `Point?` may be null"]
    );
    assert_eq!(
        in_body(
            "while (true) { Point? p = null; if (p == null) { while (true) { break; } } \
             int a = p.sum(); }"
        ),
        ["value of type `Point?` may be null"]
    );
}

#[test]
fn unnecessary_null_checks_are_warnings() {
    let diagnostics = diagnostics(&body("Point p = new Point(1, 2); int a = p?.sum() ?: 0;"));
    let messages: Vec<String> = diagnostics.iter().map(|d| d.message.clone()).collect();
    assert_eq!(
        messages,
        [
            "unnecessary `?.` on a value that is never null",
            "the left side of `?:` can never be null"
        ]
    );
    assert!(
        diagnostics
            .iter()
            .all(|d| d.level == krelpin_errors::Level::Warning)
    );
}

#[test]
fn fields_and_visibility() {
    body_ok("Point p = new Point(1, 2); int y = p.y;");
    assert_eq!(
        in_body("Point p = new Point(1, 2); int x = p.x;"),
        ["field `x` of `Point` is private"]
    );
    assert_eq!(
        in_body("Point p = new Point(1, 2); int z = p.z;"),
        ["no field `z` on type `Point`"]
    );
    ok("class A { private int secret; int peek(A other) { return other.secret; } }");
}

#[test]
fn private_methods_and_constructors() {
    assert_eq!(
        errors(
            "class A { private void hidden() {} private A() {} }\n\
             class B { void f(A a) { a.hidden(); A b = new A(); } }"
        ),
        [
            "method `hidden` of `A` is private",
            "constructor `A` of `A` is private"
        ]
    );
}

#[test]
fn class_and_instance_members() {
    let src = |code: &str| {
        format!(
            "class Account {{\n\
             \x20   static final int LIMIT = 100;\n\
             \x20   int balance;\n\
             \x20   int total() {{ return this.balance; }}\n\
             \x20   static int limit() {{ return Account.LIMIT; }}\n\
             \x20   void run() {{ {code} }}\n\
             }}"
        )
    };
    ok(&src(
        "int a = Account.LIMIT; int b = this.balance; int c = Account.limit();",
    ));
    assert_eq!(
        errors(&src("int a = Account.balance;")),
        ["`balance` is a field of each object"]
    );
    assert_eq!(
        errors(&src("int a = this.LIMIT;")),
        ["`LIMIT` belongs to the class `Account`"]
    );
    assert_eq!(
        errors(&src("int a = Account.total();")),
        ["method `total` needs an object to be called on"]
    );
    assert_eq!(
        errors(&src("int a = this.limit();")),
        ["`limit` belongs to the class `Account`"]
    );
}

#[test]
fn method_calls() {
    body_ok("Point p = new Point(1, 2); int a = p.scaled(3);");
    assert_eq!(
        in_body("Point p = new Point(1, 2); int a = p.scaled(1, 2);"),
        ["this method takes 1 argument but 2 arguments were supplied"]
    );
    assert_eq!(
        in_body("Point p = new Point(1, 2); int a = p.scaled(\"x\");"),
        ["mismatched types"]
    );
    assert_eq!(
        in_body("Point p = new Point(1, 2); String a = p.sum();"),
        ["mismatched types"]
    );
    assert_eq!(
        in_body("Point p = new Point(1, 2); p.missing();"),
        ["no method named `missing` found for `Point`"]
    );
}

#[test]
fn overloads() {
    ok("class A {\n\
        \x20   int f(int x) { return x; }\n\
        \x20   String f(String s) { return s; }\n\
        \x20   void run() { int a = this.f(1); String b = this.f(\"x\"); }\n\
        }");
    assert_eq!(
        errors(
            "class A {\n\
             \x20   void f(int x) {}\n\
             \x20   void f(String s) {}\n\
             \x20   void run() { this.f(true); }\n\
             }"
        ),
        ["no overload of `f` accepts arguments of type (boolean)"]
    );
}

#[test]
fn varargs() {
    ok("class A {\n\
        \x20   static int sum(int... xs) { return xs.length; }\n\
        \x20   void run() {\n\
        \x20       int a = A.sum();\n\
        \x20       int b = A.sum(1, 2, 3);\n\
        \x20       int[] xs = {1};\n\
        \x20       int c = A.sum(xs);\n\
        \x20   }\n\
        }");
}

#[test]
fn constructors() {
    body_ok("Point p = new Point(1, 2);");
    assert_eq!(
        in_body("Point p = new Point(\"a\", 2);"),
        ["mismatched types"]
    );
    assert_eq!(
        in_body("Point p = new Point(1);"),
        ["this constructor takes 2 arguments but 1 argument was supplied"]
    );
    ok("class A {} class B { static void f() { A a = new A(); } }");
    assert_eq!(
        errors("class A {} class B { static void f() { A a = new A(1); } }"),
        ["`A` has no constructor that takes 1 argument"]
    );
    assert_eq!(
        errors("abstract class A {} class B { static void f() { A a = new A(); } }"),
        ["cannot create an object of an abstract class `A`"]
    );
    assert_eq!(
        errors("interface I {} class B { static void f() { I i = new I(); } }"),
        ["cannot create an object of an interface `I`"]
    );
}

#[test]
fn static_fields_cannot_be_assigned() {
    let src = |code: &str| {
        format!(
            "class Counter {{\n\
             \x20   static final int MAX = 10;\n\
             \x20   static final int count = 0;\n\
             \x20   static final AtomicInt created = new AtomicInt(0);\n\
             \x20   void run() {{ {code} }}\n\
             }}"
        )
    };
    ok(&src(
        "Counter.created.increment(); int a = Counter.count + Counter.MAX;",
    ));
    assert_eq!(
        errors(&src("Counter.count = 1;")),
        ["cannot assign to `static final` field `count`"]
    );
    assert_eq!(
        errors(&src("Counter.count++;")),
        ["cannot assign to `static final` field `count`"]
    );
    assert_eq!(
        errors(&src("Counter.MAX = 2;")),
        ["cannot assign to `static final` field `MAX`"]
    );
}

#[test]
fn final_fields_are_assigned_only_in_constructors() {
    let src = |code: &str| {
        format!(
            "class Account {{\n\
             \x20   final String id;\n\
             \x20   int balance;\n\
             \x20   Account(String id) {{ this.id = id; this.balance = 0; }}\n\
             \x20   mut void run(&mut Account other) {{ {code} }}\n\
             }}"
        )
    };
    ok(&src("this.balance = 5;"));
    assert_eq!(
        errors(&src("this.id = \"other\";")),
        ["cannot assign to `final` field `id`"]
    );
    assert_eq!(
        errors(&src("other.id = \"other\";")),
        ["cannot assign to `final` field `id`"]
    );
    assert_eq!(
        errors("class A { final int x; A(&mut A other) { this.x = 1; other.x = 2; } }"),
        ["cannot assign to `final` field `x`"]
    );
    assert_eq!(
        errors("class A { final int x = 1; void f() { int y = this.x; } }"),
        Vec::<String>::new()
    );
}

#[test]
fn returns() {
    ok("class A { static int f(boolean b) { if (b) { return 1; } else { return 2; } } }");
    ok("class A { static int f() { while (true) {} } }");
    ok("class A { static int f() throws Exception { throw new Exception(); } }");
    ok("class A { static int f() { throw new IllegalStateException(); } }");
    ok("class A { static int f(int x) { switch (x) { \
         case 1 -> { return 1; } default -> { return 2; } } } }");
    assert_eq!(
        errors("class A { static int f(boolean b) { if (b) { return 1; } } }"),
        ["missing return statement"]
    );
    assert_eq!(
        errors("class A { static int f() { while (true) { break; } } }"),
        ["missing return statement"]
    );
    assert_eq!(
        errors("class A { static void f() { return 1; } }"),
        ["cannot return a value from a method that returns `void`"]
    );
    assert_eq!(
        errors("class A { static int f() { return; } }"),
        ["this method must return a `int`"]
    );
    assert_eq!(
        errors("class A { static int f() { return \"x\"; } }"),
        ["mismatched types"]
    );
}

#[test]
fn operators() {
    body_ok(
        "String s = \"n=\" + 1; boolean b = 1 < 2.5; long l = 1 + 2L; int m = 7 % 3; \
             boolean c = true & false; int bits = 1 << 3;",
    );
    assert_eq!(
        in_body("int a = true + 1;"),
        ["cannot apply `+` to `boolean` and `int`"]
    );
    assert_eq!(
        in_body("boolean b = 1 < \"a\";"),
        ["cannot apply `<` to `int` and `String`"]
    );
    assert_eq!(in_body("boolean b = !5;"), ["mismatched types"]);
    assert_eq!(in_body("if (1) {}"), ["mismatched types"]);
    assert_eq!(
        in_body("boolean b = 1 == true;"),
        ["cannot compare `int` with `boolean`"]
    );
}

#[test]
fn switch_expressions() {
    body_ok("int x = 1; String s = switch (x) { case 1 -> \"a\"; default -> { yield \"b\"; } };");
    assert_eq!(
        in_body("int x = 1; Object s = switch (x) { case 1 -> \"a\"; default -> 2; };"),
        ["the cases of this `switch` have incompatible types `String` and `int`"]
    );
    assert_eq!(
        in_body("int x = 1; String s = switch (x) { case 1 -> \"a\"; };"),
        ["this `switch` expression does not cover every case"]
    );

    let enums = |code: &str| {
        format!(
            "enum Color {{ RED, GREEN }}\n\
             class A {{ String f(Color c) {{ return {code}; }} }}"
        )
    };
    ok(&enums(
        "switch (c) { case RED -> \"r\"; case GREEN -> \"g\"; }",
    ));
    assert_eq!(
        errors(&enums("switch (c) { case RED -> \"r\"; }")),
        ["this `switch` expression does not cover every case"]
    );
    assert_eq!(
        errors(&enums(
            "switch (c) { case BLUE -> \"b\"; default -> \"?\"; }"
        )),
        ["no variant `BLUE` in enum `Color`"]
    );
}

#[test]
fn inheritance_and_generics() {
    let src = |code: &str| {
        format!(
            "class Animal {{ String name() {{ return \"animal\"; }} }}\n\
             class Dog extends Animal {{}}\n\
             class Box<T> {{\n\
             \x20   T value;\n\
             \x20   Box(T value) {{ this.value = value; }}\n\
             \x20   T get() {{ return this.value; }}\n\
             }}\n\
             class Main {{ void run() {{ {code} }} }}"
        )
    };
    ok(&src(
        "Dog d = new Dog(); String n = d.name(); Animal a = new Dog();",
    ));
    assert_eq!(errors(&src("Dog d = new Animal();")), ["mismatched types"]);
    ok(&src(
        "Box<String> b = new Box<String>(\"x\"); String s = b.get();",
    ));
    assert_eq!(
        errors(&src(
            "Box<String> b = new Box<String>(\"x\"); int n = b.get();"
        )),
        ["mismatched types"]
    );
    assert_eq!(
        labels(&src(
            "Box<String> b = new Box<String>(\"x\"); int n = b.get();"
        )),
        ["expected `int`, found `String`"]
    );
}

#[test]
fn cyclic_inheritance() {
    assert_eq!(
        errors("class A extends B {} class B extends A {}"),
        ["cyclic inheritance: `A` inherits from itself"]
    );
}

#[test]
fn references() {
    body_ok("String s = \"x\"; &String r = &s; &mut String m = &mut s; &String fromMut = m;");
    body_ok("String s = \"x\"; &String r = s; &int n = 5;");
    assert_eq!(
        in_body("int[] xs = {1}; &int[] r = xs;"),
        ["mismatched types"]
    );
    assert_eq!(
        helps(&body("int[] xs = {1}; &int[] r = xs;")),
        ["borrow the value with `&`"]
    );
    assert_eq!(
        in_body("String s = \"x\"; &mut String m = s;"),
        ["mismatched types"]
    );
    assert_eq!(
        in_body("String s = \"x\"; &mut String m = &s;"),
        ["mismatched types"]
    );
}

#[test]
fn arrays() {
    body_ok(
        "int[] xs = {1, 2}; int x = xs[0]; int n = xs.length; int[] ys = new int[n]; \
             for (int v : xs) { int w = v; }",
    );
    assert_eq!(in_body("int[] xs = {\"a\"};"), ["mismatched types"]);
    assert_eq!(
        in_body("int[] xs = {1}; int x = xs[\"0\"];"),
        ["mismatched types"]
    );
    assert_eq!(
        in_body("int[] xs = {1}; for (String s : xs) {}"),
        ["mismatched types"]
    );
    assert_eq!(
        in_body("int x = 1; int y = x[0];"),
        ["cannot index into a value of type `int`"]
    );
}

#[test]
fn casts() {
    body_ok("double d = 1.5; int i = (int) d; long l = (long) i;");
    assert_eq!(
        in_body("int i = (int) true;"),
        ["cannot cast `boolean` to `int`"]
    );
}

#[test]
fn standard_library_has_no_errors() {
    ok("");
}

#[test]
fn string_methods_are_checked() {
    body_ok(
        "String s = \"Krelpin\"; int n = s.length(); char c = s.chars()[0]; \
         boolean b = s.contains(\"pin\") && !s.isEmpty(); String[] parts = s.split(\",\"); \
         String joined = String.join(\", \", \"a\", \"b\");",
    );
    assert_eq!(
        in_body("String s = \"x\"; int n = s.lenght();"),
        ["no method named `lenght` found for `String`"]
    );
    assert_eq!(
        in_body("String s = \"x\"; String n = s.length();"),
        ["mismatched types"]
    );
    assert_eq!(
        in_body("String s = \"x\"; String part = s.substring(\"0\");"),
        ["mismatched types"]
    );
}

#[test]
fn every_object_has_the_methods_of_object() {
    body_ok("Point p = new Point(1, 2); String text = p.toString(); Object any = p;");
    ok("interface Shape { double area(); }\n\
        class Main { static String f(Shape shape) { return shape.toString(); } }");
    ok("enum Color { RED, GREEN }\n\
        class Main { static String f(Color c) { return c.name() + c.ordinal(); } }");
}

#[test]
fn collections_are_generic() {
    body_ok(
        "List<String> names = new ArrayList<>(); names.add(\"x\"); int n = names.size(); \
         String first = names.get(0); \
         for (String name : names) { Console.println(name.length()); }",
    );
    body_ok(
        "Map<String, int> ages = new HashMap<>(); ages.put(\"Ali\", 30); \
         int? age = ages.get(\"Ali\"); int years = age ?: 0;",
    );
    assert_eq!(
        in_body("List<String> names = new ArrayList<>(); int first = names.get(0);"),
        ["mismatched types"]
    );
    assert_eq!(
        in_body("List<String> names = new ArrayList<>(); names.add(1);"),
        ["mismatched types"]
    );
    assert_eq!(
        in_body("List<String> names = new ArrayList<>(); for (int name : names) {}"),
        ["mismatched types"]
    );
    assert_eq!(
        in_body("Map<String, int> ages = new HashMap<>(); int age = ages.get(\"Ali\");"),
        ["mismatched types"]
    );
    assert_eq!(
        in_body("Map<String, int> ages = new HashMap<>(); for (String key : ages) {}"),
        ["cannot iterate over a value of type `Map<String, int>`"]
    );
    assert_eq!(
        in_body("List<String> names = new ArrayList<>(); String s = names[0];"),
        ["cannot index into a value of type `List<String>`"]
    );
    assert_eq!(
        helps(&body(
            "List<String> names = new ArrayList<>(); String s = names[0];"
        )),
        ["use `.get(index)` instead"]
    );
}

#[test]
fn own_types_can_be_iterable() {
    ok("abstract class Countdown implements Iterable<int> {}\n\
        class Main {\n\
        \x20   void run(Countdown countdown) {\n\
        \x20       for (int n : countdown) { int x = n; }\n\
        \x20   }\n\
        }");
}

#[test]
fn primitives_are_the_only_number_types() {
    body_ok(
        "List<int> xs = new ArrayList<>(); xs.add(5); int first = xs.get(0); \
         Map<String, int> ages = new HashMap<>(); int? age = ages.get(\"Ali\"); \
         int? missing = null; Object any = 5; Comparable<int> order = 5;",
    );
    assert_eq!(
        errors("import std.primitive.Int; class A { Int x; }"),
        ["`Int` is not a type"]
    );
    assert_eq!(
        helps("import std.primitive.Int; class A { Int x; }"),
        ["use `int` instead"]
    );
    assert_eq!(
        in_body("int? maybe = null; int x = maybe;"),
        ["mismatched types"]
    );
}

#[test]
fn primitives_have_members() {
    body_ok(
        "int big = int.MAX_VALUE; long small = long.MIN_VALUE; int parsed = int.parse(\"42\"); \
         int order = 5.compareTo(&6); String text = 5.toString(); boolean digit = 'x'.isDigit();",
    );
    assert_eq!(
        in_body("int x = 5; int n = x.lenght();"),
        ["no method named `lenght` found for `int`"]
    );
    assert_eq!(in_body("int n = int.parse(5);"), ["mismatched types"]);
    assert_eq!(
        in_body("int n = 5.parse(\"5\");"),
        ["`parse` belongs to the class `int`"]
    );
}

#[test]
fn class_members_of_the_standard_library() {
    body_ok(
        "int a = Math.max(1, 2); long b = Math.max(1L, 2); double c = Math.sqrt(2.0) * Math.PI; \
         int big = int.MAX_VALUE; int parsed = int.parse(\"42\");",
    );
    assert_eq!(in_body("int a = Math.sqrt(2.0);"), ["mismatched types"]);
    assert_eq!(
        in_body("Console c = new Console();"),
        ["constructor `Console` of `Console` is private"]
    );
    assert_eq!(
        in_body("Math.PI = 3.0;"),
        ["cannot assign to `static final` field `PI`"]
    );
}

#[test]
fn console_prints_values_and_borrows() {
    body_ok(
        "Console.println(); Console.println(1); Console.println(2L); Console.println('c'); \
         Console.println(true); Console.println(1.5); Console.println(\"text\"); \
         Console.println(new Point(1, 2)); String s = \"x\"; Console.println(&s); \
         String? maybe = null; Console.print(maybe); String? line = Console.readLine();",
    );
    assert_eq!(
        in_body("String line = Console.readLine();"),
        ["mismatched types"]
    );
    assert_eq!(
        in_body("Console.print(null);"),
        ["call to `print` is ambiguous"]
    );
}

#[test]
fn exceptions() {
    body_ok(
        "try { throw new IllegalArgumentException(\"bad\"); } \
         catch (RuntimeException e) { String? message = e.getMessage(); }",
    );
    assert_eq!(
        in_body("try {} catch (Exception e) { String message = e.getMessage(); }"),
        ["mismatched types"]
    );
    ok("import std.io.IOException;\n\
        class Main { void run() throws IOException { throw new IOException(\"disk\"); } }");
}

#[test]
fn atomics_can_change_through_static_fields() {
    ok("class Counter {\n\
        \x20   static final AtomicInt created = new AtomicInt(0);\n\
        \x20   Counter() { int id = Counter.created.increment(); }\n\
        }");
    assert_eq!(
        errors("class Counter { static final AtomicInt created = new AtomicInt(\"0\"); }"),
        ["mismatched types"]
    );
}

#[test]
fn generic_arguments_are_counted() {
    assert_eq!(
        errors("class A { List<String, int>? xs; }"),
        ["`List` takes 1 type argument but 2 were supplied"]
    );
    assert_eq!(
        errors("class A { String<int>? s; }"),
        ["`String` takes 0 type arguments but 1 was supplied"]
    );
    assert_eq!(
        errors("class A<T> { T<String>? x; }"),
        ["type parameter `T` does not take type arguments"]
    );
    assert_eq!(
        in_body("Map<String>? ages = null;"),
        ["`Map` takes 2 type arguments but 1 was supplied"]
    );
}

#[test]
fn generic_arguments_satisfy_bounds() {
    let src = |code: &str| {
        format!(
            "class Sorted<T extends Comparable<T>> {{}}\n\
             class Thing {{}}\n\
             class Main {{ void run() {{ {code} }} }}"
        )
    };
    ok(&src(
        "Sorted<String>? s = null; Sorted<int>? i = new Sorted<>();",
    ));
    assert_eq!(
        errors(&src("Sorted<Thing>? s = null;")),
        ["type `Thing` does not satisfy the bound of `T`"]
    );
    assert_eq!(
        labels(&src("Sorted<Thing>? s = null;")),
        ["`Thing` is not a `Comparable<Thing>`"]
    );
}

#[test]
fn type_parameters_have_the_methods_of_their_bounds() {
    ok("class Max {\n\
        \x20   static <T extends Comparable<T>> T max(T a, T b) {\n\
        \x20       return a.compareTo(&b) >= 0 ? a : b;\n\
        \x20   }\n\
        }");
    ok("class Show<T> { String show(T value) { return value.toString(); } }");
    ok("class View<T extends Comparable<T>> {\n\
        \x20   Comparable<T> view(T value) { return value; }\n\
        }");
    assert_eq!(
        errors("class Show<T> { int size(T value) { return value.length(); } }"),
        ["no method named `length` found for `T`"]
    );
    assert_eq!(
        errors("class View<T> { Comparable<T> view(T value) { return value; } }"),
        ["mismatched types"]
    );
}

fn pick(code: &str) -> String {
    format!(
        "class Pick {{\n\
         \x20   static int f(long x) {{ return 1; }}\n\
         \x20   static String f(int x) {{ return \"\"; }}\n\
         \x20   static boolean g(Object? x) {{ return true; }}\n\
         \x20   static char g(String? x) {{ return 'c'; }}\n\
         \x20   static int v(String... xs) {{ return 0; }}\n\
         \x20   static String v(String x) {{ return x; }}\n\
         \x20   static void amb(int a, long b) {{}}\n\
         \x20   static void amb(long a, int b) {{}}\n\
         }}\n\
         class Main {{ void run() {{ {code} }} }}"
    )
}

#[test]
fn the_most_specific_overload_is_chosen() {
    ok(&pick(
        "String a = Pick.f(1); int b = Pick.f(1L); char c = Pick.g(\"x\"); \
         boolean d = Pick.g(new Pick());",
    ));
    assert_eq!(errors(&pick("int a = Pick.f(1);")), ["mismatched types"]);
    assert_eq!(
        errors(&pick("char d = Pick.g(new Pick());")),
        ["mismatched types"]
    );
}

#[test]
fn variadic_methods_are_the_last_resort() {
    ok(&pick(
        "String a = Pick.v(\"x\"); int b = Pick.v(\"x\", \"y\"); int c = Pick.v();",
    ));
}

#[test]
fn ambiguous_calls() {
    assert_eq!(
        errors(&pick("Pick.amb(1, 2);")),
        ["call to `amb` is ambiguous"]
    );
    assert_eq!(
        helps(&pick("Pick.amb(1, 2);")),
        [
            "it could call `Pick.amb(int, long)` or `Pick.amb(long, int)`",
            "cast the arguments to the types of the method you want to call",
        ]
    );
}

fn util(code: &str) -> String {
    format!(
        "class Util {{\n\
         \x20   static <T> &T first(&List<T> xs) {{ return xs.get(0); }}\n\
         \x20   static <T> T either(T a, T b) {{ return a; }}\n\
         \x20   static <T extends Comparable<T>> T max(T a, T b) {{\n\
         \x20       return a.compareTo(&b) >= 0 ? a : b;\n\
         \x20   }}\n\
         \x20   static <T> List<T> listOf(T... xs) {{ return new ArrayList<>(); }}\n\
         }}\n\
         class Thing {{}}\n\
         class Main {{ void run() {{ {code} }} }}"
    )
}

#[test]
fn generic_methods_infer_their_type_arguments() {
    ok(&util(
        "List<String> names = new ArrayList<>(); String s = Util.first(&names); \
         int i = Util.either(1, 2); String m = Util.max(\"a\", \"b\"); \
         List<String> xs = Util.listOf(\"a\", \"b\");",
    ));
    assert_eq!(
        errors(&util(
            "List<String> names = new ArrayList<>(); int n = Util.first(&names);"
        )),
        ["mismatched types"]
    );
    assert_eq!(
        labels(&util("List<int> xs = Util.listOf(\"a\");")),
        ["expected `List<int>`, found `List<String>`"]
    );
    assert_eq!(
        errors(&util("Object o = Util.either(\"a\", 1);")),
        ["mismatched types"]
    );
}

#[test]
fn inferred_type_arguments_satisfy_bounds() {
    assert_eq!(
        errors(&util("Thing t = Util.max(new Thing(), new Thing());")),
        ["type `Thing` does not satisfy the bound of `T`"]
    );
}

fn closures(code: &str) -> String {
    format!(
        "import std.function.Consumer;\n\
         interface Mapper<A, B> {{ B apply(A value); }}\n\
         class Thing {{ Thing(String name) {{}} }}\n\
         class Exec {{\n\
         \x20   static int run(Runnable task) {{ return 0; }}\n\
         \x20   static String run(Consumer<String> action) {{ return \"\"; }}\n\
         }}\n\
         class Main {{\n\
         \x20   int helper(String s) {{ return 1; }}\n\
         \x20   void run() {{ {code} }}\n\
         }}"
    )
}

#[test]
fn lambdas_take_the_types_of_their_target() {
    ok(&closures(
        "Runnable r = () -> Console.println(\"x\"); \
         Consumer<String> c = s -> Console.println(s.length()); \
         Mapper<String, int> m = s -> s.length(); \
         Mapper<String, int> b = (String s) -> { return s.length(); }; \
         List<String> names = new ArrayList<>(); \
         names.forEach(name -> Console.println(name.length()));",
    ));
    assert_eq!(
        errors(&closures("Mapper<String, int> m = s -> s.lenght();")),
        ["no method named `lenght` found for `String`"]
    );
    assert_eq!(
        errors(&closures(
            "List<String> names = new ArrayList<>(); names.forEach(name -> name.lenght());"
        )),
        ["no method named `lenght` found for `String`"]
    );
    assert_eq!(
        labels(&closures("Mapper<String, int> m = s -> s;")),
        ["expected `int`, found `String`"]
    );
}

#[test]
fn lambda_errors() {
    assert_eq!(
        errors(&closures("Mapper<String, int> m = (a, b) -> 1;")),
        ["this lambda takes 2 parameters but `apply` takes 1 parameter"]
    );
    assert_eq!(
        labels(&closures("Mapper<String, int> m = (int s) -> 1;")),
        ["expected `String`, found `int`"]
    );
    assert_eq!(
        errors(&closures(
            "Mapper<String, int> m = s -> { Console.println(s); };"
        )),
        ["missing return statement"]
    );
    assert_eq!(
        errors(&closures("String s = () -> 1;")),
        ["a lambda cannot be used as `String`"]
    );
}

#[test]
fn lambdas_choose_overloads_by_their_parameters() {
    ok(&closures(
        "int a = Exec.run(() -> {}); String b = Exec.run(s -> Console.println(s.length()));",
    ));
}

#[test]
fn method_references() {
    ok(&closures(
        "Mapper<String, int> len = String::length; \
         Mapper<String, int> parse = int::parse; \
         Consumer<String> print = Console::println; \
         Mapper<String, Thing> make = Thing::new; \
         Mapper<String, int> own = this::helper;",
    ));
    assert_eq!(
        errors(&closures("Mapper<String, int> size = String::size;")),
        ["`String::size` does not match `Mapper<String, int>`"]
    );
    assert_eq!(
        labels(&closures("Mapper<String, String> len = String::length;")),
        ["expected `String`, found `int`"]
    );
}

fn shapes(code: &str) -> String {
    format!(
        "interface Shape {{\n\
         \x20   double area();\n\
         \x20   String name() {{ return \"shape\"; }}\n\
         }}\n\
         interface Box<T> {{ T get(); }}\n\
         {code}"
    )
}

#[test]
fn abstract_methods_are_implemented() {
    ok(&shapes(
        "class Circle implements Shape { double area() { return 3.14; } }",
    ));
    ok(&shapes("abstract class Base implements Shape {}"));
    ok(&shapes(
        "class Base { double area() { return 1.0; } }\n\
         class Square extends Base implements Shape {}",
    ));
    ok(&shapes(
        "class IntBox implements Box<int> { int get() { return 1; } }",
    ));

    let src = shapes("class Square implements Shape {}");
    assert_eq!(
        errors(&src),
        ["`Square` does not implement every method of `Shape`"]
    );
    assert_eq!(
        helps(&src),
        [
            "missing: `double area()`",
            "implement the missing methods, or mark `Square` as `abstract`",
        ]
    );
    assert_eq!(
        helps(&shapes("record Point(int x) implements Shape {}")),
        ["missing: `double area()`", "implement the missing methods"]
    );
    assert_eq!(
        errors(&shapes("enum Kind implements Shape { ROUND }")),
        ["`Kind` does not implement every method of `Shape`"]
    );
    assert_eq!(
        errors("class A { abstract void f(); }"),
        ["`A` is not abstract but declares abstract methods"]
    );
}

fn base(code: &str) -> String {
    format!(
        "class Base {{\n\
         \x20   void f() {{}}\n\
         \x20   final void g() {{}}\n\
         \x20   public void h() {{}}\n\
         \x20   Base copy() {{ return new Base(); }}\n\
         }}\n\
         {code}"
    )
}

#[test]
fn overrides_keep_the_signature() {
    ok(&base(
        "class A extends Base {\n\
         \x20   void f() {}\n\
         \x20   mut void f(int x) {}\n\
         \x20   A copy() { return new A(); }\n\
         \x20   String toString() { return \"a\"; }\n\
         }",
    ));
    assert_eq!(
        errors(&base("class A extends Base { mut void f() {} }")),
        ["`f` is `mut` but `Base.f` only reads the object"]
    );
    assert_eq!(
        errors(&base("class A extends Base { static void f() {} }")),
        ["`f` is `static` but `Base.f` only reads the object"]
    );
    assert_eq!(
        errors(&base("class A extends Base { void g() {} }")),
        ["cannot override `Base.g` because it is `final`"]
    );
    assert_eq!(
        errors(&base("class A extends Base { private void h() {} }")),
        ["`h` cannot be less visible than `Base.h`"]
    );
    assert_eq!(
        errors(&base("class A extends Base { int f() { return 1; } }")),
        ["`f` returns `int` but `Base.f` returns `void`"]
    );
    assert_eq!(
        errors(&base(
            "class A extends Base { String copy() { return \"\"; } }"
        )),
        ["`copy` returns `String` but `Base.copy` returns `Base`"]
    );
    assert_eq!(
        errors("class A { int toString() { return 1; } }"),
        ["`toString` returns `int` but `Object.toString` returns `String`"]
    );
    assert_eq!(
        errors(&shapes(
            "class StrBox implements Box<String> { int get() { return 1; } }"
        )),
        ["`get` returns `int` but `Box.get` returns `String`"]
    );
}

#[test]
fn parents_have_the_right_kind() {
    assert_eq!(
        errors("interface I {} class A extends I {}"),
        ["a class cannot extend an interface"]
    );
    assert_eq!(
        helps("interface I {} class A extends I {}"),
        ["use `implements I` instead"]
    );
    assert_eq!(
        errors("class B {} class A implements B {}"),
        ["`B` is not an interface"]
    );
    assert_eq!(
        helps("class B {} class A implements B {}"),
        ["use `extends B` instead"]
    );
    assert_eq!(
        errors("class B {} interface I extends B {}"),
        ["an interface can only extend interfaces"]
    );
    assert_eq!(
        errors("record S(int x) {} class A extends S {}"),
        ["a class can only extend another class"]
    );
    assert_eq!(
        errors("final class F {} class A extends F {}"),
        ["cannot extend `F` because it is `final`"]
    );
    assert_eq!(
        errors("class A extends String {}"),
        ["cannot extend `String` because it is `final`"]
    );
    assert_eq!(
        errors("interface I { void f(); } class A extends I {}"),
        ["a class cannot extend an interface"]
    );
}

#[test]
fn only_throwables_are_thrown_and_caught() {
    body_ok("throw new IllegalStateException(\"broken\");");
    assert_eq!(
        in_body("throw \"oops\";"),
        ["cannot throw a value of type `String`"]
    );
    assert_eq!(
        in_body("RuntimeException? error = null; throw error;"),
        ["cannot throw a value of type `RuntimeException?`"]
    );
    assert_eq!(
        errors("class A { static void f() throws String {} }"),
        ["`String` is not a `Throwable`"]
    );
    assert_eq!(
        in_body("try {} catch (String s) {}"),
        ["`String` cannot be caught"]
    );
}

#[test]
fn multi_catch_binds_the_common_superclass() {
    body_ok(
        "try {} catch (IllegalArgumentException | IllegalStateException e) { \
         RuntimeException r = e; String? message = e.getMessage(); }",
    );
    assert_eq!(
        in_body(
            "try {} catch (IllegalArgumentException | IllegalStateException e) { \
             IllegalStateException s = e; }"
        ),
        ["mismatched types"]
    );
    assert_eq!(
        in_body("try {} catch (RuntimeException | IllegalStateException e) {}"),
        ["`IllegalStateException` and `RuntimeException` overlap in this `catch`"]
    );
}

#[test]
fn exceptions_are_caught_only_once() {
    body_ok("try {} catch (RuntimeException e) {} catch (Exception e) {}");
    let code = "try {} catch (Exception e) {} catch (RuntimeException e) {}";
    assert_eq!(
        in_body(code),
        ["`RuntimeException` has already been caught"]
    );
    assert_eq!(
        labels(&body(code)),
        ["already caught by the `catch` for `Exception`"]
    );
}

fn files(code: &str) -> String {
    format!(
        "import std.io.IOException;\n\
         class Files {{\n\
         \x20   static String read(String path) throws IOException {{ return path; }}\n\
         \x20   static void write(String text) {{}}\n\
         }}\n\
         interface Source {{ String next() throws IOException; }}\n\
         class Main {{\n\
         \x20   {code}\n\
         }}"
    )
}

#[test]
fn checked_exceptions_are_caught_or_declared() {
    ok(&files(
        "void run() throws IOException { String text = Files.read(\"a\"); }",
    ));
    ok(&files("void run() throws Exception { Files.read(\"a\"); }"));
    ok(&files(
        "void run() { try { Files.read(\"a\"); } catch (IOException e) {} }",
    ));
    ok(&files(
        "void run() { try { Files.read(\"a\"); } catch (Exception e) {} }",
    ));
    ok(&files(
        "void run() { throw new IllegalArgumentException(\"bad\"); }",
    ));

    let src = files("void run() { Files.read(\"a\"); }");
    assert_eq!(errors(&src), ["unreported exception `IOException`"]);
    assert_eq!(
        helps(&src),
        [
            "checked exceptions must be caught or declared with `throws`",
            "catch it with `try`, or add `throws IOException` to the method",
        ]
    );
    assert_eq!(
        errors(&files("void run() { throw new IOException(\"disk\"); }")),
        ["unreported exception `IOException`"]
    );
    assert_eq!(
        errors(&files(
            "void run() { try { Files.read(\"a\"); } catch (RuntimeException e) {} }"
        )),
        ["unreported exception `IOException`"]
    );
}

#[test]
fn exceptions_thrown_in_catch_blocks_are_not_caught_by_them() {
    assert_eq!(
        errors(&files(
            "void run() { \
             try { Files.read(\"a\"); } catch (IOException e) { Files.read(\"b\"); } }"
        )),
        ["unreported exception `IOException`"]
    );
    ok(&files(
        "void run() { try { try { Files.read(\"a\"); } finally {} } \
         catch (IOException e) {} }",
    ));
}

#[test]
fn lambdas_cannot_throw_checked_exceptions_their_method_does_not() {
    let src = files(
        "void run() throws IOException { \
         List<String> paths = new ArrayList<>(); \
         paths.forEach(path -> Files.read(path)); }",
    );
    assert_eq!(errors(&src), ["unreported exception `IOException`"]);
    assert_eq!(
        helps(&src)[1],
        "catch it inside the lambda, because `accept` cannot throw it"
    );
    ok(&files("void run() { Source s = () -> Files.read(\"a\"); }"));
}

#[test]
fn constructors_declare_their_exceptions() {
    ok("import std.io.IOException;\n\
        class Conn { Conn() throws IOException {} }\n\
        class Main { void run() throws IOException { Conn c = new Conn(); } }");
    assert_eq!(
        errors(
            "import std.io.IOException;\n\
             class Conn { Conn() throws IOException {} }\n\
             class Main { void run() { Conn c = new Conn(); } }"
        ),
        ["unreported exception `IOException`"]
    );
}

#[test]
fn catching_checked_exceptions_that_are_never_thrown() {
    assert_eq!(
        errors(&files(
            "void run() { try { Files.write(\"a\"); } catch (IOException e) {} }"
        )),
        ["`IOException` is never thrown in the body of this `try`"]
    );
    ok(&files(
        "void run() { try { Files.write(\"a\"); } catch (Exception e) {} }",
    ));
    ok(&files(
        "void run() { try { Files.write(\"a\"); } catch (IllegalStateException e) {} }",
    ));
}

#[test]
fn overrides_cannot_throw_more() {
    let src = |code: &str| {
        format!(
            "import std.io.IOException;\n\
             class Base {{ void f() {{}} void g() throws Exception {{}} }}\n\
             {code}"
        )
    };
    ok(&src(
        "class A extends Base { void g() throws IOException {} \
         void f() throws IllegalStateException {} }",
    ));
    assert_eq!(
        errors(&src(
            "class A extends Base { void f() throws IOException {} }"
        )),
        ["`f` cannot throw `IOException` because `Base.f` does not"]
    );
}

fn bag(code: &str) -> String {
    format!(
        "class Bag<T> {{\n\
         \x20   T first;\n\
         \x20   Bag(T first) {{ this.first = first; }}\n\
         \x20   boolean isSmall(T limit) where T extends Comparable<T> {{\n\
         \x20       return this.first.compareTo(&limit) < 0;\n\
         \x20   }}\n\
         }}\n\
         class Thing {{}}\n\
         class Main {{ void run() {{ {code} }} }}"
    )
}

#[test]
fn where_clauses_are_checked_at_the_call() {
    ok(&bag(
        "Bag<String> words = new Bag<String>(\"a\"); boolean small = words.isSmall(\"b\");",
    ));
    ok(&bag("Bag<Thing> things = new Bag<Thing>(new Thing());"));
    assert_eq!(
        errors(&bag(
            "Bag<Thing> things = new Bag<Thing>(new Thing()); things.isSmall(new Thing());"
        )),
        ["type `Thing` does not satisfy the bound of `T`"]
    );
    assert_eq!(
        errors(
            "class Bag<T> { T first; Bag(T first) { this.first = first; } boolean bad(T other) { \
             return this.first.compareTo(&other) < 0; } }"
        ),
        ["no method named `compareTo` found for `T`"]
    );
}

fn points(code: &str) -> String {
    format!(
        "class Point implements Hashable<Point> {{\n\
         \x20   int x;\n\
         \x20   Point(int x) {{ this.x = x; }}\n\
         \x20   boolean equals(&Point other) {{ return this.x == other.x; }}\n\
         \x20   int hashCode() {{ return this.x; }}\n\
         }}\n\
         class Thing {{}}\n\
         enum Color {{ RED, GREEN }}\n\
         class Main {{ void run() {{ {code} }} }}"
    )
}

#[test]
fn equality_needs_equatable() {
    ok(&points(
        "Point a = new Point(1); Point b = new Point(2); boolean same = a == b; \
         boolean text = \"a\" != \"b\"; boolean number = 1 == 1L; \
         boolean color = Color.RED == Color.GREEN; Point? maybe = null; \
         boolean missing = maybe == null; boolean found = maybe == a;",
    ));
    let src = points("Thing a = new Thing(); boolean same = a == new Thing();");
    assert_eq!(
        errors(&src),
        ["values of type `Thing` cannot be compared with `==`"]
    );
    assert_eq!(helps(&src), ["implement `Equatable<Thing>` for `Thing`"]);
    assert_eq!(
        errors(&points("boolean wrong = \"a\" == 1;")),
        ["cannot compare `String` with `int`"]
    );
    assert_eq!(
        errors(&points("int x = 1; boolean wrong = x == null;")),
        ["cannot compare `int` with `null`"]
    );
}

#[test]
fn generic_equality_needs_a_bound() {
    ok("class Box<T extends Equatable<T>> { boolean same(T a, T b) { return a == b; } }");
    let src = "class Box<T> { boolean same(T a, T b) { return a == b; } }";
    assert_eq!(
        errors(src),
        ["values of type `T` cannot be compared with `==`"]
    );
    assert_eq!(helps(src), ["add the bound `T extends Equatable<T>`"]);
}

#[test]
fn hash_collections_need_hashable_keys() {
    ok(&points(
        "Map<Point, String> names = new HashMap<Point, String>(); \
         Set<Color> colors = new HashSet<Color>(); Set<String> words = new HashSet<String>();",
    ));
    assert_eq!(
        errors(&points(
            "Map<Thing, int> counts = new HashMap<Thing, int>();"
        )),
        ["type `Thing` does not satisfy the bound of `K`"]
    );
}

#[test]
fn list_lookups_need_equatable_elements() {
    ok(&points(
        "List<Point> points = new ArrayList<>(); Point p = new Point(1); \
         boolean has = points.contains(&p);",
    ));
    assert_eq!(
        errors(&points(
            "List<Thing> things = new ArrayList<>(); Thing t = new Thing(); things.contains(&t);"
        )),
        ["type `Thing` does not satisfy the bound of `T`"]
    );
}

#[test]
fn chars_are_unicode_scalars() {
    body_ok(
        "char smile = '😀'; char last = char.MAX_VALUE; int code = smile; \
         char[] letters = \"Ayşe 😀\".chars(); boolean letter = letters[2].isLetter();",
    );
    body_ok("String s = \"x\"; char c = s.charAt(0);");
    assert_eq!(
        in_body("String s = \"x\"; String c = s.charAt(0);"),
        ["mismatched types"]
    );
}

#[test]
fn only_lossless_conversions_are_implicit() {
    body_ok(
        "byte b = 1; short s = b; int i = s; long l = i; double d = i; float f = 1.5f; \
         double e = f; float literal = 1; char c = 'x'; int code = c; \
         double mixed = i + f; float narrowed = (float) i; double wide = (double) l;",
    );
    assert_eq!(in_body("int i = 1; float f = i;"), ["mismatched types"]);
    assert_eq!(in_body("long l = 1L; double d = l;"), ["mismatched types"]);
    assert_eq!(in_body("long l = 1L; float f = l;"), ["mismatched types"]);
    assert_eq!(
        in_body("int i = 1; float f = 1.5f; float sum = i + f;"),
        ["mismatched types"]
    );
    assert_eq!(
        in_body("long l = 1L; double d = 1.5; double sum = l * d;"),
        ["cannot apply `*` to `long` and `double`"]
    );
}

#[test]
fn enum_variants_carry_data() {
    let src = |code: &str| {
        format!(
            "enum Shape {{\n\
             \x20   Circle(double radius),\n\
             \x20   Rect(double width, double height),\n\
             \x20   Empty;\n\
             \x20   Shape unit() {{ return Circle(1.0); }}\n\
             }}\n\
             enum Tree<T> {{ Leaf(T value), Node(Tree<T> left, Tree<T> right), Empty }}\n\
             class Main {{ void run() {{ {code} }} }}"
        )
    };
    ok(&src(
        "Shape a = Shape.Circle(2.0); Shape b = Shape.Rect(1, 2.0); Shape c = Shape.Empty; \
         Tree<String> s = Tree.Leaf(\"x\"); Tree<int> n = Tree.Empty; \
         String name = a.name(); int index = c.ordinal();",
    ));
    assert_eq!(
        errors(&src("Shape a = Shape.Circle(\"x\");")),
        ["mismatched types"]
    );
    assert_eq!(
        errors(&src("Tree<String> s = Tree.Leaf(5);")),
        ["mismatched types"]
    );
    assert_eq!(
        errors(&src("Shape a = Shape.Rect(1.0);")),
        ["this variant takes 2 arguments but 1 argument was supplied"]
    );
    assert_eq!(
        errors(&src("Shape a = Shape.Circle;")),
        ["the variant `Shape.Circle` has fields"]
    );
    assert_eq!(
        errors(&src("Shape a = Shape.Empty();")),
        ["the variant `Shape.Empty` has no fields"]
    );
}

#[test]
fn only_enums_without_data_are_ordered() {
    let src = |code: &str| {
        format!(
            "enum Color {{ RED, GREEN }}\n\
             enum Shape {{ Circle(double radius), Empty }}\n\
             class Main {{ void run() {{ {code} }} }}"
        )
    };
    ok(&src(
        "Color[] all = Color.values(); boolean same = Color.RED == Color.GREEN; \
         HashSet<Color> colors = new HashSet<>();",
    ));
    ok(&src(
        "boolean same = Shape.Empty == Shape.Empty; int order = Color.RED.compareTo(&Color.GREEN);",
    ));
    assert_eq!(
        errors(&src("int order = Shape.Empty.compareTo(&Shape.Empty);")),
        ["no method named `compareTo` found for `Shape`"]
    );
    assert_eq!(
        errors(&src("Shape[] all = Shape.values();")),
        ["no method named `values` found for `Shape`"]
    );
}

fn variants(code: &str) -> String {
    format!(
        "enum Shape {{\n\
         \x20   Circle(double radius),\n\
         \x20   Rect(double width, double height),\n\
         \x20   Empty;\n\
         }}\n\
         enum Tree<T> {{ Leaf(T value), Node(Tree<T> left, Tree<T> right), Empty }}\n\
         class Main {{ {code} }}"
    )
}

#[test]
fn patterns_destructure_variants() {
    ok(&variants(
        "static double area(Shape shape) {\n\
         \x20   return switch (shape) {\n\
         \x20       case Circle(double r) -> 3.14 * r * r;\n\
         \x20       case Rect(double w, double h) when w == h -> w * w;\n\
         \x20       case Shape.Rect(double w, double h) -> w * h;\n\
         \x20       case Empty -> 0.0;\n\
         \x20   };\n\
         }\n\
         static boolean round(Tree<Shape> tree) {\n\
         \x20   return tree instanceof Leaf(Circle(_));\n\
         }\n\
         static String first(Tree<String> tree) {\n\
         \x20   if (tree instanceof Leaf(String value) && value.length() > 0) {\n\
         \x20       return value;\n\
         \x20   }\n\
         \x20   return \"\";\n\
         }",
    ));
    assert_eq!(
        errors(&variants(
            "static double f(Shape s) { return switch (s) { \
             case Circle(int r) -> 1.0; default -> 0.0; }; }"
        )),
        ["mismatched types"]
    );
    assert_eq!(
        errors(&variants(
            "static int f(Shape s) { return switch (s) { case Rect(double w) -> 1; default -> \
             0; }; }"
        )),
        ["this pattern has 1 field, but the variant `Shape.Rect` has 2 fields"]
    );
    assert_eq!(
        errors(&variants(
            "static int f(Shape s) { return switch (s) { case Circle -> 1; default -> 0; }; }"
        )),
        ["the variant `Shape.Circle` has fields"]
    );
    assert_eq!(
        errors(&variants(
            "static int f(Shape s) { return switch (s) { case Empty(_) -> 1; default -> 0; }; }"
        )),
        ["the variant `Shape.Empty` has no fields"]
    );
    assert_eq!(
        errors(&variants(
            "static int f(Shape s) { return switch (s) { case Square -> 1; default -> 0; }; }"
        )),
        ["no variant `Square` in enum `Shape`"]
    );
    assert_eq!(
        errors(&variants(
            "static int f(Object o) { return switch (o) { case Main(int x) -> 1; default -> 0; }; }"
        )),
        ["`Main` is not an enum variant or a record"]
    );
}

#[test]
fn switches_on_enums_cover_every_case() {
    let notes = |code: &str| -> Vec<String> {
        diagnostics(&variants(code))
            .into_iter()
            .flat_map(|d| d.children.into_iter().map(|child| child.message))
            .filter(|message| message.starts_with("not covered"))
            .collect()
    };
    assert_eq!(
        notes("static int f(Shape s) { return switch (s) { case Circle(_) -> 1; }; }"),
        ["not covered: `Rect(_, _)` and `Empty`"]
    );
    assert_eq!(
        notes(
            "static int f(Tree<Shape> t) { return switch (t) { \
             case Leaf(Circle(_)) -> 1; case Node(_, _), Empty -> 0; }; }"
        ),
        ["not covered: `Leaf(Rect(_, _))` and `Leaf(Empty)`"]
    );
    assert_eq!(
        notes(
            "static int f(Shape s) { return switch (s) { case Circle(_) -> 1; \
             case Rect(_, _) when true -> 2; case Empty -> 3; }; }"
        ),
        ["not covered: `Rect(_, _)`"]
    );
    assert_eq!(
        notes("static int f(boolean b) { return switch (b) { case true -> 1; }; }"),
        ["not covered: `false`"]
    );
    assert_eq!(
        errors(&variants(
            "static void f(Shape s) { switch (s) { case Empty -> {} } }"
        )),
        ["this `switch` statement does not cover every case"]
    );
    ok(&variants(
        "static void f(Shape s, int n) { switch (n) { case 1 -> {} } switch (s) { default -> \
         {} } }",
    ));
    ok(&variants(
        "static int f(Shape s) { switch (s) { case Circle(_) -> { return 1; } \
         case Rect(_, _) -> { return 2; } case Empty -> { return 3; } } }",
    ));
}

#[test]
fn unreachable_patterns_are_reported() {
    assert_eq!(
        errors(&variants(
            "static int f(Shape s) { return switch (s) { case Circle(_) -> 1; default -> 0; \
             case Empty -> 2; }; }"
        )),
        ["unreachable pattern"]
    );
    assert_eq!(
        errors(&variants(
            "static int f(int n) { return switch (n) { case 1, 2 -> 1; case 1 -> 2; default -> \
             0; }; }"
        )),
        ["unreachable pattern"]
    );
    assert_eq!(
        errors(&variants(
            "static int f(Object o) { return switch (o) { case Object any -> 1; case String s \
             -> 2; }; }"
        )),
        ["unreachable pattern"]
    );
    ok(&variants(
        "static int f(Object o) { return switch (o) { case String s -> 1; case Object any -> \
         2; }; }",
    ));
}

#[test]
fn enums_with_data_are_compared_by_value() {
    ok("record Point(int x, String? label);\n\
        enum Shape { Circle(Point center, double radius), Empty }\n\
        class Main {\n\
        \x20   boolean run() {\n\
        \x20       HashMap<Shape, String> names = new HashMap<>();\n\
        \x20       names.put(Shape.Circle(new Point(1, null), 2.0), \"circle\");\n\
        \x20       Shape copy = Shape.Empty.clone();\n\
        \x20       return Shape.Empty == copy;\n\
        \x20   }\n\
        }");
    assert_eq!(
        errors(
            "class Handle {}\n\
             enum Slot { Held(Handle handle), Free }\n\
             class Main { boolean run() { return Slot.Free == Slot.Free; } }"
        ),
        ["values of type `Slot` cannot be compared with `==`"]
    );
}

#[test]
fn records_are_built_from_their_components() {
    let src = |code: &str| {
        format!(
            "record Version(int major, String tag);\n\
             class Main {{ void run() {{ {code} }} }}"
        )
    };
    ok(&src(
        "Version a = new Version(1, \"beta\"); boolean same = a == a;",
    ));
    assert_eq!(
        errors(&src("Version a = new Version(1);")),
        ["this constructor takes 2 arguments but 1 argument was supplied"]
    );
    assert_eq!(
        errors(&src("Version a = new Version(\"beta\", 1);")),
        ["mismatched types", "mismatched types"]
    );
}

#[test]
fn results_record_callees_and_fields() {
    let src = "record Money(long cents, String currency) { long run(String... tags) {\n\
               \x20   Main.log(\"a\", \"b\");\n\
               \x20   return this.cents + this.currency.length();\n\
               } }\n\
               class Main { static void log(String... tags) {} }";
    let (results, diagnostics, source_map) = check_str(src);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let named = |name: &str| {
        let mut spans: Vec<_> = results
            .callees
            .iter()
            .filter(|(span, _)| {
                source_map
                    .lookup_char_pos(span.lo)
                    .is_some_and(|loc| loc.file.name.as_os_str() == "test.kr")
            })
            .filter(|(span, _)| source_map.span_to_snippet(**span).as_deref() == Some(name))
            .map(|(_, callee)| callee.clone())
            .collect();
        assert_eq!(spans.len(), 1, "one call to `{name}`");
        spans.remove(0)
    };
    assert!(named("log").packs_varargs);
    assert_eq!(named("length").ret, crate::Ty::INT);
    let fields: Vec<String> = results
        .fields
        .iter()
        .filter(|(span, _)| (span.hi.0 as usize) <= src.len())
        .map(|(_, field)| field.name.name.as_str().to_owned())
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect();
    assert_eq!(fields, ["cents", "currency"]);
}

#[test]
fn with_copies_a_struct_with_some_fields_changed() {
    let src = |code: &str| {
        format!(
            "record User(String name, String email, long visits);\n\
             class Account {{ String owner = \"\"; }}\n\
             class Main {{ static void run(User user, Account account) {{ {code} }} }}"
        )
    };
    ok(&src(
        "User other = user with { email = \"x@example.com\", visits = 1 };",
    ));
    assert_eq!(
        errors(&src("User other = user with { phone = \"1\" };")),
        ["no field `phone` on type `User`"]
    );
    assert_eq!(
        errors(&src("User other = user with { visits = \"x\" };")),
        ["mismatched types"]
    );
    assert_eq!(
        errors(&src(
            "User other = user with { name = \"a\", name = \"b\" };"
        )),
        ["the field `name` is set more than once"]
    );
    assert_eq!(
        errors(&src("Account other = account with { owner = \"x\" };")),
        ["`with` cannot be used on `Account`"]
    );
}

#[test]
fn record_components_never_change() {
    let src = |code: &str| {
        format!(
            "record User(String name, long visits) {{\n\
             \x20   User {{\n\
             \x20       if (visits < 0) {{ throw new IllegalArgumentException(\"visits\"); }}\n\
             \x20   }}\n\
             \x20   boolean isNew() {{ return this.visits == 0; }}\n\
             }}\n\
             class Main {{ static void run(User user) {{ {code} }} }}"
        )
    };
    ok(&src(
        "User user2 = new User(\"Ali\", 0); boolean fresh = user2.isNew(); \
         String name = user.name(); long visits = user.visits();",
    ));
    assert_eq!(
        errors(&src("String name = user.name;")),
        ["field `name` of `User` is private"]
    );
    assert_eq!(
        errors(&src("user.visits = 3;")),
        ["cannot assign to `visits`, a component of the record `User`"]
    );
    assert_eq!(
        errors(&src("User user2 = new User(\"Ali\");")),
        ["this constructor takes 2 arguments but 1 argument was supplied"]
    );
}

#[test]
fn records_are_equatable_when_their_components_are() {
    let src = |code: &str| {
        format!(
            "record Point(double x, double y);\n\
             class Handle {{}}\n\
             record Holder(Handle handle);\n\
             record Pair<A, B>(A first, B second);\n\
             record Key<K extends Hashable<K>>(K value);\n\
             class Main {{ static void run(Point a, Point b, Holder h) {{ {code} }} }}"
        )
    };
    ok(&src(
        "boolean same = a == b; HashSet<Point> points = new HashSet<>(); \
         HashSet<Key<String>> keys = new HashSet<>();",
    ));
    assert_eq!(
        errors(&src("boolean same = h == h;")),
        ["values of type `Holder` cannot be compared with `==`"]
    );
    assert_eq!(
        errors(&src(
            "Pair<String, int> p = new Pair<>(\"a\", 1); boolean same = p == p;"
        )),
        ["values of type `Pair<String, int>` cannot be compared with `==`"]
    );
}

#[test]
fn records_are_taken_apart_with_patterns() {
    let src = |code: &str| {
        format!(
            "record Point(double x, double y);\n\
             record Line(Point from, Point to);\n\
             class Main {{ static double run(Line line, Object any) {{ {code} }} }}"
        )
    };
    ok(&src(
        "if (any instanceof Point(double x, _) && x > 0.0) { return x; }\n\
         return switch (line) {\n\
         \x20   case Line(Point(double x1, _), Point(double x2, _)) -> x2 - x1;\n\
         };",
    ));
    assert_eq!(
        errors(&src(
            "return switch (line) { case Line(Point from) -> 0.0; };"
        )),
        ["this pattern has 1 field, but the record `Line` has 2 components"]
    );
}

#[test]
fn copyable_values_are_read_through_references() {
    body_ok(
        "List<String> names = new ArrayList<>(); String first = names.get(0); \
         &String borrowed = names.get(0); String copied = borrowed; int n = borrowed.length();",
    );
    assert_eq!(
        errors(
            "import std.util.List;\n\
             class A { static <T> T first(&List<T> xs) { return xs.get(0); } }"
        ),
        ["mismatched types"]
    );
    assert_eq!(
        errors(
            "import std.util.List;\n\
             class Box {}\n\
             class A { static Box first(&List<Box> xs) { return xs.get(0); } }"
        ),
        ["mismatched types"]
    );
}

#[test]
fn diamonds_take_their_arguments_from_the_context() {
    body_ok(
        "List<String> names = new ArrayList<>(); \
         Map<String, List<int>> groups = new HashMap<>(); \
         groups.put(\"a\", new ArrayList<>());",
    );
    assert_eq!(
        in_body("Object any = new ArrayList<>();"),
        ["cannot infer the type arguments of `ArrayList<>`"]
    );
}

#[test]
fn lambdas_decide_generic_results() {
    let src = |code: &str| {
        format!(
            "import std.function.Supplier;\n\
             class Main {{\n\
             \x20   static <R> R call(Supplier<R> make) {{ return make.get(); }}\n\
             \x20   void run() {{ {code} }}\n\
             }}"
        )
    };
    ok(&src(
        "int five = Main.call(() -> 5); String text = Main.call(() -> { return \"x\"; });",
    ));
    assert_eq!(
        errors(&src("String text = Main.call(() -> 5);")),
        ["mismatched types"]
    );
}

#[test]
fn assignments_write_through_mutable_references() {
    ok("class Main {\n\
        \x20   static void bump(&mut int value) { value = 3; value += 1; value++; }\n\
        \x20   static void rebind(&mut int a, &mut int b) { &mut int r = a; r = b; r = 5; }\n\
        }");
    assert_eq!(
        errors("class Main { static void set(&mut int value) { value = \"x\"; } }"),
        ["mismatched types"]
    );
}

#[test]
fn this_is_typed_by_the_receiver() {
    ok("class Node {\n\
        \x20   &Node self() { return this; }\n\
        \x20   mut &mut Node change() { return this; }\n\
        }");
    assert_eq!(
        errors("class Node { Node copy() { return this; } }"),
        ["mismatched types"]
    );
}

#[test]
fn loops_borrow_their_elements() {
    body_ok(
        "List<Point> points = new ArrayList<>(); \
         for (&Point point : points) { int x = point.sum(); } \
         for (Point point : points) { int y = point.sum(); } \
         List<int> numbers = new ArrayList<>(); \
         for (int n : numbers) { int z = n; }",
    );
}

#[test]
fn generic_results_follow_the_expected_type() {
    let src = |code: &str| {
        format!(
            "class Main {{\n\
             \x20   static <T> List<T> empty() {{ return new ArrayList<>(); }}\n\
             \x20   void run() {{ {code} }}\n\
             }}"
        )
    };
    ok(&src("List<String> names = Main.empty();"));
    assert_eq!(
        errors(&src("int size = Main.empty().size();")),
        ["cannot infer the type argument `T` of `empty`"]
    );
}

#[test]
fn references_to_nullables_need_a_check() {
    assert_eq!(
        errors("class A { static void f() { String? m = null; int n = (&m).length(); } }"),
        ["value of type `String?` may be null"]
    );
    assert_eq!(
        errors(
            "class A { static void f() { String? m = null; \
             if (m != null) { int n = (&m).length(); } } }"
        ),
        Vec::<String>::new()
    );
}

#[test]
fn methods_with_the_same_parameters_are_duplicates() {
    assert_eq!(
        errors("class A { int f(int a) { return 1; } static int f(int b) { return 2; } }"),
        ["duplicate definitions of `f` with the same parameter types"]
    );
    assert_eq!(
        errors("class A { <T> void f(T a) {} <U> void f(U b) {} }"),
        ["duplicate definitions of `f` with the same parameter types"]
    );
    assert_eq!(
        errors("class A { A(int a) {} A(int b) {} }"),
        ["duplicate definitions of `A` with the same parameter types"]
    );
    ok("class A { void f(int a) {} void f(long a) {} void f(int a, int b) {} }");
}

#[test]
fn cyclic_bounds_are_reported_without_looping() {
    assert_eq!(
        errors("class A<T extends T> {}"),
        ["the bounds of `T` lead back to `T`"]
    );
    assert_eq!(
        errors("class A { static <T extends U, U extends T> void f(T a) { a.x(); } }"),
        [
            "the bounds of `T` lead back to `T`",
            "no method named `x` found for `T`"
        ]
    );
}

#[test]
fn fields_that_cannot_be_null_need_a_value() {
    assert_eq!(
        errors("class A { String name; }"),
        ["field `name` is never given a value"]
    );
    assert_eq!(
        errors("class A { static final String name; }"),
        ["static field `name` is never given a value"]
    );
    assert_eq!(
        errors(
            "class A { String name; A(boolean early) { if (early) { return; } this.name = \"\"; } }"
        ),
        ["this constructor doesn't always give field `name` a value"]
    );
    assert_eq!(
        errors("class A { String name; A(boolean b) { if (b) { this.name = \"x\"; } } }"),
        ["this constructor doesn't always give field `name` a value"]
    );
    ok("class A { String? name; int count; static final int total; }");
    ok(
        "class A { String name; A(boolean b) { if (b) { this.name = \"x\"; } else { this.name = \"y\"; } } }",
    );
    ok("class A { String name; A() { this(\"x\"); } A(String name) { this.name = name; } }");
    ok(
        "class A { String name; A(int n) { if (n < 0) { throw new IllegalArgumentException(); } this.name = \"\"; } }",
    );
}

#[test]
fn inferred_type_arguments_meet_their_bounds() {
    assert_eq!(
        errors(
            "import std.util.*; class B {} class A { void f() { Set<B?> tags = new HashSet(); } }"
        ),
        ["type `B?` does not satisfy the bound of `T`"]
    );
    ok("import std.util.*; class A { void f() { Set<String> tags = new HashSet(); } }");
    ok("import std.util.*; class A { void f() { Set<String?> tags = new HashSet(); } }");
}

#[test]
fn type_parameters_have_no_static_members() {
    assert_eq!(
        errors(
            "class A<T> { T value; A(T value) { this.value = value; } Object f() { return T.value; } }"
        ),
        ["cannot reach `value` through type parameter `T`"]
    );
    assert_eq!(
        errors("class A<T> { void f() { T.make(); } }"),
        ["cannot reach `make` through type parameter `T`"]
    );
}

#[test]
fn values_that_cannot_be_built_or_called() {
    assert_eq!(
        errors("record P(int x) {} class A { void f() { Object o = new &P(1); } }"),
        ["cannot create an object of type `&P`"]
    );
    assert_eq!(
        errors("class A { void f() { String[] words = {}; words.println(1); } }"),
        ["no method named `println` found for `String[]`"]
    );
    assert_eq!(
        errors("class A { void f() { int[] a = {1}; a.length = 3; } }"),
        ["cannot assign to the length of an array"]
    );
    assert_eq!(
        errors("class A { void f() { Object o = (() -> 1).run(); } }"),
        ["cannot tell what type this closure has"]
    );
}

#[test]
fn constructor_calls_only_start_constructors() {
    assert_eq!(
        errors("class A { void f() { String s = \"a\" + this(); } }"),
        ["`this(...)` can only be the first statement of a constructor"]
    );
    assert_eq!(
        errors("class A { A() { int x = 1; this(x); } A(int x) {} }"),
        ["`this(...)` can only be the first statement of a constructor"]
    );
    assert_eq!(
        errors("class A { void f() { super(); } }"),
        ["`super(...)` can only be the first statement of a constructor"]
    );
    ok("class A { A() { this(1); } A(int x) { super(); } }");
}

#[test]
fn constructors_run_the_superclass_constructor() {
    assert_eq!(
        errors("class B { B(int x) {} } class A extends B { A() {} }"),
        ["`A` must call a constructor of `B` first"]
    );
    assert_eq!(
        errors("class B { B(int x) {} } class A extends B {}"),
        ["`A` must call a constructor of `B` first"]
    );
    assert_eq!(
        errors(
            "class B { B(int x) {} } class M extends B { M() { super(1); } } class A extends M {}"
        ),
        Vec::<String>::new()
    );
    ok("class B { B() {} B(int x) {} } class A extends B { A(int y) {} }");
}
