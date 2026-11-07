use std::thread;

use krelpin_ast::ast::{
    CompilationUnit, FieldStorage, FnRetTy, GenericParamKind, Ident, ItemKind, MemberKind,
    ReceiverKind, TyKind, Visibility,
};
use krelpin_ast::token::TokenKind;
use krelpin_errors::{DiagCtxt, DiagnosticBuffer};
use krelpin_span::SourceMap;

use super::{class, errors, members, only_member, parse_ok, parse_str, ret_ty};
use crate::{lexer, parser};

#[test]
fn package_and_imports() {
    let unit = parse_ok("package a.b;\nimport a.c.D;\nimport a.e.*;\nclass X {}");
    assert_eq!(unit.package.unwrap().to_string(), "a.b");

    let imports: Vec<(String, bool)> = unit
        .imports
        .iter()
        .map(|import| (import.path.to_string(), import.glob))
        .collect();
    assert_eq!(
        imports,
        [("a.c.D".to_owned(), false), ("a.e".to_owned(), true)]
    );
    assert_eq!(unit.items.len(), 1);
}

#[test]
fn hello_world() {
    let unit = parse_ok(
        "package example;\n\
         class Main {\n\
         \x20   static void main() {\n\
         \x20       Console.println(\"Hello World!\");\n\
         \x20   }\n\
         }\n",
    );
    assert_eq!(unit.items[0].name.name.as_str(), "Main");

    let MemberKind::Method(main) = &class(&unit, 0).members[0].kind else {
        panic!("expected main method");
    };
    assert_eq!(main.name.name.as_str(), "main");
    assert!(matches!(main.ret, FnRetTy::Void(_)));
    assert!(main.receiver.is_none());
    assert!(main.body.is_some());
}

#[test]
fn fields() {
    let members = members(
        "class Person {\n\
         \x20   static final int MAX = 64;\n\
         \x20   static final AtomicInt created = new AtomicInt(0);\n\
         \x20   final String name;\n\
         \x20   public int age;\n\
         \x20   private String? nickname;\n\
         }",
    );

    let summary: Vec<(String, String, bool)> = members
        .iter()
        .map(|member| match &member.kind {
            MemberKind::Field(field) => {
                let storage = match (field.storage, field.final_kw.is_some()) {
                    (FieldStorage::Instance, false) => "instance",
                    (FieldStorage::Instance, true) => "final",
                    (FieldStorage::Static(_), false) => "static",
                    (FieldStorage::Static(_), true) => "static final",
                };
                (
                    storage.to_owned(),
                    format!("{} {}", field.ty, field.name.name),
                    field.init.is_some(),
                )
            }
            other => panic!("expected a field, found {other:?}"),
        })
        .collect();

    let expected = [
        ("static final", "int MAX", true),
        ("static final", "AtomicInt created", true),
        ("final", "String name", false),
        ("instance", "int age", false),
        ("instance", "String? nickname", false),
    ];
    let expected: Vec<(String, String, bool)> = expected
        .iter()
        .map(|&(storage, decl, init)| (storage.to_owned(), decl.to_owned(), init))
        .collect();
    assert_eq!(summary, expected);

    assert!(matches!(members[3].vis, Visibility::Public(_)));
    assert!(matches!(members[4].vis, Visibility::Private(_)));
    assert_eq!(members[2].vis, Visibility::Default);
}

#[test]
fn constructors() {
    let members = members("class Person { Person(String name, int age) { this.name = name; } }");
    let MemberKind::Constructor(constructor) = &members[0].kind else {
        panic!("expected a constructor");
    };
    assert_eq!(constructor.params.len(), 2);
}

#[test]
fn method_receivers() {
    let members = members(
        "class Person {\n\
         \x20   &String getName() { return &this.name; }\n\
         \x20   mut void rename(String newName) {}\n\
         \x20   move String intoName() { return this.name; }\n\
         \x20   static int max(int a, int b) { return a; }\n\
         }",
    );

    let receivers: Vec<Option<ReceiverKind>> = members
        .iter()
        .map(|member| match &member.kind {
            MemberKind::Method(method) => method.receiver.map(|receiver| receiver.kind),
            other => panic!("expected a method, found {other:?}"),
        })
        .collect();
    assert_eq!(
        receivers,
        [
            Some(ReceiverKind::Ref),
            Some(ReceiverKind::RefMut),
            Some(ReceiverKind::Owned),
            None,
        ]
    );
}

#[test]
fn move_is_only_a_keyword_before_a_method() {
    let unit = parse_ok(
        "class Piece {\n\
         \x20   int move;\n\
         \x20   mut void move(int steps) { int move = steps; this.move = move; }\n\
         \x20   move Piece take() { return this; }\n\
         }",
    );
    let names: Vec<String> = class(&unit, 0)
        .members
        .iter()
        .map(|member| match &member.kind {
            MemberKind::Field(field) => format!("field {}", field.name.name),
            MemberKind::Method(method) => format!(
                "{:?} {}",
                method.receiver.map(|receiver| receiver.kind),
                method.name.name
            ),
            other => panic!("unexpected member {other:?}"),
        })
        .collect();
    assert_eq!(
        names,
        ["field move", "Some(RefMut) move", "Some(Owned) take"]
    );
}

#[test]
fn reference_types() {
    assert_eq!(ret_ty("static &String f() {}"), "&String");
    assert_eq!(ret_ty("static &mut String f() {}"), "&mut String");
    assert_eq!(ret_ty("static &String? f() {}"), "&String?");
    assert_eq!(ret_ty("static &(String?) f() {}"), "&(String?)");
    assert_eq!(ret_ty("static &&String f() {}"), "&&String");
}

#[test]
fn array_types() {
    assert_eq!(ret_ty("static String[] f() {}"), "String[]");
    assert_eq!(ret_ty("static int[][] f() {}"), "int[][]");
    assert_eq!(ret_ty("static &int[] f() {}"), "&int[]");
    assert_eq!(ret_ty("static String[]? f() {}"), "String[]?");
    assert_eq!(ret_ty("static &String[]? f() {}"), "&String[]?");
    assert_eq!(ret_ty("static (&String)[] f() {}"), "(&String)[]");
    assert_eq!(ret_ty("static (String?)[] f() {}"), "(String?)[]");
    assert_eq!(ret_ty("static List<String>[] f() {}"), "List<String>[]");
}

#[test]
fn reference_binds_to_whole_array() {
    let MemberKind::Method(method) = only_member("static &int[] f() {}") else {
        panic!("expected a method");
    };
    let FnRetTy::Ty(ty) = method.ret else {
        panic!("expected a return type");
    };
    let TyKind::Ref { ty: inner, .. } = ty.kind else {
        panic!("expected a reference");
    };
    assert!(matches!(inner.kind, TyKind::Array(_)));
}

#[test]
fn generic_types_split_closing_brackets() {
    assert_eq!(
        ret_ty("static Map<String, List<&String>> f() {}"),
        "Map<String, List<&String>>"
    );
    assert_eq!(ret_ty("static A<B<C<D>>> f() {}"), "A<B<C<D>>>");
    assert_eq!(
        ret_ty("static java.util.List<int> f() {}"),
        "java.util.List<int>"
    );
}

#[test]
fn class_generics() {
    let unit = parse_ok("class Parser<T extends Comparable<T> & Cloneable> borrows src {}");
    let params = &class(&unit, 0).generics.params;

    assert_eq!(params[1].name.name.as_str(), "src");
    assert_eq!(params[1].kind, GenericParamKind::BorrowSource);

    let GenericParamKind::Type { bounds } = &params[0].kind else {
        panic!("expected a type parameter");
    };
    let bounds: Vec<String> = bounds.iter().map(ToString::to_string).collect();
    assert_eq!(bounds, ["Comparable<T>", "Cloneable"]);
}

#[test]
fn borrows_and_keeps_clauses() {
    let MemberKind::Method(method) =
        only_member("static &String pick(&String a, &String b) borrows a, b keeps b throws Bad {}")
    else {
        panic!("expected a method");
    };
    let names = |idents: &[Ident]| -> Vec<String> {
        idents.iter().map(|ident| ident.name.to_string()).collect()
    };
    assert_eq!(names(&method.borrows), ["a", "b"]);
    assert_eq!(names(&method.keeps), ["b"]);
    assert_eq!(method.throws.len(), 1);

    let MemberKind::Method(method) = only_member("&String name() borrows this {}") else {
        panic!("expected a method");
    };
    assert_eq!(names(&method.borrows), ["this"]);

    let unit = parse_ok("class A { int borrows; int keeps(int borrows) { return borrows; } }");
    assert_eq!(class(&unit, 0).members.len(), 2);

    assert_eq!(
        errors("class Parser<&src, T> {}"),
        ["borrow sources are not declared between `<` and `>`"]
    );
    assert_eq!(
        errors("class Parser borrows this {}"),
        ["`this` cannot be declared as a borrow source"]
    );
    assert_eq!(
        errors("class A { &[this] String f() {} }"),
        ["borrow sources are not written in brackets"]
    );
    assert_eq!(
        errors("class A { A(&String a) borrows a {} }"),
        ["a constructor does not return a value, so it borrows nothing"]
    );
}

#[test]
fn extends_and_implements() {
    let unit = parse_ok("class Dog extends Animal implements Pet, Comparable<Dog> {}");
    let class = class(&unit, 0);
    assert_eq!(class.extends.as_ref().unwrap().to_string(), "Animal");
    let implements: Vec<String> = class.implements.iter().map(ToString::to_string).collect();
    assert_eq!(implements, ["Pet", "Comparable<Dog>"]);
}

#[test]
fn generic_methods_varargs_throws_and_abstract_methods() {
    let MemberKind::Method(first) = only_member("static <T> T first(List<T> items) {}") else {
        panic!("expected a method");
    };
    assert_eq!(first.generics.params.len(), 1);

    let MemberKind::Method(log) = only_member("static void log(String... parts) {}") else {
        panic!("expected a method");
    };
    assert!(log.params[0].variadic);

    let MemberKind::Method(read) = only_member("void read() throws IOException, Bad {}") else {
        panic!("expected a method");
    };
    assert_eq!(read.throws.len(), 2);

    let MemberKind::Method(run) = only_member("abstract void run();") else {
        panic!("expected a method");
    };
    assert!(run.body.is_none());
}

#[test]
fn docs_and_annotations() {
    let members = members("class A { /** Docs */ @Override @Since(\"1.0\") String text() {} }");
    assert_eq!(members[0].docs.len(), 1);
    assert_eq!(members[0].docs[0].as_str(), " Docs ");

    let annotations: Vec<(String, bool)> = members[0]
        .annotations
        .iter()
        .map(|annotation| (annotation.path.to_string(), annotation.args.is_some()))
        .collect();
    assert_eq!(
        annotations,
        [("Override".to_owned(), false), ("Since".to_owned(), true)]
    );
}

#[test]
fn docs_before_package_belong_to_unit() {
    let unit = parse_ok("/** Unit */ package a; /** Class */ class A {}");
    assert_eq!(unit.docs.len(), 1);
    assert_eq!(unit.items[0].docs.len(), 1);
}

#[test]
fn signature_errors() {
    assert_eq!(
        errors("class A { foo() {} }"),
        ["missing return type for method"]
    );
    assert_eq!(
        errors("class A { void x; }"),
        ["fields cannot have type `void`"]
    );
    assert_eq!(
        errors("class A { void f(int a, &mut this) {} A(this) {} }"),
        ["`this` is not a parameter", "`this` is not a parameter"]
    );
    assert_eq!(
        errors("record Point(&this, int x);"),
        ["`this` is not a parameter"]
    );
}

#[test]
fn modifier_errors() {
    assert_eq!(
        errors("class A { const int x = 1; }"),
        ["`const` is not a Krelpin modifier"]
    );
    assert_eq!(
        errors("static class A {}"),
        ["`static` cannot be used on top-level types"]
    );
    assert_eq!(
        errors("class A { public private int x; }"),
        ["multiple visibility modifiers"]
    );
    assert_eq!(
        errors("class A { static static final int x = 1; }"),
        ["duplicate `static` modifier"]
    );
    assert_eq!(
        errors("class A { static int x = 1; }"),
        ["static field `x` must be `final`"]
    );
    assert_eq!(
        errors("class A { static mut void f() {} mut move void g() {} }"),
        [
            "a `static` method cannot be `mut`",
            "only one of `mut` and `move` can be used"
        ]
    );
    assert_eq!(
        errors("mut class A { mut int x; move A() {} }"),
        [
            "`mut` cannot be used on types",
            "`mut` cannot be used on fields",
            "`move` cannot be used on constructors"
        ]
    );
}

#[test]
fn expected_token_messages() {
    assert_eq!(
        errors("class A { int x }"),
        ["expected one of `(`, `=`, or `;`, found `}`"]
    );
    assert_eq!(
        errors("class A { int class; }"),
        ["expected identifier, found keyword `class`"]
    );
    assert_eq!(
        errors("class A { int x = ; }"),
        ["expected expression, found `;`"]
    );
    assert_eq!(
        errors("class A { List<String x; }"),
        ["expected `,` or `>`, found `x`"]
    );
}

#[test]
fn unclosed_class() {
    assert_eq!(
        errors("class A { int x;"),
        ["this file contains an unclosed delimiter"]
    );
    assert_eq!(
        errors("class A { void f() { if (x) { }"),
        ["this file contains an unclosed delimiter"]
    );
}

#[test]
fn recovers_at_top_level() {
    let parsed = parse_str("int junk; class A {} 42 class B {}");
    assert_eq!(
        parsed.errors,
        [
            "expected type declaration, found keyword `int`",
            "expected type declaration, found `42`"
        ]
    );
    let names: Vec<&str> = parsed
        .unit
        .items
        .iter()
        .map(|item| item.name.name.as_str())
        .collect();
    assert_eq!(names, ["A", "B"]);
}

#[test]
fn recovers_inside_class() {
    let parsed = parse_str("class A { int 5; void broken( { } String ok; }");
    assert_eq!(parsed.errors.len(), 2);

    let names: Vec<String> = class(&parsed.unit, 0)
        .members
        .iter()
        .map(|member| match &member.kind {
            MemberKind::Field(field) => field.name.name.to_string(),
            other => panic!("unexpected member {other:?}"),
        })
        .collect();
    assert_eq!(names, ["ok"]);
}

#[test]
fn files_are_parsed_in_parallel() {
    let source_map = SourceMap::new();
    let buffer = DiagnosticBuffer::default();
    let dcx = DiagCtxt::new(buffer.clone());

    let files: Vec<_> = (0..8)
        .map(|index| {
            let src = if index == 3 {
                "class Broken { foo() {} }".to_owned()
            } else {
                format!("class C{index} {{ int value{index}; }}")
            };
            source_map.new_source_file(format!("{index}.kr"), src)
        })
        .collect();

    let units: Vec<CompilationUnit> = thread::scope(|scope| {
        let handles: Vec<_> = files
            .iter()
            .map(|file| {
                let dcx = &dcx;
                scope.spawn(move || parser::parse(lexer::lex(file, dcx), dcx))
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });

    assert_eq!(buffer.messages(), ["missing return type for method"]);
    assert_eq!(units[5].items[0].name.name.as_str(), "C5");
    assert_eq!(units[0].items[0].name.name.as_str(), "C0");
}

#[test]
fn where_clauses() {
    let MemberKind::Method(method) = only_member(
        "boolean has(T value) \
         where T extends Comparable<T> & Cloneable, U extends Object {}",
    ) else {
        panic!("expected a method");
    };
    let predicates: Vec<String> = method
        .where_clause
        .iter()
        .map(|predicate| {
            let bounds: Vec<String> = predicate.bounds.iter().map(ToString::to_string).collect();
            format!("{}: {}", predicate.param.name, bounds.join(" & "))
        })
        .collect();
    assert_eq!(predicates, ["T: Comparable<T> & Cloneable", "U: Object"]);
}

#[test]
fn macro_declarations() {
    let unit = parse_ok("@Intrinsic\nmacro Builder;\nclass A {}");
    assert_eq!(unit.items.len(), 1);
    assert_eq!(unit.macros.len(), 1);
    assert_eq!(unit.macros[0].name.name.as_str(), "Builder");
    assert!(unit.macros[0].body.is_none());
    let unit =
        parse_ok("macro Builder(TokenStream args, TokenStream item) { return item; }\nclass A {}");
    let body = unit.macros[0].body.as_ref().expect("the macro has a body");
    assert_eq!(body.params.len(), 2);
    assert_eq!(body.params[1].name.name.as_str(), "item");
    assert_eq!(body.body.stmts.len(), 1);
    assert_eq!(
        errors("macro Builder { }"),
        ["the macro `Builder` has no parameters"]
    );
    assert_eq!(
        errors("public macro Builder;"),
        ["macros cannot have a visibility modifier"]
    );
}

#[test]
fn annotated_declarations_capture_their_tokens() {
    let unit = parse_ok("/** docs */\n@Getters\nclass A { @Trace int f() { return 1; } int g; }");
    let tokens = unit.items[0]
        .tokens
        .tokens()
        .expect("annotated items keep tokens");
    assert!(matches!(tokens[0].kind, TokenKind::DocComment(_)));
    assert_eq!(tokens[1].kind, TokenKind::At);
    assert_eq!(
        tokens.last().map(|token| token.kind),
        Some(TokenKind::CloseBrace)
    );
    let ItemKind::Class(class) = &unit.items[0].kind else {
        panic!("expected a class");
    };
    let traced = class.members[0]
        .tokens
        .tokens()
        .expect("annotated members keep tokens");
    assert_eq!(traced.first().map(|token| token.kind), Some(TokenKind::At));
    assert_eq!(
        traced.last().map(|token| token.kind),
        Some(TokenKind::CloseBrace)
    );
    assert!(class.members[1].tokens.tokens().is_none());
    assert!(parse_ok("class B {}").items[0].tokens.tokens().is_none());
}

#[test]
fn annotation_arguments_keep_their_tokens() {
    let unit = parse_ok("@Builder(Equatable, Hashable) class A {}");
    let args = unit.items[0].annotations[0]
        .args
        .as_ref()
        .expect("arguments");
    assert_eq!(args.tokens.len(), 3);
}

#[test]
fn annotation_arguments_touch_the_name() {
    let members = members("class A { @Intrinsic\n    (&String)? f(); @Builder(Equatable) int x; }");
    assert_eq!(members[0].annotations[0].args, None);
    assert!(members[1].annotations[0].args.is_some());
}
