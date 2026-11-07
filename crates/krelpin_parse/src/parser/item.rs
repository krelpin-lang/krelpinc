use krelpin_ast::ast::{
    Annotation, CapturedTokens, Class, CompilationUnit, Constructor, Enum, FieldStorage, FnRetTy,
    Generics, Ident, Import, Inheritance, Interface, Item, ItemKind, MacroBody, MacroDef, Member,
    MemberKind, Path, Receiver, ReceiverKind, Record, Ty, Variant, VariantField, Visibility,
    is_intrinsic,
};
use krelpin_ast::token::TokenKind;
use krelpin_errors::Diagnostic;
use krelpin_span::{Span, Symbol, kw};

use super::lookahead::is_plain_ident;
use super::{ErrorReported, Expected, PResult, Parser};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Container {
    Class,
    Record,
    Interface,
    Enum,
}

impl Container {
    fn plural(self) -> &'static str {
        match self {
            Container::Class => "classes",
            Container::Record => "records",
            Container::Interface => "interfaces",
            Container::Enum => "enums",
        }
    }
}

enum Declaration {
    Item(Item),
    Macro(MacroDef),
}

struct Modifiers {
    vis: Visibility,
    storage: FieldStorage,
    inheritance: Inheritance,
    receiver: Option<ReceiverModifier>,
    asyncness: Option<Span>,
}

#[derive(Clone, Copy)]
struct ReceiverModifier {
    keyword: Symbol,
    receiver: Receiver,
}

impl Parser<'_> {
    pub(crate) fn parse_compilation_unit(&mut self) -> CompilationUnit {
        let lo = self.token.span;
        let mut docs = self.parse_docs();
        let mut unit_docs = Vec::new();

        let mut package = None;
        if self.token.is_keyword(kw::Package) {
            unit_docs = std::mem::take(&mut docs);
            match self.parse_package() {
                Ok(path) => package = Some(path),
                Err(_) => self.recover_to_member_end(),
            }
            docs = self.parse_docs();
        }

        let mut imports = Vec::new();
        while self.token.is_keyword(kw::Import) {
            match self.parse_import() {
                Ok(import) => imports.push(import),
                Err(_) => self.recover_to_member_end(),
            }
            docs = self.parse_docs();
        }

        let mut items = Vec::new();
        let mut macros = Vec::new();
        loop {
            docs.extend(self.parse_docs());
            if self.token.kind == TokenKind::Eof {
                break;
            }
            match self.parse_declaration(std::mem::take(&mut docs)) {
                Ok(Declaration::Item(item)) => items.push(item),
                Ok(Declaration::Macro(def)) => macros.push(def),
                Err(_) => self.recover_to_next_item(),
            }
        }

        CompilationUnit {
            docs: unit_docs,
            package,
            imports,
            items,
            macros,
            span: lo.to(self.token.span),
        }
    }

    pub(crate) fn parse_items_to_eof(&mut self) -> Vec<Item> {
        let mut items = Vec::new();
        let mut docs = Vec::new();
        loop {
            docs.extend(self.parse_docs());
            if self.token.kind == TokenKind::Eof {
                return items;
            }
            match self.parse_declaration(std::mem::take(&mut docs)) {
                Ok(Declaration::Item(item)) => items.push(item),
                Ok(Declaration::Macro(def)) => {
                    self.emit(
                        Diagnostic::error("a macro cannot define another macro")
                            .with_span(def.span)
                            .with_note("macros are only defined in `proc-macro` crates"),
                    );
                }
                Err(_) => self.recover_to_next_item(),
            }
        }
    }

    fn parse_package(&mut self) -> PResult<Path> {
        self.bump();
        let path = self.parse_path()?;
        self.expect(TokenKind::Semi)?;
        Ok(path)
    }

    fn parse_import(&mut self) -> PResult<Import> {
        let lo = self.token.span;
        self.bump();

        let path = self.parse_path()?;
        let glob = self.token.kind == TokenKind::Dot && self.look_ahead(1) == TokenKind::Star;
        if glob {
            self.bump();
            self.bump();
        }
        self.expect(TokenKind::Semi)?;

        Ok(Import {
            path,
            glob,
            span: lo.to(self.prev_token.span),
        })
    }

    fn parse_declaration(&mut self, docs: Vec<Symbol>) -> PResult<Declaration> {
        let lo = self.token.span;
        let start = self.index;
        let annotations = self.parse_annotations()?;
        let modifiers = self.parse_modifiers();
        if self.token.is_keyword(kw::Macro) {
            return self
                .parse_macro(docs, annotations, &modifiers, lo)
                .map(Declaration::Macro);
        }
        if self.token.is_keyword(kw::Struct) {
            return Err(self.reject_struct());
        }
        self.reject_storage(modifiers.storage, "top-level types");
        let Some(container) = type_container(self.token.kind) else {
            self.expected = vec![Expected::Item];
            return Err(self.unexpected());
        };
        let mut item = self.parse_item(docs, annotations, &modifiers, container, lo)?;
        item.tokens = self.capture(start, !item.annotations.is_empty());
        Ok(Declaration::Item(item))
    }

    fn capture(&self, start: usize, wanted: bool) -> CapturedTokens {
        if !wanted {
            return CapturedTokens::default();
        }
        let mut first = start;
        while first > 0 && matches!(self.tokens[first - 1].kind, TokenKind::DocComment(_)) {
            first -= 1;
        }
        CapturedTokens::new(&self.tokens[first..self.index])
    }

    fn parse_nested_type(
        &mut self,
        docs: Vec<Symbol>,
        annotations: Vec<Annotation>,
        modifiers: &Modifiers,
        container: Container,
        lo: Span,
    ) -> PResult<Item> {
        if container == Container::Class && modifiers.storage == FieldStorage::Instance {
            self.emit(
                Diagnostic::error("inner classes are not supported")
                    .with_span(self.token.span)
                    .with_note(
                        "a nested class does not keep a hidden reference to an outer object",
                    )
                    .with_help(
                        "mark it `static`, and pass the outer object to its constructor \
                         if it needs one",
                    ),
            );
        }
        self.parse_item(docs, annotations, modifiers, container, lo)
    }

    fn parse_item(
        &mut self,
        docs: Vec<Symbol>,
        annotations: Vec<Annotation>,
        modifiers: &Modifiers,
        container: Container,
        lo: Span,
    ) -> PResult<Item> {
        self.reject_receiver(modifiers.receiver, "types");
        self.reject_async(modifiers, "types");
        self.bump();

        if container != Container::Class {
            self.reject_inheritance(modifiers.inheritance, container.plural());
        } else if let Inheritance {
            abstract_kw: Some(_),
            final_kw: Some(span),
        } = modifiers.inheritance
        {
            self.emit(
                Diagnostic::error("a class cannot be both `abstract` and `final`")
                    .with_span(span)
                    .with_note("an abstract class must be extended, a final class cannot be"),
            );
        }

        let name = self.parse_ident()?;
        let kind = match container {
            Container::Class => self.parse_class(name)?,
            Container::Record => self.parse_record(name)?,
            Container::Interface => self.parse_interface(name)?,
            Container::Enum => self.parse_enum(name)?,
        };

        Ok(Item {
            docs,
            annotations,
            vis: modifiers.vis,
            inheritance: modifiers.inheritance,
            name,
            kind,
            span: lo.to(self.prev_token.span),
            tokens: CapturedTokens::default(),
        })
    }

    fn parse_macro(
        &mut self,
        docs: Vec<Symbol>,
        annotations: Vec<Annotation>,
        modifiers: &Modifiers,
        lo: Span,
    ) -> PResult<MacroDef> {
        self.bump();
        self.reject_storage(modifiers.storage, "macros");
        self.reject_inheritance(modifiers.inheritance, "macros");
        self.reject_receiver(modifiers.receiver, "macros");
        self.reject_async(modifiers, "macros");
        if let Some(span) = modifiers.vis.span() {
            self.error(span, "macros cannot have a visibility modifier");
        }
        let name = self.parse_ident()?;
        let body = if self.check(TokenKind::OpenParen) {
            let body_lo = self.token.span;
            let params = self.parse_params()?;
            let body = self.parse_block()?;
            Some(MacroBody {
                params,
                body,
                span: body_lo.to(self.prev_token.span),
            })
        } else if self.check(TokenKind::OpenBrace) {
            let block =
                self.parse_unparsed_delimited(TokenKind::OpenBrace, TokenKind::CloseBrace)?;
            self.emit(
                Diagnostic::error(format!("the macro `{}` has no parameters", name.name))
                    .with_span(name.span.to(block.span))
                    .with_help(format!(
                        "write `macro {}(TokenStream args, TokenStream item) {{ ... }}`",
                        name.name
                    )),
            );
            None
        } else {
            self.expect_semi()?;
            None
        };
        Ok(MacroDef {
            docs,
            annotations,
            name,
            body,
            span: lo.to(self.prev_token.span),
        })
    }

    fn parse_class(&mut self, name: Ident) -> PResult<ItemKind> {
        let generics = self.parse_type_generics()?;
        let extends = if self.eat_keyword(kw::Extends) {
            Some(self.parse_ty()?)
        } else {
            None
        };
        let implements = self.parse_implements()?;
        let members = self.parse_body(Container::Class, name)?;

        Ok(ItemKind::Class(Class {
            generics,
            extends,
            implements,
            members,
        }))
    }

    fn parse_record(&mut self, name: Ident) -> PResult<ItemKind> {
        let generics = self.parse_type_generics()?;
        let components = if self.token.kind == TokenKind::OpenParen {
            let components = self.parse_params()?;
            for component in components.iter().filter(|component| component.variadic) {
                self.error(component.span, "record components cannot be variadic");
            }
            components
        } else {
            self.emit(
                Diagnostic::error(format!("the record `{}` has no components", name.name))
                    .with_span(name.span)
                    .with_help(format!(
                        "list its components after the name, like `record {}(String name)`",
                        name.name
                    )),
            );
            Vec::new()
        };
        self.reject_extends("records")?;
        let implements = self.parse_implements()?;
        let mut members = if self.eat(TokenKind::Semi) {
            Vec::new()
        } else {
            self.parse_body(Container::Record, name)?
        };
        for member in &mut members {
            if let MemberKind::Constructor(ctor) = &mut member.kind
                && ctor.compact
            {
                ctor.params = components.clone();
            }
        }

        Ok(ItemKind::Record(Record {
            generics,
            components,
            implements,
            members,
        }))
    }

    fn reject_struct(&mut self) -> ErrorReported {
        let span = self.token.span;
        self.bump();
        self.emit(
            Diagnostic::error("`struct` is not a Krelpin keyword")
                .with_span(span)
                .with_note("data types are written as records")
                .with_help("write `record Name(Type field, ...) {}`"),
        )
    }

    fn parse_interface(&mut self, name: Ident) -> PResult<ItemKind> {
        let generics = self.parse_type_generics()?;
        let extends = if self.eat_keyword(kw::Extends) {
            self.parse_ty_list()?
        } else {
            Vec::new()
        };

        if self.token.is_keyword(kw::Implements) {
            self.emit(
                Diagnostic::error("interfaces cannot implement other interfaces")
                    .with_span(self.token.span)
                    .with_help("use `extends` to inherit from other interfaces"),
            );
            self.bump();
            self.parse_ty_list()?;
        }

        let members = self.parse_body(Container::Interface, name)?;
        Ok(ItemKind::Interface(Interface {
            generics,
            extends,
            members,
        }))
    }

    fn parse_enum(&mut self, name: Ident) -> PResult<ItemKind> {
        let generics = self.parse_type_generics()?;
        self.reject_extends("enums")?;
        let implements = self.parse_implements()?;

        let open = self.expect(TokenKind::OpenBrace)?;
        let mut variants = Vec::new();
        while !matches!(self.token.kind, TokenKind::Semi | TokenKind::CloseBrace) {
            variants.push(self.parse_variant(name)?);
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }

        let members = if self.eat(TokenKind::Semi) {
            self.parse_member_list(open, Container::Enum, name)?
        } else if self.eat(TokenKind::CloseBrace) {
            Vec::new()
        } else {
            return Err(self.unexpected());
        };

        Ok(ItemKind::Enum(Enum {
            generics,
            implements,
            variants,
            members,
        }))
    }

    fn parse_variant(&mut self, owner: Ident) -> PResult<Variant> {
        let lo = self.token.span;
        let docs = self.parse_docs();
        let annotations = self.parse_annotations()?;
        if !is_plain_ident(self.token.kind) {
            self.expected.push(Expected::Ident);
            return Err(self.unexpected());
        }
        let name = self.parse_ident()?;
        let fields = if self.token.kind == TokenKind::OpenParen {
            self.parse_variant_fields(owner, name)?
        } else {
            Vec::new()
        };

        Ok(Variant {
            docs,
            annotations,
            name,
            fields,
            span: lo.to(self.prev_token.span),
        })
    }

    fn parse_variant_fields(&mut self, owner: Ident, variant: Ident) -> PResult<Vec<VariantField>> {
        let open = self.token.span;
        if self.look_ahead(1) == TokenKind::CloseParen {
            self.bump();
            self.bump();
            self.emit(
                Diagnostic::error(format!("the variant `{}` has no fields", variant.name))
                    .with_span(open.to(self.prev_token.span))
                    .with_help("a variant without data is written without parentheses"),
            );
            return Ok(Vec::new());
        }
        if !self.variant_field_ahead(1) {
            self.parse_args()?;
            self.emit(
                Diagnostic::error("enum variants declare fields, not arguments")
                    .with_span(open.to(self.prev_token.span))
                    .with_note("enums have no constructors; each variant carries its own data")
                    .with_help(format!(
                        "declare its fields, like `{variant}(Type name)`, and pass the values \
                         when creating it: `{owner}.{variant}(...)`",
                        variant = variant.name,
                        owner = owner.name,
                    )),
            );
            return Ok(Vec::new());
        }

        self.bump();
        let mut fields = Vec::new();
        loop {
            let ty = self.parse_ty()?;
            let name = self.parse_ident()?;
            fields.push(VariantField { ty, name });
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        self.expect(TokenKind::CloseParen)?;
        Ok(fields)
    }

    fn parse_implements(&mut self) -> PResult<Vec<Ty>> {
        if self.eat_keyword(kw::Implements) {
            self.parse_ty_list()
        } else {
            Ok(Vec::new())
        }
    }

    fn reject_extends(&mut self, what: &str) -> PResult<()> {
        if !self.token.is_keyword(kw::Extends) {
            return Ok(());
        }
        let lo = self.token.span;
        self.bump();
        self.parse_ty()?;
        self.emit(
            Diagnostic::error(format!("{what} cannot extend other types"))
                .with_span(lo.to(self.prev_token.span))
                .with_help(format!("{what} can implement interfaces with `implements`")),
        );
        Ok(())
    }

    fn parse_body(&mut self, container: Container, owner: Ident) -> PResult<Vec<Member>> {
        let open = self.expect(TokenKind::OpenBrace)?;
        self.parse_member_list(open, container, owner)
    }

    fn parse_member_list(
        &mut self,
        open: Span,
        container: Container,
        owner: Ident,
    ) -> PResult<Vec<Member>> {
        let mut members = Vec::new();

        loop {
            let docs = self.parse_docs();
            if self.eat_noexpect(TokenKind::CloseBrace) {
                return Ok(members);
            }
            if self.eat_noexpect(TokenKind::Semi) {
                continue;
            }
            if self.token.kind == TokenKind::Eof {
                return Err(self.unclosed_delimiter(open));
            }

            match self.parse_member(docs, container, owner) {
                Ok(member) => members.push(member),
                Err(error) => {
                    self.recover_to_member_end();
                    if self.token.kind == TokenKind::Eof {
                        return Err(error);
                    }
                }
            }
        }
    }

    pub(crate) fn parse_members_to_eof(
        &mut self,
        container: Container,
        owner: Ident,
    ) -> Vec<Member> {
        let mut members = Vec::new();
        loop {
            let docs = self.parse_docs();
            if self.token.kind == TokenKind::Eof {
                return members;
            }
            if self.eat_noexpect(TokenKind::Semi) {
                continue;
            }
            match self.parse_member(docs, container, owner) {
                Ok(member) => members.push(member),
                Err(_) => {
                    self.recover_to_member_end();
                    self.eat_noexpect(TokenKind::CloseBrace);
                }
            }
        }
    }

    fn parse_annotations(&mut self) -> PResult<Vec<Annotation>> {
        let mut annotations = Vec::new();
        while self.token.kind == TokenKind::At {
            let lo = self.token.span;
            self.bump();
            let path = self.parse_path()?;
            let adjacent = self.token.span.lo == self.prev_token.span.hi;
            let args = if self.token.kind == TokenKind::OpenParen && adjacent {
                Some(self.parse_unparsed_delimited(TokenKind::OpenParen, TokenKind::CloseParen)?)
            } else {
                None
            };
            annotations.push(Annotation {
                path,
                args,
                span: lo.to(self.prev_token.span),
            });
        }
        Ok(annotations)
    }

    fn parse_modifiers(&mut self) -> Modifiers {
        let mut modifiers = Modifiers {
            vis: Visibility::Default,
            storage: FieldStorage::Instance,
            inheritance: Inheritance::default(),
            receiver: None,
            asyncness: None,
        };

        loop {
            let span = self.token.span;
            let TokenKind::Ident(symbol) = self.token.kind else {
                return modifiers;
            };

            match symbol {
                kw::Public | kw::Protected | kw::Private => {
                    let vis = match symbol {
                        kw::Public => Visibility::Public(span),
                        kw::Protected => Visibility::Protected(span),
                        _ => Visibility::Private(span),
                    };
                    if modifiers.vis == Visibility::Default {
                        modifiers.vis = vis;
                    } else {
                        self.emit(
                            Diagnostic::error("multiple visibility modifiers")
                                .with_span(span)
                                .with_help("remove all but one visibility modifier"),
                        );
                    }
                }
                kw::Const => {
                    self.emit(
                        Diagnostic::error("`const` is not a Krelpin modifier")
                            .with_span(span)
                            .with_help("declare a constant with `static final`"),
                    );
                    if modifiers.storage == FieldStorage::Instance {
                        modifiers.storage = FieldStorage::Static(span);
                    }
                    if modifiers.inheritance.final_kw.is_none() {
                        modifiers.inheritance.final_kw = Some(span);
                    }
                }
                kw::Static => {
                    if modifiers.storage == FieldStorage::Instance {
                        modifiers.storage = FieldStorage::Static(span);
                    } else {
                        self.error(span, "duplicate `static` modifier");
                    }
                }
                kw::Abstract | kw::Final => {
                    let slot = if symbol == kw::Abstract {
                        &mut modifiers.inheritance.abstract_kw
                    } else {
                        &mut modifiers.inheritance.final_kw
                    };
                    if slot.is_some() {
                        self.error(span, format!("duplicate `{symbol}` modifier"));
                    } else {
                        *slot = Some(span);
                    }
                }
                kw::Async => {
                    if modifiers.asyncness.is_some() {
                        self.error(span, "duplicate `async` modifier");
                    } else {
                        modifiers.asyncness = Some(span);
                    }
                }
                kw::Move if !self.move_is_modifier() => return modifiers,
                kw::Mut | kw::Move => {
                    let kind = if symbol == kw::Mut {
                        ReceiverKind::RefMut
                    } else {
                        ReceiverKind::Owned
                    };
                    if modifiers.receiver.is_none() {
                        modifiers.receiver = Some(ReceiverModifier {
                            keyword: symbol,
                            receiver: Receiver { kind, span },
                        });
                    } else {
                        self.error(span, "only one of `mut` and `move` can be used");
                    }
                }
                _ => return modifiers,
            }
            self.bump();
        }
    }

    fn move_is_modifier(&self) -> bool {
        matches!(
            self.look_ahead(1),
            TokenKind::Ident(_) | TokenKind::Lt | TokenKind::And
        )
    }

    fn reject_storage(&self, storage: FieldStorage, what: &str) {
        let FieldStorage::Static(span) = storage else {
            return;
        };
        self.emit(
            Diagnostic::error(format!("`static` cannot be used on {what}"))
                .with_span(span)
                .with_help("`static` is only allowed on fields, methods and nested types"),
        );
    }

    fn reject_inheritance(&self, inheritance: Inheritance, what: &str) {
        let modifiers = [
            ("abstract", inheritance.abstract_kw),
            ("final", inheritance.final_kw),
        ];
        for (keyword, span) in modifiers {
            if let Some(span) = span {
                self.error(span, format!("`{keyword}` cannot be used on {what}"));
            }
        }
    }

    fn reject_receiver(&self, modifier: Option<ReceiverModifier>, what: &str) {
        let Some(ReceiverModifier { keyword, receiver }) = modifier else {
            return;
        };
        self.emit(
            Diagnostic::error(format!("`{keyword}` cannot be used on {what}"))
                .with_span(receiver.span)
                .with_help("`mut` and `move` are only allowed on methods"),
        );
    }

    fn reject_async(&self, modifiers: &Modifiers, what: &str) {
        if let Some(span) = modifiers.asyncness {
            self.emit(
                Diagnostic::error(format!("`async` cannot be used on {what}"))
                    .with_span(span)
                    .with_help("`async` is only allowed on methods"),
            );
        }
    }

    fn method_receiver(&self, modifiers: &Modifiers, name: Ident) -> Option<Receiver> {
        match (modifiers.storage, modifiers.receiver) {
            (FieldStorage::Static(_), None) => None,
            (FieldStorage::Static(_), Some(ReceiverModifier { keyword, receiver })) => {
                self.emit(
                    Diagnostic::error(format!("a `static` method cannot be `{keyword}`"))
                        .with_span(receiver.span)
                        .with_note("a `static` method has no object to change or take"),
                );
                None
            }
            (storage, receiver) => {
                self.reject_storage(storage, "methods");
                Some(receiver.map_or(
                    Receiver {
                        kind: ReceiverKind::Ref,
                        span: name.span,
                    },
                    |modifier| modifier.receiver,
                ))
            }
        }
    }

    fn parse_member(
        &mut self,
        docs: Vec<Symbol>,
        container: Container,
        owner: Ident,
    ) -> PResult<Member> {
        let lo = self.token.span;
        let start = self.index;
        let annotations = self.parse_annotations()?;
        let modifiers = self.parse_modifiers();
        if self.token.is_keyword(kw::Struct) {
            return Err(self.reject_struct());
        }
        if let Some(nested) = type_container(self.token.kind) {
            let mut item = self.parse_nested_type(docs, annotations, &modifiers, nested, lo)?;
            item.tokens = self.capture(start, !item.annotations.is_empty());
            return Ok(Member {
                docs: Vec::new(),
                annotations: Vec::new(),
                vis: item.vis,
                inheritance: Inheritance::default(),
                span: item.span,
                kind: MemberKind::Type(Box::new(item)),
                tokens: CapturedTokens::default(),
            });
        }
        let kind = self.parse_member_kind(owner, &modifiers)?;
        self.validate_member(container, &annotations, &modifiers, &kind);
        let tokens = self.capture(start, !annotations.is_empty());

        Ok(Member {
            docs,
            annotations,
            vis: modifiers.vis,
            inheritance: modifiers.inheritance,
            kind,
            span: lo.to(self.prev_token.span),
            tokens,
        })
    }

    fn parse_member_kind(&mut self, owner: Ident, modifiers: &Modifiers) -> PResult<MemberKind> {
        let storage = modifiers.storage;
        if self.token.kind == TokenKind::Lt {
            let generics = self.parse_generics()?;
            let ret = self.parse_ret_ty()?;
            let name = self.parse_ident()?;
            let receiver = self.method_receiver(modifiers, name);
            return self
                .parse_method(modifiers.asyncness, generics, ret, name, receiver)
                .map(MemberKind::Method);
        }

        let compact = match self.token.ident() {
            Some(name) if name == owner.name && self.look_ahead(1) == TokenKind::OpenBrace => {
                Some(self.parse_ident()?)
            }
            _ => None,
        };
        if let Some(name) = compact {
            self.reject_storage(storage, "constructors");
            self.reject_receiver(modifiers.receiver, "constructors");
            self.reject_async(modifiers, "constructors");
            let body = self.parse_block()?;
            return Ok(MemberKind::Constructor(Constructor {
                compact: true,
                name,
                params: Vec::new(),
                keeps: Vec::new(),
                throws: Vec::new(),
                body,
            }));
        }

        let called = match self.token.ident() {
            Some(name) if self.look_ahead(1) == TokenKind::OpenParen => Some(name),
            _ => None,
        };
        if let Some(name) = called {
            if name != owner.name {
                return Err(self.missing_return_type());
            }
            self.reject_storage(storage, "constructors");
            self.reject_receiver(modifiers.receiver, "constructors");
            self.reject_async(modifiers, "constructors");
            return self.parse_constructor().map(MemberKind::Constructor);
        }

        let ret = self.parse_ret_ty()?;
        let name = self.parse_ident()?;

        if self.check(TokenKind::OpenParen) {
            let receiver = self.method_receiver(modifiers, name);
            return self
                .parse_method(
                    modifiers.asyncness,
                    Generics::default(),
                    ret,
                    name,
                    receiver,
                )
                .map(MemberKind::Method);
        }

        let ty = match ret {
            FnRetTy::Ty(ty) => ty,
            FnRetTy::Void(span) => {
                return Err(self.error(span, "fields cannot have type `void`"));
            }
        };
        self.reject_receiver(modifiers.receiver, "fields");
        self.reject_async(modifiers, "fields");
        self.parse_field(storage, modifiers.inheritance.final_kw, ty, name)
            .map(MemberKind::Field)
    }

    fn validate_member(
        &self,
        container: Container,
        annotations: &[Annotation],
        modifiers: &Modifiers,
        kind: &MemberKind,
    ) {
        let Inheritance {
            abstract_kw,
            final_kw,
        } = modifiers.inheritance;

        match kind {
            MemberKind::Type(_) => {}
            MemberKind::Field(field) => {
                if let Some(span) = abstract_kw {
                    self.error(span, "`abstract` cannot be used on fields");
                }
                if container == Container::Interface && field.storage == FieldStorage::Instance {
                    self.emit(
                        Diagnostic::error("interfaces can only have `static final` fields")
                            .with_span(field.name.span)
                            .with_help("make the field `static final`, or move it to a class"),
                    );
                } else if let FieldStorage::Static(span) = field.storage
                    && final_kw.is_none()
                {
                    self.emit(
                        Diagnostic::error(format!(
                            "static field `{}` must be `final`",
                            field.name.name
                        ))
                        .with_span(span)
                        .with_note("a `static` field is shared by every thread, so it never changes")
                        .with_help(
                            "write `static final`; to share changing state, store an `AtomicInt` \
                             or a `Mutex<T>` in it",
                        ),
                    );
                }
                if container == Container::Enum && field.storage == FieldStorage::Instance {
                    self.emit(
                        Diagnostic::error("enums cannot have instance fields")
                            .with_span(field.name.span)
                            .with_help("store the data in the variants that carry it"),
                    );
                }
                if container == Container::Record && field.storage == FieldStorage::Instance {
                    self.emit(
                        Diagnostic::error("records cannot have instance fields")
                            .with_span(field.name.span)
                            .with_help(format!(
                                "add `{}` to the components of the record",
                                field.name.name
                            )),
                    );
                }
            }
            MemberKind::Constructor(constructor) => {
                match container {
                    Container::Interface => {
                        self.error(constructor.name.span, "interfaces cannot have constructors");
                    }
                    Container::Enum => {
                        self.emit(
                            Diagnostic::error("enums cannot have constructors")
                                .with_span(constructor.name.span)
                                .with_help("declare the fields of each variant in the variant"),
                        );
                    }
                    Container::Record if !constructor.compact => {
                        self.emit(
                            Diagnostic::error("records cannot declare full constructors")
                                .with_span(constructor.name.span)
                                .with_note("a record is always created from its components")
                                .with_help(format!(
                                    "check the components in a compact constructor: `{} {{ ... }}`",
                                    constructor.name.name
                                )),
                        );
                    }
                    Container::Class if constructor.compact => {
                        self.emit(
                            Diagnostic::error("only records have compact constructors")
                                .with_span(constructor.name.span)
                                .with_help(format!(
                                    "list the parameters: `{}(...) {{ ... }}`",
                                    constructor.name.name
                                )),
                        );
                    }
                    Container::Record | Container::Class => {}
                }
                self.reject_inheritance(modifiers.inheritance, "constructors");
            }
            MemberKind::Method(method) => {
                let changes_this = method
                    .receiver
                    .filter(|receiver| receiver.kind == ReceiverKind::RefMut);
                if let (Container::Record, Some(receiver)) = (container, changes_this) {
                    self.emit(
                        Diagnostic::error("record methods cannot be `mut`")
                            .with_span(receiver.span)
                            .with_note("the components of a record never change")
                            .with_help("return a changed copy with `with` instead"),
                    );
                }
                if let (Some(_), Some(span)) = (abstract_kw, final_kw) {
                    self.error(span, "a method cannot be both `abstract` and `final`");
                }

                let can_be_abstract = matches!(container, Container::Class | Container::Interface);
                match (abstract_kw, &method.body) {
                    (Some(span), _) if !can_be_abstract => {
                        let what = container.plural();
                        self.error(span, format!("abstract methods are not allowed in {what}"));
                    }
                    (Some(span), Some(_)) => {
                        self.error(span, "abstract methods cannot have a body");
                    }
                    (None, None)
                        if container != Container::Interface && !is_intrinsic(annotations) =>
                    {
                        self.emit(
                            Diagnostic::error(format!(
                                "missing body for method `{}`",
                                method.name.name
                            ))
                            .with_span(method.name.span)
                            .with_help("add a body, or mark the method `abstract`"),
                        );
                    }
                    _ => {}
                }
            }
        }
    }
}

fn type_container(kind: TokenKind) -> Option<Container> {
    match kind {
        TokenKind::Ident(kw::Class) => Some(Container::Class),
        TokenKind::Ident(kw::Record) => Some(Container::Record),
        TokenKind::Ident(kw::Interface) => Some(Container::Interface),
        TokenKind::Ident(kw::Enum) => Some(Container::Enum),
        _ => None,
    }
}
