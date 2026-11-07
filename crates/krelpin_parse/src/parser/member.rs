use krelpin_ast::ast::{
    Constructor, Field, FieldStorage, FnRetTy, Generics, Ident, Method, Param, Receiver, Ty,
    Unparsed, WherePredicate,
};
use krelpin_ast::token::TokenKind;
use krelpin_errors::Diagnostic;
use krelpin_span::{Span, kw};

use super::{PResult, Parser};

impl Parser<'_> {
    pub(crate) fn missing_return_type(&mut self) -> super::ErrorReported {
        let span = self.token.span;
        self.emit(
            Diagnostic::error("missing return type for method")
                .with_span(span)
                .with_label("add a return type before the method name")
                .with_help("use `void` if the method does not return a value"),
        )
    }

    pub(crate) fn parse_ret_ty(&mut self) -> PResult<FnRetTy> {
        if self.eat_keyword_noexpect(kw::Void) {
            return Ok(FnRetTy::Void(self.prev_token.span));
        }
        self.parse_ty().map(FnRetTy::Ty)
    }

    pub(crate) fn parse_field(
        &mut self,
        storage: FieldStorage,
        final_kw: Option<Span>,
        ty: Ty,
        name: Ident,
    ) -> PResult<Field> {
        let init = if self.eat(TokenKind::Eq) {
            Some(self.parse_initializer()?)
        } else {
            None
        };
        self.expect_semi()?;

        Ok(Field {
            storage,
            final_kw,
            ty,
            name,
            init,
        })
    }

    pub(crate) fn parse_constructor(&mut self) -> PResult<Constructor> {
        let name = self.parse_ident()?;
        let params = self.parse_params()?;
        let borrows = self.parse_name_clause(kw::Borrows)?;
        if let Some(first) = borrows.first() {
            self.emit(
                Diagnostic::error("a constructor does not return a value, so it borrows nothing")
                    .with_span(first.span)
                    .with_help("to keep a parameter in the object, write `keeps` instead"),
            );
        }
        let keeps = self.parse_name_clause(kw::Keeps)?;
        let throws = self.parse_throws()?;
        let body = self.parse_block()?;

        Ok(Constructor {
            compact: false,
            name,
            params,
            keeps,
            throws,
            body,
        })
    }

    pub(crate) fn parse_method(
        &mut self,
        asyncness: Option<Span>,
        generics: Generics,
        ret: FnRetTy,
        name: Ident,
        receiver: Option<Receiver>,
    ) -> PResult<Method> {
        let params = self.parse_params()?;
        let borrows = self.parse_name_clause(kw::Borrows)?;
        let keeps = self.parse_name_clause(kw::Keeps)?;
        let throws = self.parse_throws()?;
        let where_clause = self.parse_where_clause()?;
        let body = if self.eat(TokenKind::Semi) {
            None
        } else {
            Some(self.parse_block()?)
        };

        Ok(Method {
            asyncness,
            generics,
            ret,
            name,
            receiver,
            params,
            borrows,
            keeps,
            throws,
            where_clause,
            body,
        })
    }

    fn parse_where_clause(&mut self) -> PResult<Vec<WherePredicate>> {
        let mut predicates = Vec::new();
        if !self.eat_keyword(kw::Where) {
            return Ok(predicates);
        }
        loop {
            let lo = self.token.span;
            let param = self.parse_ident()?;
            if !self.eat_keyword(kw::Extends) {
                return Err(self.unexpected());
            }
            let bounds = self.parse_bounds()?;
            predicates.push(WherePredicate {
                param,
                bounds,
                span: lo.to(self.prev_token.span),
            });
            if !self.eat(TokenKind::Comma) {
                return Ok(predicates);
            }
        }
    }

    fn parse_throws(&mut self) -> PResult<Vec<Ty>> {
        if self.eat_keyword(kw::Throws) {
            self.parse_ty_list()
        } else {
            Ok(Vec::new())
        }
    }

    pub(crate) fn parse_params(&mut self) -> PResult<Vec<Param>> {
        self.expect(TokenKind::OpenParen)?;
        let mut params = Vec::new();

        if self.eat(TokenKind::CloseParen) {
            return Ok(params);
        }

        loop {
            if !self.reject_this_param() {
                params.push(self.parse_param()?);
            }

            if self.eat(TokenKind::CloseParen) {
                return Ok(params);
            }
            self.expect(TokenKind::Comma)?;
        }
    }

    fn reject_this_param(&mut self) -> bool {
        let lo = self.token.span;
        let len = match (self.look_ahead(0), self.look_ahead(1), self.look_ahead(2)) {
            (TokenKind::Ident(kw::This), _, _) => 1,
            (TokenKind::And, TokenKind::Ident(kw::This), _) => 2,
            (TokenKind::And, TokenKind::Ident(kw::Mut), TokenKind::Ident(kw::This)) => 3,
            _ => return false,
        };
        for _ in 0..len {
            self.bump();
        }
        self.emit(
            Diagnostic::error("`this` is not a parameter")
                .with_span(lo.to(self.prev_token.span))
                .with_note(
                    "`this` is available in constructors and in every method that is not `static`",
                )
                .with_help("remove it, and mark the method `mut` if it changes the object"),
        );
        true
    }

    fn parse_param(&mut self) -> PResult<Param> {
        let lo = self.token.span;
        let final_kw = self.eat_keyword_noexpect(kw::Final).then_some(lo);
        let ty = self.parse_ty()?;
        let variadic = self.eat_noexpect(TokenKind::DotDotDot);
        let name = self.parse_ident()?;

        Ok(Param {
            final_kw,
            ty,
            name,
            variadic,
            span: lo.to(self.prev_token.span),
        })
    }

    pub(crate) fn parse_unparsed_delimited(
        &mut self,
        open: TokenKind,
        close: TokenKind,
    ) -> PResult<Unparsed> {
        let open_span = self.expect(open)?;
        let mut depth = 1usize;
        let mut tokens = Vec::new();

        loop {
            match self.token.kind {
                TokenKind::Eof => return Err(self.unclosed_delimiter(open_span)),
                kind if kind == open => depth += 1,
                kind if kind == close => {
                    depth -= 1;
                    if depth == 0 {
                        self.bump();
                        return Ok(Unparsed {
                            tokens,
                            span: open_span.to(self.prev_token.span),
                        });
                    }
                }
                _ => {}
            }
            tokens.push(self.token);
            self.bump();
        }
    }
}
