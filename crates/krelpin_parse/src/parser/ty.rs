use krelpin_ast::ast::{
    GenericParam, GenericParamKind, Generics, Ident, Path, PrimitiveTy, Ty, TyKind,
};
use krelpin_ast::token::TokenKind;
use krelpin_errors::Diagnostic;
use krelpin_span::{Symbol, kw};

use super::{Expected, PResult, Parser};

impl Parser<'_> {
    pub(crate) fn parse_ty(&mut self) -> PResult<Ty> {
        let lo = self.token.span;
        let mut ty = self.parse_ty_without_suffix()?;

        while self.eat_noexpect(TokenKind::Question) {
            ty = Ty {
                kind: TyKind::Nullable(Box::new(ty)),
                span: lo.to(self.prev_token.span),
            };
        }

        Ok(ty)
    }

    fn parse_ty_without_suffix(&mut self) -> PResult<Ty> {
        let lo = self.token.span;

        if self.break_and_eat(TokenKind::And) {
            let mutable = self.eat_keyword_noexpect(kw::Mut);
            if self.token.kind == TokenKind::OpenBracket {
                self.reject_bracket_sources()?;
            }
            let ty = Box::new(self.parse_ty_without_suffix()?);
            return Ok(Ty {
                kind: TyKind::Ref { mutable, ty },
                span: lo.to(self.prev_token.span),
            });
        }

        let mut ty = self.parse_ty_atom()?;
        while self.token.kind == TokenKind::OpenBracket
            && self.look_ahead(1) == TokenKind::CloseBracket
        {
            self.bump();
            self.bump();
            ty = Ty {
                kind: TyKind::Array(Box::new(ty)),
                span: lo.to(self.prev_token.span),
            };
        }
        Ok(ty)
    }

    fn parse_ty_atom(&mut self) -> PResult<Ty> {
        let lo = self.token.span;

        if self.eat_noexpect(TokenKind::OpenParen) {
            let ty = self.parse_ty()?;
            self.expect(TokenKind::CloseParen)?;
            return Ok(Ty {
                kind: ty.kind,
                span: lo.to(self.prev_token.span),
            });
        }

        let primitive = match self.token.kind {
            TokenKind::Ident(symbol) => PrimitiveTy::from_symbol(symbol),
            _ => None,
        };
        if let Some(primitive) = primitive {
            self.bump();
            return Ok(Ty {
                kind: TyKind::Primitive(primitive),
                span: lo,
            });
        }

        if self.token.ident().is_none() {
            self.expected.push(Expected::Type);
            return Err(self.unexpected());
        }

        let path = self.parse_path()?;
        if self.bracket_sources_ahead() {
            self.reject_bracket_sources()?;
        }
        let args = self.parse_generic_args()?;
        Ok(Ty {
            kind: TyKind::Path { path, args },
            span: lo.to(self.prev_token.span),
        })
    }

    pub(crate) fn parse_path(&mut self) -> PResult<Path> {
        let mut segments = vec![self.parse_ident()?];
        while self.token.kind == TokenKind::Dot && self.look_ahead(1) != TokenKind::Star {
            self.bump();
            segments.push(self.parse_ident()?);
        }
        Ok(Path::new(segments))
    }

    fn reject_bracket_sources(&mut self) -> PResult<()> {
        let lo = self.token.span;
        self.bump();
        while !matches!(self.token.kind, TokenKind::CloseBracket | TokenKind::Eof) {
            self.bump();
        }
        self.expect(TokenKind::CloseBracket)?;
        self.emit(
            Diagnostic::error("borrow sources are not written in brackets")
                .with_span(lo.to(self.prev_token.span))
                .with_help(
                    "name them after the parameters, like `&String first(&String a) borrows a`",
                ),
        );
        Ok(())
    }

    pub(crate) fn parse_name_clause(&mut self, keyword: Symbol) -> PResult<Vec<Ident>> {
        let clause = self.token.kind == TokenKind::Ident(keyword)
            && matches!(self.look_ahead(1), TokenKind::Ident(_));
        if !clause {
            return Ok(Vec::new());
        }
        self.bump();
        let mut names = vec![self.parse_source_name()?];
        while self.eat(TokenKind::Comma) {
            names.push(self.parse_source_name()?);
        }
        Ok(names)
    }

    fn parse_source_name(&mut self) -> PResult<Ident> {
        if self.eat_keyword_noexpect(kw::This) {
            return Ok(Ident::new(kw::This, self.prev_token.span));
        }
        self.parse_ident()
    }

    pub(crate) fn parse_generic_args(&mut self) -> PResult<Vec<Ty>> {
        if !self.eat_noexpect(TokenKind::Lt) {
            return Ok(Vec::new());
        }
        if self.break_and_eat(TokenKind::Gt) {
            return Ok(Vec::new());
        }

        let mut args = vec![self.parse_ty()?];
        loop {
            if self.break_and_eat(TokenKind::Gt) {
                return Ok(args);
            }
            if !self.eat(TokenKind::Comma) {
                self.expected.push(Expected::Token(TokenKind::Gt));
                return Err(self.unexpected());
            }
            args.push(self.parse_ty()?);
        }
    }

    pub(crate) fn parse_ty_list(&mut self) -> PResult<Vec<Ty>> {
        let mut tys = vec![self.parse_ty()?];
        while self.eat(TokenKind::Comma) {
            tys.push(self.parse_ty()?);
        }
        Ok(tys)
    }

    fn bracket_sources_ahead(&self) -> bool {
        !self.array_lengths
            && self.token.kind == TokenKind::OpenBracket
            && matches!(self.look_ahead(1), TokenKind::Ident(_))
            && matches!(
                self.look_ahead(2),
                TokenKind::CloseBracket | TokenKind::Comma
            )
    }

    pub(crate) fn parse_type_generics(&mut self) -> PResult<Generics> {
        if self.bracket_sources_ahead() {
            self.reject_bracket_sources()?;
        }
        let mut generics = self.parse_generics()?;
        for name in self.parse_name_clause(kw::Borrows)? {
            if name.name == kw::This {
                self.error(name.span, "`this` cannot be declared as a borrow source");
                continue;
            }
            generics.params.push(GenericParam {
                name,
                kind: GenericParamKind::BorrowSource,
                span: name.span,
            });
        }
        Ok(generics)
    }

    pub(crate) fn parse_generics(&mut self) -> PResult<Generics> {
        let lo = self.token.span;
        if !self.eat_noexpect(TokenKind::Lt) {
            return Ok(Generics {
                params: Vec::new(),
                span: lo.shrink_to_lo(),
            });
        }

        let mut params = vec![self.parse_generic_param()?];
        loop {
            if self.break_and_eat(TokenKind::Gt) {
                break;
            }
            if !self.eat(TokenKind::Comma) {
                self.expected.push(Expected::Token(TokenKind::Gt));
                return Err(self.unexpected());
            }
            params.push(self.parse_generic_param()?);
        }

        Ok(Generics {
            params,
            span: lo.to(self.prev_token.span),
        })
    }

    pub(crate) fn parse_bounds(&mut self) -> PResult<Vec<Ty>> {
        let mut bounds = vec![self.parse_ty()?];
        while self.break_and_eat(TokenKind::And) {
            bounds.push(self.parse_ty()?);
        }
        Ok(bounds)
    }

    fn parse_generic_param(&mut self) -> PResult<GenericParam> {
        let lo = self.token.span;

        if self.break_and_eat(TokenKind::And) {
            let name = self.parse_ident()?;
            let span = lo.to(self.prev_token.span);
            self.emit(
                Diagnostic::error("borrow sources are not declared between `<` and `>`")
                    .with_span(span)
                    .with_help(format!(
                        "declare them after the type parameters, like `class Parser<T> borrows {}`",
                        name.name
                    )),
            );
            return Ok(GenericParam {
                name,
                kind: GenericParamKind::BorrowSource,
                span,
            });
        }

        let name = self.parse_ident()?;
        let bounds = if self.eat_keyword(kw::Extends) {
            self.parse_bounds()?
        } else {
            Vec::new()
        };

        Ok(GenericParam {
            name,
            kind: GenericParamKind::Type { bounds },
            span: lo.to(self.prev_token.span),
        })
    }
}
