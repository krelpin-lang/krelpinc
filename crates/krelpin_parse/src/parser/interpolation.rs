use krelpin_ast::ast::{BinOp, Expr, ExprKind, Ident};
use krelpin_ast::token::{Lit, LitKind, Token, TokenKind};
use krelpin_errors::Diagnostic;
use krelpin_lexer::interpolate::{self, Piece};
use krelpin_lexer::unescape::Mode;
use krelpin_span::{BytePos, Span, Symbol};

use super::{PResult, Parser};
use crate::lexer;

impl Parser<'_> {
    pub(super) fn is_interpolated(lit: Lit) -> bool {
        matches!(lit.kind, LitKind::Str | LitKind::TextBlock)
            && interpolate::is_interpolated(lit.symbol.as_str())
    }

    pub(super) fn parse_interpolated(&mut self, lit: Lit, span: Span) -> PResult<Expr> {
        let content = lit.symbol.as_str();
        let fallback = Expr {
            kind: ExprKind::Lit(Lit::new(LitKind::Err, lit.symbol, None)),
            span,
        };
        let Ok(pieces) = interpolate::pieces(content) else {
            return Ok(fallback);
        };
        let (delimiter, mode) = match lit.kind {
            LitKind::TextBlock => (3, Mode::TextBlock),
            _ => (1, Mode::Str),
        };
        let content_lo = span.lo + delimiter;
        let mut texts = interpolate::texts(content, &pieces, mode).into_iter();
        let first_span = match pieces.first() {
            Some(Piece::Text(range)) => sub_span(content_lo, range),
            _ => Span::new(span.lo, content_lo),
        };
        let mut result = text_expr(&texts.next().unwrap_or_default(), first_span);
        let mut valid = true;
        for (index, piece) in pieces.iter().enumerate() {
            let part = match piece {
                Piece::Text(_) => continue,
                Piece::Name(range) => {
                    let ident = Ident {
                        name: Symbol::intern(&content[range.clone()]),
                        span: sub_span(content_lo, range),
                    };
                    let name = Expr {
                        kind: ExprKind::Name(ident),
                        span: ident.span,
                    };
                    borrow(name, sub_span(content_lo, &(range.start - 1..range.end)))
                }
                Piece::Expr(range) => {
                    match self.interpolated_expr(content, content_lo, range.clone()) {
                        Some(part) => part,
                        None => {
                            valid = false;
                            continue;
                        }
                    }
                }
            };
            result = concat(result, part, span.lo);
            let text = texts.next().unwrap_or_default();
            if let Some(Piece::Text(range)) = pieces.get(index + 1)
                && !text.is_empty()
            {
                result = concat(
                    result,
                    text_expr(&text, sub_span(content_lo, range)),
                    span.lo,
                );
            }
        }
        if !valid {
            return Ok(fallback);
        }
        Ok(Expr {
            kind: result.kind,
            span,
        })
    }

    fn interpolated_expr(
        &mut self,
        content: &str,
        content_lo: BytePos,
        range: std::ops::Range<usize>,
    ) -> Option<Expr> {
        let at = |offset: usize| content_lo + offset as u32;
        let open = Span::new(at(range.start - 2), at(range.start));
        let close = Span::new(at(range.end), at(range.end + 1));
        let colon = interpolate::spec_colon(&content[range.clone()]).map(|at| range.start + at);
        let expr_end = colon.unwrap_or(range.end);
        let mut tokens = lexer::lex_str(&content[range.start..expr_end], at(range.start), self.dcx);
        tokens.retain(|token| token.kind != TokenKind::Eof);
        let end = match colon {
            Some(colon) => Token::new(TokenKind::Colon, Span::new(at(colon), at(colon + 1))),
            None => Token::new(TokenKind::CloseBrace, close),
        };
        if tokens.is_empty() {
            self.emit(
                Diagnostic::error("expected an expression in the interpolation")
                    .with_span(Span::new(open.lo, end.span.hi)),
            );
            return None;
        }
        tokens.push(end);
        let mut parser = Parser::new(tokens, self.dcx);
        let inner = parser.parse_expr().ok()?;
        if parser.token.kind != end.kind {
            self.emit(
                Diagnostic::error("unexpected tokens in an interpolation")
                    .with_span(parser.token.span)
                    .with_help("an interpolation holds a single expression, like `${a + b}`"),
            );
            return None;
        }
        let Some(colon) = colon else {
            return Some(borrow(inner, Span::new(open.lo, close.hi)));
        };
        let spec_range = colon + 1..range.end;
        let spec = &content[spec_range.clone()];
        let spec_span = sub_span(content_lo, &spec_range);
        if let Err(message) = interpolate::parse_spec(spec) {
            self.emit(
                Diagnostic::error(format!("invalid format spec `{spec}`"))
                    .with_span(spec_span)
                    .with_note(message)
                    .with_help(
                        "a spec looks like `[[fill]align][+][#][0][width][.precision][type]`, \
                         for example `.2`, `>8`, `08.3` or `#x`",
                    ),
            );
            return None;
        }
        let colon_span = Span::new(at(colon), at(colon + 1));
        let receiver = borrow(inner, Span::new(open.lo, colon_span.hi));
        Some(Expr {
            kind: ExprKind::MethodCall {
                receiver: Some(Box::new(receiver)),
                type_args: Vec::new(),
                name: Ident {
                    name: Symbol::intern("format"),
                    span: colon_span,
                },
                args: vec![text_expr(spec, spec_span)],
                safe: false,
            },
            span: Span::new(open.lo, close.hi),
        })
    }
}

fn borrow(expr: Expr, span: Span) -> Expr {
    Expr {
        kind: ExprKind::Borrow {
            mutable: false,
            expr: Box::new(expr),
        },
        span,
    }
}

fn concat(lhs: Expr, rhs: Expr, lo: BytePos) -> Expr {
    let span = Span::new(lo, rhs.span.hi);
    Expr {
        kind: ExprKind::Binary {
            op: BinOp::Add,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        },
        span,
    }
}

fn text_expr(text: &str, span: Span) -> Expr {
    Expr {
        kind: ExprKind::Lit(Lit::new(LitKind::Str, Symbol::intern(&escape(text)), None)),
        span,
    }
}

fn sub_span(content_lo: BytePos, range: &std::ops::Range<usize>) -> Span {
    Span::new(
        content_lo + range.start as u32,
        content_lo + range.end as u32,
    )
}

fn escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '$' => out.push_str("\\$"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => out.push_str(&format!("\\u{{{:x}}}", c as u32)),
            c => out.push(c),
        }
    }
    out
}
