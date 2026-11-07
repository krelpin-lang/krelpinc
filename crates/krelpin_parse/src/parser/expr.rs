use krelpin_ast::ast::{
    BinOp, Expr, ExprKind, FieldInit, Ident, LambdaBody, LambdaParam, PrimitiveTy, SwitchExprArm,
    SwitchExprBody, TyKind, UnOp,
};
use krelpin_ast::token::TokenKind;
use krelpin_errors::Diagnostic;
use krelpin_span::{Span, kw};

use super::{Expected, PResult, Parser};

const INSTANCEOF_PRECEDENCE: u8 = 7;

fn binary_op(kind: TokenKind) -> Option<(u8, BinOp)> {
    let op = match kind {
        TokenKind::OrOr => (1, BinOp::Or),
        TokenKind::AndAnd => (2, BinOp::And),
        TokenKind::Or => (3, BinOp::BitOr),
        TokenKind::Caret => (4, BinOp::BitXor),
        TokenKind::And => (5, BinOp::BitAnd),
        TokenKind::EqEq => (6, BinOp::Eq),
        TokenKind::Ne => (6, BinOp::Ne),
        TokenKind::Lt => (7, BinOp::Lt),
        TokenKind::Le => (7, BinOp::Le),
        TokenKind::Gt => (7, BinOp::Gt),
        TokenKind::Ge => (7, BinOp::Ge),
        TokenKind::QuestionColon => (8, BinOp::Elvis),
        TokenKind::Shl => (9, BinOp::Shl),
        TokenKind::Shr => (9, BinOp::Shr),
        TokenKind::UShr => (9, BinOp::UShr),
        TokenKind::Plus => (10, BinOp::Add),
        TokenKind::Minus => (10, BinOp::Sub),
        TokenKind::Star => (11, BinOp::Mul),
        TokenKind::Slash => (11, BinOp::Div),
        TokenKind::Percent => (11, BinOp::Rem),
        _ => return None,
    };
    Some(op)
}

fn assign_op(kind: TokenKind) -> Option<Option<BinOp>> {
    let op = match kind {
        TokenKind::Eq => None,
        TokenKind::PlusEq => Some(BinOp::Add),
        TokenKind::MinusEq => Some(BinOp::Sub),
        TokenKind::StarEq => Some(BinOp::Mul),
        TokenKind::SlashEq => Some(BinOp::Div),
        TokenKind::PercentEq => Some(BinOp::Rem),
        TokenKind::AndEq => Some(BinOp::BitAnd),
        TokenKind::OrEq => Some(BinOp::BitOr),
        TokenKind::CaretEq => Some(BinOp::BitXor),
        TokenKind::ShlEq => Some(BinOp::Shl),
        TokenKind::ShrEq => Some(BinOp::Shr),
        TokenKind::UShrEq => Some(BinOp::UShr),
        _ => return None,
    };
    Some(op)
}

fn prefix_op(kind: TokenKind) -> Option<UnOp> {
    let op = match kind {
        TokenKind::Minus => UnOp::Neg,
        TokenKind::Bang => UnOp::Not,
        TokenKind::Tilde => UnOp::BitNot,
        TokenKind::PlusPlus => UnOp::PreInc,
        TokenKind::MinusMinus => UnOp::PreDec,
        _ => return None,
    };
    Some(op)
}

impl Parser<'_> {
    pub(crate) fn parse_expr(&mut self) -> PResult<Expr> {
        if self.lambda_ahead() {
            return self.parse_lambda();
        }

        let lo = self.token.span;
        let lhs = self.parse_ternary()?;
        let Some(op) = assign_op(self.token.kind) else {
            return Ok(lhs);
        };

        self.bump();
        let rhs = self.parse_expr()?;
        Ok(self.mk_expr(
            lo,
            ExprKind::Assign {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
        ))
    }

    pub(crate) fn parse_ternary(&mut self) -> PResult<Expr> {
        let lo = self.token.span;
        let cond = self.parse_binary(1)?;
        if !self.eat_noexpect(TokenKind::Question) {
            return Ok(cond);
        }

        let then = self.parse_expr()?;
        self.expect(TokenKind::Colon)?;
        let els = if self.lambda_ahead() {
            self.parse_lambda()?
        } else {
            self.parse_ternary()?
        };

        Ok(self.mk_expr(
            lo,
            ExprKind::Ternary {
                cond: Box::new(cond),
                then: Box::new(then),
                els: Box::new(els),
            },
        ))
    }

    fn parse_binary(&mut self, min_precedence: u8) -> PResult<Expr> {
        let lo = self.token.span;
        let mut lhs = self.parse_unary()?;

        loop {
            if self.token.is_keyword(kw::Instanceof) {
                if INSTANCEOF_PRECEDENCE < min_precedence {
                    return Ok(lhs);
                }
                self.bump();
                let pat = self.parse_instanceof_pat()?;
                lhs = self.mk_expr(
                    lo,
                    ExprKind::InstanceOf {
                        expr: Box::new(lhs),
                        pat: Box::new(pat),
                    },
                );
                continue;
            }

            let Some((precedence, op)) = binary_op(self.token.kind) else {
                return Ok(lhs);
            };
            if precedence < min_precedence {
                return Ok(lhs);
            }

            self.bump();
            let rhs = self.parse_binary(precedence + 1)?;
            lhs = self.mk_expr(
                lo,
                ExprKind::Binary {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
            );
        }
    }

    fn parse_unary(&mut self) -> PResult<Expr> {
        let lo = self.token.span;

        if let Some(op) = prefix_op(self.token.kind) {
            self.bump();
            let expr = self.parse_unary()?;
            return Ok(self.mk_expr(
                lo,
                ExprKind::Unary {
                    op,
                    expr: Box::new(expr),
                },
            ));
        }

        if self.eat_keyword_noexpect(kw::Await) {
            let expr = self.parse_unary()?;
            return Ok(self.mk_expr(lo, ExprKind::Await(Box::new(expr))));
        }

        if self.break_and_eat(TokenKind::And) {
            let mutable = self.eat_keyword_noexpect(kw::Mut);
            let expr = self.parse_unary()?;
            return Ok(self.mk_expr(
                lo,
                ExprKind::Borrow {
                    mutable,
                    expr: Box::new(expr),
                },
            ));
        }

        if self.cast_ahead() {
            self.bump();
            let ty = self.parse_ty()?;
            self.expect(TokenKind::CloseParen)?;
            let expr = self.parse_unary()?;
            return Ok(self.mk_expr(
                lo,
                ExprKind::Cast {
                    ty,
                    expr: Box::new(expr),
                },
            ));
        }

        let primary = self.parse_primary()?;
        self.parse_postfix(lo, primary)
    }

    fn parse_primary(&mut self) -> PResult<Expr> {
        let lo = self.token.span;
        if let TokenKind::Literal(lit) = self.token.kind
            && Self::is_interpolated(lit)
        {
            self.bump();
            return self.parse_interpolated(lit, lo);
        }
        let kind = match self.token.kind {
            TokenKind::Literal(lit) => ExprKind::Lit(lit),
            TokenKind::Ident(kw::True) => ExprKind::Bool(true),
            TokenKind::Ident(kw::False) => ExprKind::Bool(false),
            TokenKind::Ident(kw::Null) => ExprKind::Null,
            TokenKind::Ident(kw::This) => ExprKind::This,
            TokenKind::Ident(kw::Super) => ExprKind::Super,
            TokenKind::Ident(kw::New) => return self.parse_new(),
            TokenKind::Ident(kw::Switch) => return self.parse_switch_expr(),
            TokenKind::OpenParen => {
                self.bump();
                let expr = self.parse_expr()?;
                self.expect(TokenKind::CloseParen)?;
                return Ok(self.mk_expr(lo, expr.kind));
            }
            TokenKind::Ident(name) if !name.is_keyword() => ExprKind::Name(Ident::new(name, lo)),
            TokenKind::Ident(name)
                if PrimitiveTy::from_symbol(name).is_some()
                    && matches!(self.look_ahead(1), TokenKind::Dot | TokenKind::PathSep) =>
            {
                ExprKind::Name(Ident::new(name, lo))
            }
            _ => {
                self.expected.push(Expected::Expr);
                return Err(self.unexpected());
            }
        };

        self.bump();
        Ok(Expr { kind, span: lo })
    }

    fn parse_new(&mut self) -> PResult<Expr> {
        let lo = self.token.span;
        self.bump();
        let array_lengths = std::mem::replace(&mut self.array_lengths, true);
        let ty = self.parse_ty();
        self.array_lengths = array_lengths;
        let ty = ty?;

        let kind = match self.token.kind {
            TokenKind::OpenParen => ExprKind::New {
                ty,
                args: self.parse_args()?,
            },
            TokenKind::OpenBracket => {
                self.bump();
                let len = self.parse_expr()?;
                self.expect(TokenKind::CloseBracket)?;
                ExprKind::NewArray {
                    elem: ty,
                    len: Box::new(len),
                }
            }
            TokenKind::OpenBrace if matches!(ty.kind, TyKind::Array(_)) => ExprKind::ArrayInit {
                ty: Some(ty),
                elems: self.parse_array_elems()?,
            },
            _ => {
                self.expected.push(Expected::Token(TokenKind::OpenParen));
                self.expected.push(Expected::Token(TokenKind::OpenBracket));
                return Err(self.unexpected());
            }
        };

        Ok(self.mk_expr(lo, kind))
    }

    fn parse_postfix(&mut self, lo: Span, mut expr: Expr) -> PResult<Expr> {
        loop {
            let kind = match self.token.kind {
                TokenKind::Dot | TokenKind::QuestionDot => {
                    let safe = self.token.kind == TokenKind::QuestionDot;
                    self.bump();
                    let type_args = self.parse_generic_args()?;
                    let name = self.parse_ident()?;
                    if !type_args.is_empty() && self.token.kind != TokenKind::OpenParen {
                        self.expected.push(Expected::Token(TokenKind::OpenParen));
                        return Err(self.unexpected());
                    }
                    if self.token.kind == TokenKind::OpenParen {
                        ExprKind::MethodCall {
                            receiver: Some(Box::new(expr)),
                            type_args,
                            name,
                            args: self.parse_args()?,
                            safe,
                        }
                    } else {
                        ExprKind::Field {
                            expr: Box::new(expr),
                            name,
                            safe,
                        }
                    }
                }
                TokenKind::OpenParen => match expr.kind {
                    ExprKind::Name(name) => ExprKind::MethodCall {
                        receiver: None,
                        type_args: Vec::new(),
                        name,
                        args: self.parse_args()?,
                        safe: false,
                    },
                    ExprKind::This | ExprKind::Super => ExprKind::Call {
                        callee: Box::new(expr),
                        args: self.parse_args()?,
                    },
                    _ => return Ok(expr),
                },
                TokenKind::OpenBracket => {
                    self.bump();
                    let index = self.parse_expr()?;
                    self.expect(TokenKind::CloseBracket)?;
                    ExprKind::Index {
                        expr: Box::new(expr),
                        index: Box::new(index),
                    }
                }
                TokenKind::PlusPlus | TokenKind::MinusMinus => {
                    let op = if self.token.kind == TokenKind::PlusPlus {
                        UnOp::PostInc
                    } else {
                        UnOp::PostDec
                    };
                    self.bump();
                    ExprKind::Unary {
                        op,
                        expr: Box::new(expr),
                    }
                }
                TokenKind::Ident(kw::With) if self.look_ahead(1) == TokenKind::OpenBrace => {
                    self.bump();
                    ExprKind::With {
                        base: Box::new(expr),
                        fields: self.parse_field_inits()?,
                    }
                }
                TokenKind::PathSep => {
                    self.bump();
                    let name = if self.eat_keyword_noexpect(kw::New) {
                        Ident::new(kw::New, self.prev_token.span)
                    } else {
                        self.parse_ident()?
                    };
                    ExprKind::MethodRef {
                        expr: Box::new(expr),
                        name,
                    }
                }
                _ => return Ok(expr),
            };
            expr = self.mk_expr(lo, kind);
        }
    }

    fn parse_field_inits(&mut self) -> PResult<Vec<FieldInit>> {
        let open = self.expect(TokenKind::OpenBrace)?;
        let mut fields = Vec::new();
        loop {
            if self.eat(TokenKind::CloseBrace) {
                break;
            }
            let lo = self.token.span;
            let name = self.parse_ident()?;
            self.expect(TokenKind::Eq)?;
            let value = self.parse_expr()?;
            fields.push(FieldInit {
                name,
                value,
                span: lo.to(self.prev_token.span),
            });
            if !self.eat(TokenKind::Comma) {
                self.expect(TokenKind::CloseBrace)?;
                break;
            }
        }
        if fields.is_empty() {
            self.emit(
                Diagnostic::error("`with` needs at least one field")
                    .with_span(open.to(self.prev_token.span))
                    .with_help("write the fields to change, like `with { email = \"...\" }`"),
            );
        }
        Ok(fields)
    }

    pub(crate) fn parse_args(&mut self) -> PResult<Vec<Expr>> {
        self.expect(TokenKind::OpenParen)?;
        let mut args = Vec::new();
        if self.eat(TokenKind::CloseParen) {
            return Ok(args);
        }

        loop {
            args.push(self.parse_expr()?);
            if self.eat(TokenKind::CloseParen) {
                return Ok(args);
            }
            self.expect(TokenKind::Comma)?;
        }
    }

    fn parse_switch_expr(&mut self) -> PResult<Expr> {
        let lo = self.token.span;
        self.bump();
        let scrutinee = self.parse_paren_expr()?;
        let open = self.expect(TokenKind::OpenBrace)?;
        let mut arms = Vec::new();

        loop {
            if self.eat_noexpect(TokenKind::CloseBrace) {
                return Ok(self.mk_expr(
                    lo,
                    ExprKind::Switch {
                        scrutinee: Box::new(scrutinee),
                        arms,
                    },
                ));
            }
            if self.token.kind == TokenKind::Eof {
                return Err(self.unclosed_delimiter(open));
            }

            match self.parse_switch_expr_arm() {
                Ok(arm) => arms.push(arm),
                Err(error) => {
                    self.recover_to_member_end();
                    if self.token.kind == TokenKind::Eof {
                        return Err(error);
                    }
                }
            }
        }
    }

    fn parse_switch_expr_arm(&mut self) -> PResult<SwitchExprArm> {
        let lo = self.token.span;
        let label = self.parse_case_label()?;

        let body = if self.token.kind == TokenKind::OpenBrace {
            SwitchExprBody::Block(self.parse_block()?)
        } else if self.eat_keyword_noexpect(kw::Throw) {
            let expr = self.parse_expr()?;
            self.expect_semi()?;
            SwitchExprBody::Throw(expr)
        } else {
            let expr = self.parse_expr()?;
            self.expect_semi()?;
            SwitchExprBody::Expr(expr)
        };

        Ok(SwitchExprArm {
            label,
            body,
            span: lo.to(self.prev_token.span),
        })
    }

    pub(crate) fn parse_initializer(&mut self) -> PResult<Expr> {
        if self.token.kind != TokenKind::OpenBrace {
            return self.parse_expr();
        }

        let lo = self.token.span;
        let elems = self.parse_array_elems()?;
        Ok(self.mk_expr(lo, ExprKind::ArrayInit { ty: None, elems }))
    }

    fn parse_array_elems(&mut self) -> PResult<Vec<Expr>> {
        self.expect(TokenKind::OpenBrace)?;
        let mut elems = Vec::new();

        loop {
            if self.eat(TokenKind::CloseBrace) {
                return Ok(elems);
            }
            elems.push(self.parse_initializer()?);
            if !self.eat(TokenKind::Comma) {
                self.expect(TokenKind::CloseBrace)?;
                return Ok(elems);
            }
        }
    }

    fn parse_lambda(&mut self) -> PResult<Expr> {
        let lo = self.token.span;
        let moves = self.move_lambda_ahead();
        if moves {
            self.bump();
        }
        let params = if self.token.kind == TokenKind::OpenParen {
            self.parse_lambda_params()?
        } else {
            let name = self.parse_ident()?;
            vec![LambdaParam {
                ty: None,
                name,
                span: name.span,
            }]
        };

        self.expect(TokenKind::Arrow)?;
        let body = if self.token.kind == TokenKind::OpenBrace {
            LambdaBody::Block(self.parse_block()?)
        } else {
            LambdaBody::Expr(self.parse_expr()?)
        };

        Ok(self.mk_expr(
            lo,
            ExprKind::Lambda {
                moves,
                params,
                body: Box::new(body),
            },
        ))
    }

    fn parse_lambda_params(&mut self) -> PResult<Vec<LambdaParam>> {
        self.expect(TokenKind::OpenParen)?;
        let mut params = Vec::new();
        if self.eat(TokenKind::CloseParen) {
            return Ok(params);
        }

        loop {
            let lo = self.token.span;
            let untyped = self.token.ident().is_some()
                && matches!(self.look_ahead(1), TokenKind::Comma | TokenKind::CloseParen);
            let ty = if untyped {
                None
            } else {
                Some(self.parse_ty()?)
            };
            let name = self.parse_ident()?;
            params.push(LambdaParam {
                ty,
                name,
                span: lo.to(self.prev_token.span),
            });

            if self.eat(TokenKind::CloseParen) {
                return Ok(params);
            }
            self.expect(TokenKind::Comma)?;
        }
    }

    fn mk_expr(&self, lo: Span, kind: ExprKind) -> Expr {
        Expr {
            kind,
            span: lo.to(self.prev_token.span),
        }
    }
}
