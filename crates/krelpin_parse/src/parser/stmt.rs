use krelpin_ast::ast::{
    Block, Catch, Expr, ExprKind, Local, Stmt, StmtKind, SwitchArm, Ty, TyKind, UnOp,
};
use krelpin_ast::token::TokenKind;
use krelpin_errors::Diagnostic;
use krelpin_span::{Span, kw};

use super::{PResult, Parser};

impl Parser<'_> {
    pub(crate) fn parse_block(&mut self) -> PResult<Block> {
        let open = self.expect(TokenKind::OpenBrace)?;
        let mut stmts = Vec::new();

        loop {
            self.parse_docs();
            if self.eat_noexpect(TokenKind::CloseBrace) {
                return Ok(Block {
                    stmts,
                    span: open.to(self.prev_token.span),
                });
            }
            if self.token.kind == TokenKind::Eof {
                return Err(self.unclosed_delimiter(open));
            }

            match self.parse_stmt() {
                Ok(stmt) => stmts.push(stmt),
                Err(error) => {
                    self.recover_to_member_end();
                    if self.token.kind == TokenKind::Eof {
                        return Err(error);
                    }
                }
            }
        }
    }

    pub(crate) fn parse_stmt(&mut self) -> PResult<Stmt> {
        let lo = self.token.span;
        let kind = match self.token.kind {
            TokenKind::OpenBrace => StmtKind::Block(self.parse_block()?),
            TokenKind::Semi => {
                self.bump();
                StmtKind::Empty
            }
            TokenKind::Ident(kw::If) => self.parse_if()?,
            TokenKind::Ident(kw::While) => self.parse_while()?,
            TokenKind::Ident(kw::Do) => self.parse_do_while()?,
            TokenKind::Ident(kw::For) => self.parse_for()?,
            TokenKind::Ident(kw::Switch) => self.parse_switch()?,
            TokenKind::Ident(kw::Try) => self.parse_try()?,
            TokenKind::Ident(kw::Return) => {
                self.bump();
                let value = if self.token.kind == TokenKind::Semi {
                    None
                } else {
                    Some(self.parse_expr()?)
                };
                self.expect_semi()?;
                StmtKind::Return(value)
            }
            TokenKind::Ident(kw::Yield) => {
                self.bump();
                let value = self.parse_expr()?;
                self.expect_semi()?;
                StmtKind::Yield(value)
            }
            TokenKind::Ident(kw::Throw) => {
                self.bump();
                let value = self.parse_expr()?;
                self.expect_semi()?;
                StmtKind::Throw(value)
            }
            TokenKind::Ident(kw::Break) => {
                self.bump();
                self.expect_semi()?;
                StmtKind::Break
            }
            TokenKind::Ident(kw::Continue) => {
                self.bump();
                self.expect_semi()?;
                StmtKind::Continue
            }
            TokenKind::Ident(kw::Final) => {
                let final_kw = self.final_before_decl(false)?;
                let local = self.parse_local(final_kw)?;
                self.expect_semi()?;
                StmtKind::Local(local)
            }
            _ if self.local_decl_ahead(false) => {
                let local = self.parse_local(None)?;
                self.expect_semi()?;
                StmtKind::Local(local)
            }
            _ => {
                let expr = self.parse_expr()?;
                self.check_expr_stmt(&expr);
                self.expect_semi()?;
                StmtKind::Expr(expr)
            }
        };

        Ok(Stmt {
            kind,
            span: lo.to(self.prev_token.span),
        })
    }

    fn parse_local(&mut self, final_kw: Option<Span>) -> PResult<Local> {
        let ty = self.parse_local_ty()?;
        let name = self.parse_ident()?;
        let init = if self.eat(TokenKind::Eq) {
            Some(self.parse_initializer()?)
        } else {
            None
        };
        Ok(Local {
            final_kw,
            ty,
            name,
            init,
        })
    }

    fn final_before_decl(&mut self, in_for: bool) -> PResult<Option<Span>> {
        let final_kw = self.token.span;
        self.bump();
        if self.local_decl_ahead(in_for) {
            return Ok(Some(final_kw));
        }
        Err(self.emit(
            Diagnostic::error("expected a variable declaration after `final`")
                .with_span(final_kw)
                .with_label("`final` here marks a variable that is assigned only once")
                .with_help("write `final Type name = value;`"),
        ))
    }

    fn parse_local_ty(&mut self) -> PResult<Ty> {
        let ty = self.parse_ty()?;
        if !is_var(&ty) {
            return Ok(ty);
        }
        Err(self.emit(
            Diagnostic::error("invalid variable declaration")
                .with_span(ty.span)
                .with_label("`var` is not supported")
                .with_help("write the type of the variable instead of `var`"),
        ))
    }

    fn check_expr_stmt(&self, expr: &Expr) {
        let is_statement = matches!(
            expr.kind,
            ExprKind::Assign { .. }
                | ExprKind::MethodCall { .. }
                | ExprKind::Call { .. }
                | ExprKind::New { .. }
                | ExprKind::Await(_)
                | ExprKind::Unary {
                    op: UnOp::PreInc | UnOp::PreDec | UnOp::PostInc | UnOp::PostDec,
                    ..
                }
        );
        if is_statement {
            return;
        }

        self.emit(
            Diagnostic::error("expression is not a statement")
                .with_span(expr.span)
                .with_help(
                    "only assignments, increments, method calls, object creation \
                     and `await` can be used as statements",
                ),
        );
    }

    pub(crate) fn parse_paren_expr(&mut self) -> PResult<Expr> {
        self.expect(TokenKind::OpenParen)?;
        let expr = self.parse_expr()?;
        self.expect(TokenKind::CloseParen)?;
        Ok(expr)
    }

    fn parse_if(&mut self) -> PResult<StmtKind> {
        self.bump();
        let cond = self.parse_paren_expr()?;
        let then = Box::new(self.parse_stmt()?);
        let els = if self.eat_keyword_noexpect(kw::Else) {
            Some(Box::new(self.parse_stmt()?))
        } else {
            None
        };
        Ok(StmtKind::If { cond, then, els })
    }

    fn parse_while(&mut self) -> PResult<StmtKind> {
        self.bump();
        let cond = self.parse_paren_expr()?;
        let body = Box::new(self.parse_stmt()?);
        Ok(StmtKind::While { cond, body })
    }

    fn parse_do_while(&mut self) -> PResult<StmtKind> {
        self.bump();
        let body = Box::new(self.parse_stmt()?);
        if !self.eat_keyword(kw::While) {
            return Err(self.unexpected());
        }
        let cond = self.parse_paren_expr()?;
        self.expect_semi()?;
        Ok(StmtKind::DoWhile { body, cond })
    }

    fn parse_for(&mut self) -> PResult<StmtKind> {
        self.bump();
        self.expect(TokenKind::OpenParen)?;

        let mut init = Vec::new();
        let lo = self.token.span;
        let final_kw = if self.token.is_keyword(kw::Final) {
            self.final_before_decl(true)?
        } else {
            None
        };
        if final_kw.is_some() || self.local_decl_ahead(true) {
            let ty = self.parse_local_ty()?;
            let name = self.parse_ident()?;

            if self.eat_noexpect(TokenKind::Colon) {
                let iter = self.parse_expr()?;
                self.expect(TokenKind::CloseParen)?;
                let body = Box::new(self.parse_stmt()?);
                return Ok(StmtKind::ForEach {
                    final_kw,
                    ty,
                    name,
                    iter,
                    body,
                });
            }

            let value = if self.eat(TokenKind::Eq) {
                Some(self.parse_initializer()?)
            } else {
                None
            };
            init.push(Stmt {
                kind: StmtKind::Local(Local {
                    final_kw,
                    ty,
                    name,
                    init: value,
                }),
                span: lo.to(self.prev_token.span),
            });
        } else if self.token.kind != TokenKind::Semi {
            for expr in self.parse_expr_list()? {
                init.push(Stmt {
                    span: expr.span,
                    kind: StmtKind::Expr(expr),
                });
            }
        }
        self.expect(TokenKind::Semi)?;

        let cond = if self.token.kind == TokenKind::Semi {
            None
        } else {
            Some(self.parse_expr()?)
        };
        self.expect(TokenKind::Semi)?;

        let update = if self.token.kind == TokenKind::CloseParen {
            Vec::new()
        } else {
            self.parse_expr_list()?
        };
        self.expect(TokenKind::CloseParen)?;

        let body = Box::new(self.parse_stmt()?);
        Ok(StmtKind::For {
            init,
            cond,
            update,
            body,
        })
    }

    fn parse_expr_list(&mut self) -> PResult<Vec<Expr>> {
        let mut exprs = vec![self.parse_expr()?];
        while self.eat(TokenKind::Comma) {
            exprs.push(self.parse_expr()?);
        }
        Ok(exprs)
    }

    fn parse_switch(&mut self) -> PResult<StmtKind> {
        self.bump();
        let scrutinee = self.parse_paren_expr()?;
        let open = self.expect(TokenKind::OpenBrace)?;
        let mut arms = Vec::new();

        loop {
            if self.eat_noexpect(TokenKind::CloseBrace) {
                return Ok(StmtKind::Switch { scrutinee, arms });
            }
            if self.token.kind == TokenKind::Eof {
                return Err(self.unclosed_delimiter(open));
            }

            match self.parse_switch_arm() {
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

    fn parse_switch_arm(&mut self) -> PResult<SwitchArm> {
        let lo = self.token.span;
        let label = self.parse_case_label()?;
        let body = Box::new(self.parse_stmt()?);

        Ok(SwitchArm {
            label,
            body,
            span: lo.to(self.prev_token.span),
        })
    }

    fn parse_try(&mut self) -> PResult<StmtKind> {
        let try_span = self.token.span;
        self.bump();
        let body = self.parse_block()?;

        let mut catches = Vec::new();
        while self.token.is_keyword(kw::Catch) {
            let lo = self.token.span;
            self.bump();
            self.expect(TokenKind::OpenParen)?;
            let final_kw = self.token.span;
            let final_kw = self.eat_keyword_noexpect(kw::Final).then_some(final_kw);
            let mut tys = vec![self.parse_ty()?];
            while self.eat_noexpect(TokenKind::Or) {
                tys.push(self.parse_ty()?);
            }
            let name = self.parse_ident()?;
            self.expect(TokenKind::CloseParen)?;
            let body = self.parse_block()?;
            catches.push(Catch {
                final_kw,
                tys,
                name,
                body,
                span: lo.to(self.prev_token.span),
            });
        }

        let finally = if self.eat_keyword_noexpect(kw::Finally) {
            Some(self.parse_block()?)
        } else {
            None
        };

        if catches.is_empty() && finally.is_none() {
            self.emit(
                Diagnostic::error("`try` without `catch` or `finally`")
                    .with_span(try_span)
                    .with_help("add a `catch` block, a `finally` block, or remove the `try`"),
            );
        }

        Ok(StmtKind::Try {
            body,
            catches,
            finally,
        })
    }
}

fn is_var(ty: &Ty) -> bool {
    match &ty.kind {
        TyKind::Path { path, args, .. } => {
            args.is_empty()
                && matches!(path.segments.as_slice(), [segment] if segment.name.as_str() == "var")
        }
        _ => false,
    }
}
