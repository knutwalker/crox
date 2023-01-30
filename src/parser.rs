//! Book-flavored BNF-ish:
//!
//! ```bnf
//!     program := declaration* EOF ;
//! declaration := classDecl | funDecl | varDecl | statement ;
//!
//!   classDecl := "class" IDENTIFIER ( "<" IDENTIFIER )? "{" member* "}" ;
//!      member := method | property ;
//!      method := "class"? function ;
//!    property := IDENTIFIER block ;
//!     funDecl := "fun" function ;
//!    function := IDENTIFIER "(" parameters? ")" block ;
//!     varDecl := "var" IDENTIFIER ( "=" expression )? ";" ;
//!   statement := exprStmt | forStmt | ifStmt | printStmt | returnStmt | whileStmt | block;
//!
//!    exprStmt := expression ";" ;
//!     forStmt := "for" "(" ( varDecl | exprStmt | ";" ) expression? ";" expression? ")" statement ;
//!      ifStmt := "if" "(" expression ")" statement ( "else" statement )? ;
//!   printStmt := "print" expression ";" ;
//!  returnStmt := "return" expression? ";" ;
//!   whileStmt := "while" "(" expression ")" statement ;
//!       block := "{" declaration* "}" ;
//!
//!  expression := assignment ;
//!  assignment := ( call "." )? IDENTIFIER "=" assignment | logic_or ;
//!    logic_or := logic_and ( "or" logic_and )* ;
//!   logic_and := equality ( "and" equality )* ;
//!    eqaulity := comparison ( ( "==" | "!=" ) comparison )* ;
//!  comparison := term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
//!        term := factor ( ( "+" | "-" ) factor )* ;
//!      factor := unary ( ( "*" | "/" ) unary )* ;
//!       unary := ( "!" | "-" ) unary | call ;
//!        call := primary ( "(" arguments? ")" | "." IDENTIFIER )* ;
//!     primary := NUMBER | STRING | IDENTIFIER | funDecl |
//!                "true" | "false" | "nil" | "this" |
//!                "(" expression ")" | "super" . IDENTIFIER ;
//!
//!   arguments := expression ( "," expression )* ;
//!  parameters := IDENTIFIER ( "," IDENTIFIER )* ;
//!```
use crate::{
    BinaryOp, Bump, CroxError, CroxErrorKind, Expr, ExprNode, ExpressionRule, FunctionDecl,
    FunctionDef, FunctionKind, Ident, Node, Range, Result, Source, Span, Spannable, StatementRule,
    Stmt, StmtNode, Token, TokenSet, TokenType, TooMany, UnaryOp, Var,
};
use std::{iter::Peekable, marker::PhantomData};
use TokenType::*;

type Tok = (TokenType, Span);

pub fn expr_parser<'env, I>(
    source: Source<'env>,
    tokens: I,
    arena: &'env Bump,
) -> Parser<'env, ExpressionRule, UnpackToken<I::IntoIter>>
where
    I: IntoIterator<Item = Token>,
{
    any_parser(source, tokens, arena)
}

pub fn stmt_parser<'env, I>(
    source: Source<'env>,
    tokens: I,
    arena: &'env Bump,
) -> Parser<'env, StatementRule, UnpackToken<I::IntoIter>>
where
    I: IntoIterator<Item = Token>,
{
    any_parser(source, tokens, arena)
}

fn any_parser<'env, R, I>(
    source: Source<'env>,
    tokens: I,
    arena: &'env Bump,
) -> Parser<'env, R, UnpackToken<I::IntoIter>>
where
    I: IntoIterator<Item = Token>,
{
    let tokens = UnpackToken {
        inner: tokens.into_iter(),
    }
    .peekable();
    Parser::new(source, tokens, arena)
}

pub struct Parser<'env, R, T: Iterator<Item = Tok>> {
    source: Source<'env>,
    tokens: Peekable<T>,
    arena: &'env Bump,
    _rule: PhantomData<R>,
}

macro_rules! peek {
    ($this:ident, { $($pat:pat => $expr:expr),+ $(,)? }) => {
        match $this.tokens.peek() {
            $(Some(&$pat) => {
                let _ = $this.tokens.next();
                Some($expr)
            }),+,
            _ => None,
        }
    };

    ($this:ident, $($pat:pat),+ $(,)?) => {
        match $this.tokens.peek() {
            $(Some(&($pat, _)) => {
                let _ = $this.tokens.next();
                true
            }),+,
            _ => false,
        }
    };
}

macro_rules! bin_op {
    ($this:ident, $descent:ident, { $($pat:pat => $expr:expr),+ $(,)? }) => {{
        let mut lhs = $this.$descent()?;
        loop {
            let op = match peek!($this, { $($pat => $expr),+ }) {
                Some(op) => op,
                None => break,
            };
            let rhs = $this.$descent()?;
            let left = lhs.alloc(&$this.arena);
            let right = rhs.alloc(&$this.arena);
            let span = left.span.union(right.span);
            lhs = Expr::binary(left, op, right).at(span);
        }
        Ok(lhs)
    }};
}

impl<'env, R, T: Iterator<Item = Tok>> Parser<'env, R, T> {
    fn new(source: Source<'env>, tokens: Peekable<T>, arena: &'env Bump) -> Self {
        Self {
            source,
            tokens,
            arena,
            _rule: PhantomData,
        }
    }
}

impl<'env, R, T: Iterator<Item = Tok>> Parser<'env, R, T> {
    fn sync_declaration(&mut self) -> Result<StmtNode<'env>> {
        match self.declaration() {
            Ok(stmt) => Ok(stmt),
            Err(e) => {
                self.synchronize();
                Err(e)
            }
        }
    }

    /// declaration := classDecl | funDecl | varDecl | statement ;
    fn declaration(&mut self) -> Result<StmtNode<'env>> {
        peek!(self, {
            (Var, span) => self.var_decl(span),
            (Class, span) => self.class_decl(span),
            (Fun, span) => self.fun_decl(span),
        })
        .transpose()?
        .map_or_else(|| self.statement(), Ok)
    }

    ///   classDecl := "class" IDENTIFIER ( "<" IDENTIFIER )? "{" member* "}" ;
    fn class_decl(&mut self, start: Span) -> Result<StmtNode<'env>> {
        let name = self
            .ident(start)
            .map_err(|c| c.with_payload(ExpectedFn(FunctionKind::Class)))?;

        let extends = self.tokens.next_if(|&(token, _)| token == Less);
        let superclass = extends
            .map(|(_, span)| {
                self.ident(span)
                    .map(|name| name.map(|v| Var::new(v, self.arena)))
                    .map_err(|c| c.with_payload(ExpectedFn(FunctionKind::Class)))
            })
            .transpose()?;

        let open_brace = self.expect(LeftBrace, EndOfInput::expected(LeftBrace, name.span))?;

        let mut members = Vec::new();

        loop {
            // not peek! because we don't want to consume the token
            // if it's a RightBrace, we consume it after the loop
            // otherwise it's consumed by function_decl
            match self.tokens.peek() {
                Some(&(RightBrace, _)) | None => {
                    break;
                }
                Some(&(_, fn_span)) => {
                    let method = self.member(fn_span)?;
                    members.push(method);
                }
            }
        }

        let members = self.arena.alloc_slice_fill_iter(members);

        let close_brace = self.expect(RightBrace, EndOfInput::Unclosed(LeftBrace, open_brace))?;
        let stmt = Stmt::class(name, superclass, members);
        let span = open_brace.union(close_brace);
        Ok(stmt.at(span))
    }

    ///      member := method | property ;
    ///      method := "class"? function ;
    fn member(&mut self, start: Span) -> Result<Node<FunctionDecl<'env>>> {
        let class = self.tokens.next_if(|&(token, _)| token == Class);
        match class {
            Some((_, class_span)) => self.function_decl(FunctionKind::ClassMethod, class_span),
            None => self.function_or_property(start),
        }
    }

    ///     funDecl := "fun" function ;
    ///    function := IDENTIFIER "(" parameters? ")" block ;
    ///  parameters := IDENTIFIER ( "," IDENTIFIER )* ;
    fn fun_decl(&mut self, start: Span) -> Result<StmtNode<'env>> {
        self.function_decl(FunctionKind::Function, start)
            .map(|f| f.map(Stmt::Function))
    }

    fn function_decl(
        &mut self,
        kind: FunctionKind,
        start: Span,
    ) -> Result<Node<FunctionDecl<'env>>> {
        let name = self
            .ident(start)
            .map_err(|c| c.with_payload(ExpectedFn(kind)))?;

        let fn_def = self.function_def(name.span)?;
        let span = start.union(fn_def.span);

        Ok(Stmt::fun(name, kind, fn_def.item).at(span))
    }

    ///    property := IDENTIFIER block ;
    fn function_or_property(&mut self, start: Span) -> Result<Node<FunctionDecl<'env>>> {
        let name = self
            .ident(start)
            .map_err(|c| c.with_payload(ExpectedFn(FunctionKind::Method)))?;

        let (is_property, fn_def) = match self.tokens.peek() {
            Some(&(LeftBrace, left_brace)) => {
                (FunctionKind::Property, self.property_def(left_brace)?)
            }
            _ => (FunctionKind::Method, self.function_def(name.span)?),
        };

        let span = start.union(fn_def.span);
        let fn_item = Stmt::fun(name, is_property, fn_def.item).at(span);
        Ok(fn_item)
    }

    fn property_def(&mut self, start: Span) -> Result<Node<FunctionDef<'env>>> {
        self.function_body(&[], start, start)
    }

    fn function_def(&mut self, start: Span) -> Result<Node<FunctionDef<'env>>> {
        let params = self.parens_list::<_, Parameters>(start, true, Parser::ident)?;

        self.function_body(&params.item, start, params.span)
    }

    fn function_body(
        &mut self,
        params: &[Ident<'env>],
        fn_start: Span,
        body_start: Span,
    ) -> Result<Node<FunctionDef<'env>>> {
        let open_brace = self.expect(LeftBrace, EndOfInput::expected(LeftBrace, body_start))?;
        let body = self.block(open_brace)?;
        let span = fn_start.union(body.span);

        let params = self.arena.alloc_slice_copy(params);
        let body = self.arena.alloc_slice_clone(&body.item);
        Ok(FunctionDef::new(params, body).at(span))
    }

    ///     varDecl := "var" IDENTIFIER ( "=" expression )? ";" ;
    fn var_decl(&mut self, span: Span) -> Result<StmtNode<'env>> {
        let name = self.ident(span)?;

        let init = peek!(self, {
            (Equal, _) => self.expression()?,
        });

        let init = init.map(|i| i.alloc(self.arena));
        let end_span = self.expect(Semicolon, EndOfInput::unclosed(Identifier, span))?;

        Ok(Stmt::var(name, init).at(span.union(end_span)))
    }

    ///   statement := exprStmt | forStmt | ifStmt | printStmt | whileStmt | block;
    fn statement(&mut self) -> Result<StmtNode<'env>> {
        let stmt = peek!(self, {
            (For, span) => self.for_statement(span)?,
            (If, span) => self.if_statement(span)?,
            (Print, span) => self.print_statement(span)?,
            (Return, span) => self.return_statement(span)?,
            (While, span) => self.while_statement(span)?,
            (LeftBrace, span) => self.block(span)?.map(|stmts| {
                let stmts = self.arena.alloc_slice_fill_iter(stmts);
                Stmt::block(stmts)
            }),
        });
        match stmt {
            Some(stmt) => Ok(stmt),
            None => self.expr_statement(),
        }
    }

    ///    exprStmt := expression ";" ;
    fn expr_statement(&mut self) -> Result<StmtNode<'env>> {
        let expr = self.expression()?;
        let expr = expr.alloc(self.arena);
        let end_span = self.expect(Semicolon, EndOfInput::expected(Semicolon, expr.span))?;
        let span = expr.span.union(end_span);
        let stmt = Stmt::expression(expr);
        Ok(stmt.at(span))
    }

    ///     forStmt := "for" "(" ( varDecl | exprStmt | ";" ) expression? ";" expression? ")" statement ;
    fn for_statement(&mut self, for_span: Span) -> Result<StmtNode<'env>> {
        let paren = self.expect(LeftParen, EndOfInput::expected(LeftParen, for_span))?;

        // cannot use peek since we don't consume in the catch all case
        let (init_span, initializer) = match self.tokens.peek() {
            Some(&(Var, span)) => {
                let _ = self.tokens.next();
                let decl = self.var_decl(span)?;
                (Span::from(span.union(decl.span)), Some(decl))
            }
            Some(&(Semicolon, span)) => {
                let _ = self.tokens.next();
                (span, None)
            }
            Some(_) => {
                let expr = self.expr_statement()?;
                (expr.span, Some(expr))
            }
            None => Err(EndOfInput::expected(
                TokenSet::from_iter([Semicolon, Var]),
                paren,
            ))?,
        };

        // cannot use peek since we don't consume the token
        let condition = match self.tokens.peek() {
            Some(&(Semicolon, span)) => Expr::tru().at(span),
            Some(_) => self.expression()?,
            None => Err(EndOfInput::expected(Semicolon, init_span))?,
        };
        let cond_span = condition.span;

        let _ = self.expect(Semicolon, EndOfInput::expected(Semicolon, cond_span))?;

        // cannot use peek since we don't consume the token
        let (inc_span, increment) = match self.tokens.peek() {
            Some(&(RightParen, span)) => (span, None),
            Some(_) => {
                let expr = self.expression()?;
                (expr.span, Some(expr))
            }
            None => Err(EndOfInput::expected(RightBrace, cond_span))?,
        };

        let _ = self.expect(RightParen, EndOfInput::Unclosed(LeftParen, paren))?;

        let mut body = self.statement()?;
        let body_span = body.span;

        if let Some(increment) = increment {
            let increment = increment.alloc(self.arena);
            let increment = Stmt::expression(increment).at(inc_span);
            // the increment must happen in a separate, outer scope of the body
            // so we need to wrap the body in a block if it isn't already
            // and then wrap the body and the increment in their own block
            if !matches!(&body.item, Stmt::Block { .. }) {
                let inner_body = self.arena.alloc(body);
                let inner_body = std::slice::from_ref(inner_body);
                body = Stmt::block(inner_body).at(body_span);
            }
            let inner_body = self.arena.alloc_slice_fill_iter([body, increment]);
            body = Stmt::block(inner_body).at(body_span);
        };

        let condition = condition.alloc(self.arena);
        let body = body.alloc(self.arena);
        let body = Stmt::while_(condition, body).at(body_span);

        let body = match initializer {
            Some(init) => {
                let inner_body = self.arena.alloc_slice_fill_iter([init, body]);
                Stmt::block(inner_body)
            }
            None => body.item,
        };

        Ok(body.at(for_span.union(body_span)))
    }

    ///      ifStmt := "if" "(" expression ")" statement ( "else" statement )? ;
    fn if_statement(&mut self, span: Span) -> Result<StmtNode<'env>> {
        self.expect(LeftParen, EndOfInput::expected(LeftParen, span))?;
        let cond = self.expression()?;
        let cond = cond.alloc(self.arena);
        self.expect(RightParen, EndOfInput::unclosed(LeftParen, span))?;

        let then_ = self.statement()?;
        let then_ = then_.alloc(self.arena);
        // cannot rewrite this with peek! because we move cond into the match
        let stmt = match self.tokens.peek() {
            Some((Else, _)) => {
                let _ = self.tokens.next();
                let else_ = self.statement()?;
                let else_ = else_.alloc(self.arena);
                let span = span.union(else_.span);
                Stmt::if_else(cond, then_, else_).at(span)
            }
            _ => {
                let span = span.union(then_.span);
                Stmt::if_(cond, then_).at(span)
            }
        };

        Ok(stmt)
    }

    ///   printStmt := "print" expression ";" ;
    fn print_statement(&mut self, print_span: Span) -> Result<StmtNode<'env>> {
        let expr = self.expression()?;
        let expr = expr.alloc(self.arena);
        let end_span = self.expect(Semicolon, EndOfInput::Unclosed(Print, print_span))?;
        let stmt = Stmt::print(expr);
        Ok(stmt.at(print_span.union(end_span)))
    }

    ///  returnStmt := "return" expression? ";" ;
    fn return_statement(&mut self, span: Span) -> Result<StmtNode<'env>> {
        let expr = match self.tokens.peek() {
            Some(&(Semicolon, _)) => None,
            Some(_) => Some(self.expression()?.alloc(self.arena)),
            None => None,
        };
        let end_span = self.expect(Semicolon, EndOfInput::Unclosed(Return, span))?;

        Ok(Stmt::return_(expr).at(span.union(end_span)))
    }

    ///   whileStmt := "while" "(" expression ")" statement ;
    fn while_statement(&mut self, span: Span) -> Result<StmtNode<'env>> {
        self.expect(LeftParen, EndOfInput::expected(LeftParen, span))?;
        let cond = self.expression()?;
        let cond = cond.alloc(self.arena);
        self.expect(RightParen, EndOfInput::unclosed(LeftParen, span))?;

        let body = self.statement()?;
        let body = body.alloc(self.arena);
        let span = span.union(body.span);
        Ok(Stmt::while_(cond, body).at(span))
    }

    ///       block := "{" declaration* "}" ;
    fn block(&mut self, start: Span) -> Result<Node<Vec<StmtNode<'env>>>> {
        let mut stmts = Vec::new();

        let end = loop {
            // cannot use peek since we don't consume the token in the catch all case
            match self.tokens.peek() {
                Some(&(RightBrace, end)) => {
                    let _ = self.tokens.next();
                    break end;
                }
                Some(_) => {
                    stmts.push(self.sync_declaration()?);
                }
                _ => Err(EndOfInput::Unclosed(LeftBrace, start))?,
            };
        };

        Ok(stmts.at(start.union(end)))
    }

    ///  expression := assignment ;
    fn expression(&mut self) -> Result<ExprNode<'env>> {
        self.assignment()
    }

    ///  assignment := ( call "." )? IDENTIFIER "=" assignment | logic_or ;
    fn assignment(&mut self) -> Result<ExprNode<'env>> {
        let expr = self.logic_or()?;

        if peek!(self, Equal) {
            let value = self.assignment()?;
            let span = expr.span.union(value.span);
            let assign = match &expr.item {
                Expr::Var(Var { name, .. }) => {
                    let value = value.alloc(self.arena);
                    Expr::assign(name, value, self.arena)
                }
                Expr::Get { object, name } => {
                    let value = value.alloc(self.arena);
                    Expr::set(*object, *name, value)
                }
                _ => {
                    return Err(CroxErrorKind::InvalidAssignmentTarget.at(expr.span));
                }
            };

            return Ok(assign.at(span));
        }

        Ok(expr)
    }

    ///    logic_or := logic_and ( "or" logic_and )* ;
    fn logic_or(&mut self) -> Result<ExprNode<'env>> {
        let mut expr = self.logic_and()?;

        while peek!(self, Or) {
            let right = self.logic_and()?;
            let left = expr.alloc(self.arena);
            let right = right.alloc(self.arena);
            let span = left.span.union(right.span);
            expr = Expr::or(left, right).at(span);
        }

        Ok(expr)
    }

    ///   logic_and := equality ( "and" equality )* ;
    fn logic_and(&mut self) -> Result<ExprNode<'env>> {
        let mut expr = self.equality()?;

        while peek!(self, And) {
            let right = self.equality()?;
            let left = expr.alloc(self.arena);
            let right = right.alloc(self.arena);
            let span = left.span.union(right.span);
            expr = Expr::and(left, right).at(span);
        }

        Ok(expr)
    }

    ///    eqaulity := comparison ( ( "==" | "!=" ) comparison )* ;
    fn equality(&mut self) -> Result<ExprNode<'env>> {
        bin_op!(self, comparison, {
            (BangEqual, _) => BinaryOp::NotEquals,
            (EqualEqual, _) => BinaryOp::Equals,
        })
    }

    ///  comparison := term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
    fn comparison(&mut self) -> Result<ExprNode<'env>> {
        bin_op!(self, term, {
            (Greater, _) => BinaryOp::GreaterThan,
            (GreaterEqual, _) => BinaryOp::GreaterThanOrEqual,
            (Less, _) => BinaryOp::LessThan,
            (LessEqual, _) => BinaryOp::LessThanOrEqual,
        })
    }

    ///        term := factor ( ( "+" | "-" ) factor )* ;
    fn term(&mut self) -> Result<ExprNode<'env>> {
        bin_op!(self, factor, {
            (Plus, _) => BinaryOp::Add,
            (Minus, _) => BinaryOp::Sub,
        })
    }

    ///      factor := unary ( ( "*" | "/" ) unary )* ;
    fn factor(&mut self) -> Result<ExprNode<'env>> {
        bin_op!(self, unary, {
            (Star, _) => BinaryOp::Mul,
            (Slash, _) => BinaryOp::Div,
        })
    }

    ///       unary := ( "!" | "-" ) unary | call ;
    fn unary(&mut self) -> Result<ExprNode<'env>> {
        match peek!(self, {
            (Bang, span) => (UnaryOp::Not, span),
            (Minus, span) => (UnaryOp::Neg, span),
        }) {
            Some((op, span)) => {
                let inner = self.unary()?;
                let inner = inner.alloc(self.arena);
                let span = span.union(inner.span);
                Ok(Expr::unary(op, inner).at(span))
            }
            None => self.call(),
        }
    }

    ///        call := primary ( "(" arguments? ")" | "." IDENTIFIER )* ;
    fn call(&mut self) -> Result<ExprNode<'env>> {
        let mut expr = self.primary()?;

        loop {
            let next = peek!(self, {
                (LeftParen, span) => {
                    let (args, end) = self.arguments(span)?;
                    let args = self.arena.alloc_slice_fill_iter(args);
                    let inner = expr.alloc(self.arena);
                    let span = inner.span.union(end);
                    expr = Expr::call(inner, args).at(span);
                },
                (Dot, span) => {
                    let name = self.ident(span)?;
                    let inner = expr.alloc(self.arena);
                    let span = inner.span.union(name.span);
                    expr = Expr::get(inner, name).at(span);
                },
            });
            if next.is_none() {
                break;
            }
        }

        Ok(expr)
    }

    ///     primary := NUMBER | STRING | IDENTIFIER | funDecl |
    ///                "true" | "false" | "nil" | "this" |
    ///                "(" expression ")" | "super" . IDENTIFIER ;
    fn primary(&mut self) -> Result<ExprNode<'env>> {
        fn expected() -> TokenSet {
            TokenSet::from_iter([
                LeftParen, String, Number, This, Super, Identifier, Fun, False, Nil, True,
            ])
        }

        let (node, span) = match self.tokens.next() {
            Some((LeftParen, span)) => {
                let inner = self.expression()?;
                let inner = inner.alloc(self.arena);
                let end_span = self.expect(RightParen, EndOfInput::Unclosed(LeftParen, span))?;
                (Expr::group(inner), Span::from(span.union(end_span)))
            }
            Some((String, span)) => {
                let string = self.source.slice(span);
                (Expr::string(string), span)
            }
            Some((Number, span)) => {
                let range = Range::from(span);
                let num = self.source.source.get(range).ok_or_else(|| {
                    CroxError::new(CroxErrorKind::InvalidNumberLiteral { reason: None }, span)
                })?;
                let num = num.parse::<f64>().map_err(|err| {
                    CroxError::new(
                        CroxErrorKind::InvalidNumberLiteral { reason: Some(err) },
                        span,
                    )
                })?;

                (Expr::number(num), span)
            }
            Some((This, span)) => (Expr::this(self.arena), span),
            Some((Super, span)) => {
                let dot = self.expect(Dot, EndOfInput::expected(Dot, span))?;
                let method = self
                    .ident(dot)
                    .map_err(|c| c.with_payload(ExpectedFn(FunctionKind::Superclass)))?;

                let span = span.union(method.span);
                (Expr::super_(method, self.arena), Span::from(span))
            }
            Some((Identifier, span)) => {
                let ident = self.source.slice(span);
                (Expr::var(ident, self.arena), span)
            }
            Some((Fun, span)) => {
                let fun = self.function_def(span)?;
                (Expr::fun(fun.item), fun.span)
            }
            Some((False, span)) => (Expr::fals(), span),
            Some((Nil, span)) => (Expr::nil(), span),
            Some((True, span)) => (Expr::tru(), span),
            Some((typ, span)) => return Err(CroxErrorKind::of((typ, expected())).at(span)),
            None => {
                let kind = CroxErrorKind::of(expected());
                let end = self.source.source.len();
                return Err(CroxError::new(kind, end..end));
            }
        };

        Ok(node.at(span))
    }

    ///   arguments := expression ( "," expression )* ;
    fn arguments(&mut self, start: Span) -> Result<(Vec<ExprNode<'env>>, Span)> {
        let args = self.parens_list::<_, Arguments>(start, false, |this, _| this.expression())?;

        Ok((args.item, args.span))
    }

    fn expect(&mut self, expected: impl Into<TokenSet>, on_eoi: EndOfInput) -> Result<Span> {
        let expected = expected.into();
        match self.tokens.next() {
            Some((typ, span)) if expected.contains(typ) => Ok(span),
            Some((typ, span)) => Err(CroxError::new(CroxErrorKind::of((typ, expected)), span)),
            None => Err(CroxError::from(on_eoi)),
        }
    }

    fn ident(&mut self, span: Span) -> Result<Ident<'env>> {
        let span = self.expect(Identifier, EndOfInput::expected(Identifier, span))?;
        let identifier = self.source.slice(span);
        Ok(identifier.at(span))
    }

    fn parens_list<A, K: IntoTooMany>(
        &mut self,
        start: Span,
        parse_left_paren: bool,
        mut item: impl FnMut(&mut Self, Span) -> Result<Node<A>>,
    ) -> Result<Node<Vec<Node<A>>>> {
        let left_paren = if parse_left_paren {
            self.expect(LeftParen, EndOfInput::expected(LeftParen, start))?
        } else {
            start
        };

        let mut args = ArgsFor::<K>::create();

        // not peek! because we don't want to consume the token
        match self.tokens.peek() {
            Some(&(RightParen, _)) => {}
            _ => {
                let mut span = left_paren;
                loop {
                    args.push(item(self, span)?);
                    match peek!(self, { (Comma, span) => span }) {
                        Some(comma) => span = comma,
                        None => break,
                    }
                }
            }
        };

        let right_paren = self.expect(RightParen, EndOfInput::Unclosed(LeftParen, left_paren))?;
        let args = args.finish()?;

        Ok(args.at(right_paren))
    }
}

impl<R, T: Iterator<Item = Tok>> Parser<'_, R, T> {
    fn synchronize(&mut self) {
        // not peek! because we don't want to consume the token
        while let Some(&(tok, _)) = self.tokens.peek() {
            match tok {
                Class | Fun | For | If | Print | Return | Var | While => break,
                otherwise => {
                    let _ = self.tokens.next();
                    if otherwise == Semicolon {
                        break;
                    }
                }
            }
        }
    }
}

impl<'env, T: Iterator<Item = Tok>, R: ParserRule> Iterator for Parser<'env, R, T> {
    type Item = Result<R::Parsed<'env>>;

    fn next(&mut self) -> Option<Self::Item> {
        // check if we are at EOF since the previous iteration
        // could have reported an 'unexpected EOI'
        let _ = self.tokens.peek()?;
        Some(R::rule(self))
    }
}

pub trait ParserRule: Sized {
    type Parsed<'env>;

    fn rule<'env, T>(parser: &mut Parser<'env, Self, T>) -> Result<Self::Parsed<'env>>
    where
        T: Iterator<Item = Tok>;
}

impl ParserRule for ExpressionRule {
    type Parsed<'env> = ExprNode<'env>;

    fn rule<'env, T>(parser: &mut Parser<'env, Self, T>) -> Result<Self::Parsed<'env>>
    where
        T: Iterator<Item = Tok>,
    {
        parser.expression()
    }
}

impl ParserRule for StatementRule {
    type Parsed<'env> = StmtNode<'env>;

    fn rule<'env, T>(parser: &mut Parser<'env, Self, T>) -> Result<Self::Parsed<'env>>
    where
        T: Iterator<Item = Tok>,
    {
        parser.sync_declaration()
    }
}

pub struct UnpackToken<T> {
    inner: T,
}

impl<T: Iterator<Item = Token>> Iterator for UnpackToken<T> {
    type Item = Tok;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|tok| (tok.typ, tok.span))
    }
}

enum EndOfInput {
    Unclosed(TokenType, Span),
    Expected(TokenSet, Span),
}

impl EndOfInput {
    pub fn unclosed(open: TokenType, span: impl Into<Span>) -> Self {
        EndOfInput::Unclosed(open, span.into())
    }

    pub fn expected(expected: impl Into<TokenSet>, span: impl Into<Span>) -> Self {
        EndOfInput::Expected(expected.into(), span.into())
    }
}

impl From<EndOfInput> for CroxErrorKind {
    fn from(eoi: EndOfInput) -> Self {
        CroxError::from(eoi).kind
    }
}

impl From<EndOfInput> for CroxError {
    fn from(eoi: EndOfInput) -> Self {
        match eoi {
            EndOfInput::Unclosed(unclosed, span) => {
                CroxErrorKind::UnclosedDelimiter { unclosed }.at(span)
            }
            EndOfInput::Expected(typ, span) => CroxErrorKind::from(typ).at(span),
        }
    }
}

impl std::fmt::Display for FunctionKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Class => f.write_str("class"),
            Self::Superclass => f.write_str("superclass"),
            Self::Function => f.write_str("function"),
            Self::Method => f.write_str("method"),
            Self::ClassMethod => f.write_str("class method"),
            Self::Property => f.write_str("property"),
        }
    }
}

struct ExpectedFn(FunctionKind);

impl std::fmt::Display for ExpectedFn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Expected {} name", self.0)
    }
}

#[derive(Copy, Clone, Debug)]
struct ArgsFor<K> {
    _kind: PhantomData<K>,
}

impl<K> ArgsFor<K> {
    fn create<T>() -> Args<T, K, 255> {
        Args::new()
    }
}

#[derive(Clone, Debug)]
struct Args<T, K, const LIMIT: usize> {
    items: Result<Vec<Node<T>>>,
    _kind: PhantomData<K>,
}

impl<T, K> Args<T, K, 255> {
    fn new() -> Self {
        Self {
            items: Ok(Vec::new()),
            _kind: PhantomData,
        }
    }
}

impl<T, K, const LIMIT: usize> Args<T, K, LIMIT> {
    fn finish(self) -> Result<Vec<Node<T>>> {
        self.items
    }
}

impl<T, K: IntoTooMany, const LIMIT: usize> Args<T, K, LIMIT> {
    fn push(&mut self, item: Node<T>) {
        if let Ok(items) = self.items.as_mut() {
            if items.len() >= LIMIT {
                self.items = Err(CroxErrorKind::TooMany(K::into()).at(item.span));
            } else {
                items.push(item);
            }
        }
    }
}

enum Arguments {}
enum Parameters {}

trait IntoTooMany {
    fn into() -> TooMany;
}

impl IntoTooMany for Arguments {
    fn into() -> TooMany {
        TooMany::Arguments
    }
}

impl IntoTooMany for Parameters {
    fn into() -> TooMany {
        TooMany::Parameters
    }
}

#[cfg(test)]
mod tests {
    use crate::Spannable;

    use super::*;

    use pretty_assertions::assert_eq;

    fn parse<'env, T: ParserRule>(source: &'env str, arena: &'env Bump) -> Vec<T::Parsed<'env>> {
        let source = Source::new(source);
        let tokens = source.scan_all().unwrap();

        let parser = any_parser::<T, _>(source, tokens, arena);
        parser.collect::<Result<Vec<_>>>().unwrap()
    }

    #[test]
    fn test_parse1() {
        let arena = Bump::new();
        let actual = parse::<ExpressionRule>("6 / 3 - 1", &arena);

        let lhs = Expr::number(6.0).at(0..1).alloc(&arena);
        let rhs = Expr::number(3.0).at(4..5).alloc(&arena);
        let div = Expr::binary(lhs, BinaryOp::Div, rhs).at(0..5).alloc(&arena);

        let rhs = Expr::number(1.0).at(8..9).alloc(&arena);
        let sub = Expr::binary(div, BinaryOp::Sub, rhs).at(0..9);

        assert_eq!(actual, vec![sub]);
    }

    #[test]
    fn test_parse2() {
        let arena = Bump::new();
        let actual = parse::<ExpressionRule>("6 - 3 / 1", &arena);

        let first = Expr::number(6.0).at(0..1).alloc(&arena);

        let lhs = Expr::number(3.0).at(4..5).alloc(&arena);
        let rhs = Expr::number(1.0).at(8..9).alloc(&arena);
        let div = Expr::binary(lhs, BinaryOp::Div, rhs).at(4..9).alloc(&arena);

        let sub = Expr::binary(first, BinaryOp::Sub, div).at(0..9);

        assert_eq!(actual, vec![sub]);
    }

    #[test]
    fn test_parse_stmt1() {
        let arena = Bump::new();
        let actual = parse::<StatementRule>("print 1;", &arena);

        let expected = Stmt::print(Expr::number(1.0).at(6..7).alloc(&arena)).at(0..8);
        assert_eq!(actual, vec![expected]);
    }

    #[test]
    fn test_parse_stmt2() {
        let arena = Bump::new();
        let actual = parse::<StatementRule>("print 1 + 3 + 3 + 7;", &arena);

        let one = Expr::number(1.0).at(6..7).alloc(&arena);
        let three = Expr::number(3.0).at(10..11).alloc(&arena);
        let sum = Expr::add(one, three).at(6..11).alloc(&arena);

        let three = Expr::number(3.0).at(14..15).alloc(&arena);
        let sum = Expr::add(sum, three).at(6..15).alloc(&arena);

        let seven = Expr::number(7.0).at(18..19).alloc(&arena);
        let sum = Expr::add(sum, seven).at(6..19).alloc(&arena);

        let expected = Stmt::print(sum).at(0..20);
        assert_eq!(actual, vec![expected]);
    }

    #[test]
    fn test_parse_block() {
        let arena = Bump::new();
        let actual = parse::<StatementRule>("{ print 1; print 2; }", &arena);

        let one = Expr::number(1.0).at(8..9).alloc(&arena);
        let two = Expr::number(2.0).at(17..18).alloc(&arena);

        let first = Stmt::print(one).at(2..10);
        let second = Stmt::print(two).at(11..19);

        let block = [first, second];
        let expected = Stmt::block(&block).at(0..21);
        assert_eq!(actual, vec![expected]);
    }

    #[test]
    fn test_parse_eq() {
        let arena = Bump::new();
        let actual = parse::<ExpressionRule>("1 == 2", &arena);

        let one = Expr::number(1.0).at(0..1).alloc(&arena);
        let two = Expr::number(2.0).at(5..6).alloc(&arena);

        let expected = Expr::equals(one, two).at(0..6);
        assert_eq!(actual, vec![expected]);
    }

    #[test]
    fn test_parse_not_eq() {
        let arena = Bump::new();
        let actual = parse::<ExpressionRule>("1 != 2", &arena);

        let one = Expr::number(1.0).at(0..1).alloc(&arena);
        let two = Expr::number(2.0).at(5..6).alloc(&arena);

        let expected = Expr::not_equals(one, two).at(0..6);
        assert_eq!(actual, vec![expected]);
    }

    #[test]
    fn test_for_desugar() {
        let arena = Bump::new();
        let actual = parse::<StatementRule>("for (var i = 0; i < 10; i = i + 1) print i;", &arena);

        // constants
        let zero = Expr::number(0.0).at(13..14).alloc(&arena);
        let ten = Expr::number(10.0).at(20..22).alloc(&arena);
        let one = Expr::number(1.0).at(32..33).alloc(&arena);

        // initializer
        let init = Stmt::var("i".at(9..10), Some(zero)).at(5..15);

        // condition
        let i = Expr::var("i", &arena).at(16..17).alloc(&arena);
        let cond = Expr::less_than(i, ten).at(16..22).alloc(&arena);

        // increment
        let i = Expr::var("i", &arena).at(28..29).alloc(&arena);
        let add = Expr::add(i, one).at(28..33).alloc(&arena);
        let incr = Expr::assign("i", add, &arena).at(24..33).alloc(&arena);

        // body
        let i = Expr::var("i", &arena).at(41..42).alloc(&arena);
        let body = Stmt::print(i).at(35..43);
        let block = [body];
        let body = Stmt::block(&block).at(35..43);

        // desugar body
        let block = [body, Stmt::expression(incr).at(24..33)];
        let body = Stmt::block(&block).at(35..43).alloc(&arena);
        let body = Stmt::while_(cond, body).at(35..43);
        let block = [init, body];
        let body = Stmt::block(&block).at(0..43);

        assert_eq!(actual, &[body]);
    }

    #[test]
    fn test_for_desugar_block() {
        let arena = Bump::new();
        let actual = parse::<StatementRule>(
            "for (var i = 0; i < 10; i = i + 1) { print i; print i; }",
            &arena,
        );

        // constants
        let zero = Expr::number(0.0).at(13..14).alloc(&arena);
        let ten = Expr::number(10.0).at(20..22).alloc(&arena);
        let one = Expr::number(1.0).at(32..33).alloc(&arena);

        // initializer
        let init = Stmt::var("i".at(9..10), Some(zero)).at(5..15);

        // condition
        let i = Expr::var("i", &arena).at(16..17).alloc(&arena);
        let cond = Expr::less_than(i, ten).at(16..22).alloc(&arena);

        // increment
        let i = Expr::var("i", &arena).at(28..29).alloc(&arena);
        let add = Expr::add(i, one).at(28..33).alloc(&arena);
        let incr = Expr::assign("i", add, &arena).at(24..33).alloc(&arena);

        // body
        let i = Expr::var("i", &arena).at(43..44).alloc(&arena);
        let print1 = Stmt::print(i).at(37..45);
        let i = Expr::var("i", &arena).at(52..53).alloc(&arena);
        let print2 = Stmt::print(i).at(46..54);
        let block = [print1, print2];
        let body = Stmt::block(&block).at(35..56);

        // desugar body
        let block = [body, Stmt::expression(incr).at(24..33)];
        let body = Stmt::block(&block).at(35..56).alloc(&arena);
        let body = Stmt::while_(cond, body).at(35..56);
        let block = [init, body];
        let body = Stmt::block(&block).at(0..56);

        assert_eq!(actual, &[body]);
    }

    #[test]
    fn test_for_desugar_no_increment() {
        let arena = Bump::new();
        let actual = parse::<StatementRule>("for (var i = 0; i < 10; ) print i;", &arena);

        // constants
        let zero = Expr::number(0.0).at(13..14).alloc(&arena);
        let ten = Expr::number(10.0).at(20..22).alloc(&arena);

        // initializer
        let init = Stmt::var("i".at(9..10), Some(zero)).at(5..15);

        // condition
        let i = Expr::var("i", &arena).at(16..17).alloc(&arena);
        let cond = Expr::less_than(i, ten).at(16..22).alloc(&arena);

        // body
        let i = Expr::var("i", &arena).at(32..33).alloc(&arena);
        let body = Stmt::print(i).at(26..34).alloc(&arena);

        // desugar body
        let body = Stmt::while_(cond, body).at(26..34);
        let block = [init, body];
        let body = Stmt::block(&block).at(0..34);

        assert_eq!(actual, &[body]);
    }

    #[test]
    fn test_for_desugar_no_condition() {
        let arena = Bump::new();
        let actual = parse::<StatementRule>("for (var i = 0 ;; i = i + 1) print i;", &arena);

        // constants
        let zero = Expr::number(0.0).at(13..14).alloc(&arena);
        let one = Expr::number(1.0).at(26..27).alloc(&arena);

        // initializer
        let init = Stmt::var("i".at(9..10), Some(zero)).at(5..16);

        // increment
        let i = Expr::var("i", &arena).at(22..23).alloc(&arena);
        let add = Expr::add(i, one).at(22..27).alloc(&arena);
        let incr = Expr::assign("i", add, &arena).at(18..27).alloc(&arena);

        // body
        let i = Expr::var("i", &arena).at(35..36).alloc(&arena);
        let body = Stmt::print(i).at(29..37);
        let block = [body];
        let body = Stmt::block(&block).at(29..37);

        // desugar body
        let block = [body, Stmt::expression(incr).at(18..27)];
        let body = Stmt::block(&block).at(29..37).alloc(&arena);
        let body = Stmt::while_(Expr::tru().at(16..17).alloc(&arena), body).at(29..37);
        let block = [init, body];
        let body = Stmt::block(&block).at(0..37);

        assert_eq!(actual, &[body]);
    }

    #[test]
    fn test_for_desugar_no_initializer() {
        let arena = Bump::new();
        let actual = parse::<StatementRule>("for (; i < 10; i = i + 1) print i;", &arena);

        // constants
        let ten = Expr::number(10.0).at(11..13).alloc(&arena);
        let one = Expr::number(1.0).at(23..24).alloc(&arena);

        // condition
        let i = Expr::var("i", &arena).at(7..8).alloc(&arena);
        let cond = Expr::less_than(i, ten).at(7..13).alloc(&arena);

        // increment
        let i = Expr::var("i", &arena).at(19..20).alloc(&arena);
        let add = Expr::add(i, one).at(19..24).alloc(&arena);
        let incr = Expr::assign("i", add, &arena).at(15..24).alloc(&arena);

        // body
        let i = Expr::var("i", &arena).at(32..33).alloc(&arena);
        let body = Stmt::print(i).at(26..34);
        let block = [body];
        let body = Stmt::block(&block).at(26..34);

        // desugar body
        let block = [body, Stmt::expression(incr).at(15..24)];
        let body = Stmt::block(&block).at(26..34).alloc(&arena);
        let body = Stmt::while_(cond, body).at(0..34);

        assert_eq!(actual, &[body]);
    }

    #[test]
    fn test_for_desugar_block_shadow() {
        let arena = Bump::new();
        let actual = parse::<StatementRule>(
            "for (var i = 0; i < 10; i = i + 1) { print i; var i = -1; }",
            &arena,
        );

        // constants
        let zero = Expr::number(0.0).at(13..14).alloc(&arena);
        let ten = Expr::number(10.0).at(20..22).alloc(&arena);
        let one1 = Expr::number(1.0).at(32..33).alloc(&arena);
        let one2 = Expr::number(1.0).at(55..56).alloc(&arena);

        // initializer
        let init = Stmt::var("i".at(9..10), Some(zero)).at(5..15);

        // condition
        let i = Expr::var("i", &arena).at(16..17).alloc(&arena);
        let cond = Expr::less_than(i, ten).at(16..22).alloc(&arena);

        // increment
        let i = Expr::var("i", &arena).at(28..29).alloc(&arena);
        let add = Expr::add(i, one1).at(28..33).alloc(&arena);
        let incr = Expr::assign("i", add, &arena).at(24..33).alloc(&arena);

        // body
        let i = Expr::var("i", &arena).at(43..44).alloc(&arena);
        let print = Stmt::print(i).at(37..45);
        let assign = Stmt::var("i".at(50..51), Expr::neg(one2).at(54..56).alloc(&arena)).at(46..57);
        let block = [print, assign];
        let body = Stmt::block(&block).at(35..59);

        // desugar body
        let block = [body, Stmt::expression(incr).at(24..33)];
        let body = Stmt::block(&block).at(35..59).alloc(&arena);
        let body = Stmt::while_(cond, body).at(35..59);
        let block = [init, body];
        let body = Stmt::block(&block).at(0..59);

        assert_eq!(actual, &[body]);
    }

    #[test]
    fn test_invalid_var_target_synchronizes() {
        let arena = Bump::new();
        let source = Source::new("var nil = 42;");
        let tokens = source.scan_all().unwrap();

        let parser = any_parser::<StatementRule, _>(source, tokens, &arena);
        let actual = parser.collect::<Vec<_>>();

        assert_eq!(
            actual,
            &[Err(CroxErrorKind::from((
                TokenType::Nil,
                TokenType::Identifier
            ))
            .at(4..7))]
        );
    }
}
