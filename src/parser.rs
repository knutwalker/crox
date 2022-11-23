//! Book-flavored BNF-ish:
//!
//! ```bnf
//!     program := declaration* EOF ;
//! declaration := varDecl | statement ;
//!   statement := exprStmt | printStmt ;
//!
//!     varDecl := "var" IDENTIFIER ( "=" expression )? ";" ;
//!    exprStmt := expression ";" ;
//!   printStmt := "print" expression ";" ;
//!
//!  expression := equality ;
//!     equlity := comparison ( ( "==" | "!=" ) comparison )* ;
//!  comparison := term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
//!        term := factor ( ( "+" | "-" ) factor )* ;
//!      factor := unary ( ( "*" | "/" ) unary )* ;
//!       unary := ( "!" | "-" ) unary | primary ;
//!     primary := NUMBER | STRING | IDENTIFIER | "true" | "false" | "nil" | "(" expression ")" ;
//!```
use crate::{
    BinaryOp, CroxError, CroxErrorKind, Expr, ExprNode, Range, Result, Source, Span, Stmt,
    StmtNode, Token, TokenSet, TokenType, UnaryOp,
};
use std::{iter::Peekable, marker::PhantomData};
use TokenType::*;

type Tok = (TokenType, Span);

pub fn expr_parser<I>(
    source: Source<'_>,
    tokens: I,
) -> Parser<ExpressionRule, UnpackToken<I::IntoIter>>
where
    I: IntoIterator<Item = Token>,
{
    any_parser(source, tokens)
}

pub fn stmt_parser<I>(
    source: Source<'_>,
    tokens: I,
) -> Parser<StatementRule, UnpackToken<I::IntoIter>>
where
    I: IntoIterator<Item = Token>,
{
    any_parser(source, tokens)
}

fn any_parser<R, I>(source: Source<'_>, tokens: I) -> Parser<R, UnpackToken<I::IntoIter>>
where
    I: IntoIterator<Item = Token>,
{
    let tokens = UnpackToken {
        inner: tokens.into_iter(),
    }
    .peekable();
    Parser::new(source, tokens)
}

pub struct Parser<'a, R, T: Iterator<Item = Tok>> {
    source: Source<'a>,
    tokens: Peekable<T>,
    rule: PhantomData<R>,
}

pub enum ExpressionRule {}

pub enum StatementRule {}

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
            let span = lhs.span.union(rhs.span);
            lhs = Self::mk_node(Expr::binary(lhs, op, rhs), span);
        }
        Ok(lhs)
    }};
}

impl<'a, R, T: Iterator<Item = Tok>> Parser<'a, R, T> {
    fn new(source: Source<'a>, tokens: Peekable<T>) -> Self {
        Self {
            source,
            tokens,
            rule: PhantomData,
        }
    }
}

impl<'a, R, T: Iterator<Item = Tok>> Parser<'a, R, T> {
    /// declaration := varDecl | statement ;
    fn declaration(&mut self) -> Result<StmtNode<'a>> {
        let stmt = peek!(self, {
         (Var, span) => self.var_decl(span),
        })
        .transpose()?;

        match stmt {
            Some(stmt) => Ok(stmt),
            None => match self.statement() {
                Ok(stmt) => Ok(stmt),
                Err(e) => {
                    // are we really gonna ignore all errors?
                    self.synchronize();
                    Err(e)
                }
            },
        }
    }

    ///     varDecl := "var" IDENTIFIER ( "=" expression )? ";" ;
    fn var_decl(&mut self, span: Span) -> Result<StmtNode<'a>> {
        let name = self.expect(Identifier, EndOfInput::Expected(Identifier, span))?;
        let name = self.source.slice(name);

        let init = match self.tokens.peek() {
            Some((Equal, _)) => {
                let _ = self.tokens.next();
                let init = self.expression()?;
                Some(init)
            }
            _ => None,
        };

        let end_span = self.expect(Semicolon, EndOfInput::Unclosed(Identifier, span))?;

        Ok(Stmt::var(name, init).node(span.union(end_span)))
    }

    ///  statement := exprStmt | printStmt ;
    fn statement(&mut self) -> Result<StmtNode<'a>> {
        let stmt = peek!(self, {
            (Print, span) => self.print_statement(span),
        });
        match stmt {
            Some(Ok(stmt)) => Ok(stmt),
            Some(Err(err)) => Err(err),
            None => self.expr_statement(),
        }
    }

    fn print_statement(&mut self, print_span: Span) -> Result<StmtNode<'a>> {
        let expr = self.expression()?;
        let end_span = self.expect(Semicolon, EndOfInput::Unclosed(Print, print_span))?;
        let stmt = Stmt::print(expr);
        Ok(Self::mk_stmt(stmt, print_span.union(end_span)))
    }

    fn expr_statement(&mut self) -> Result<StmtNode<'a>> {
        let expr = self.expression()?;
        let end_span = self.expect(Semicolon, EndOfInput::Expected(Semicolon, expr.span))?;
        let span = expr.span.union(end_span);
        let stmt = Stmt::expression(expr);
        Ok(Self::mk_stmt(stmt, span))
    }

    /// expression := equality ;
    fn expression(&mut self) -> Result<ExprNode<'a>> {
        self.equality()
    }

    ///    equlity := comparison ( ( "==" | "!=" ) comparison )* ;
    fn equality(&mut self) -> Result<ExprNode<'a>> {
        bin_op!(self, comparison, {
            (BangEqual, _) => BinaryOp::Equals,
            (EqualEqual, _) => BinaryOp::NotEquals,
        })
    }

    /// comparison := term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
    fn comparison(&mut self) -> Result<ExprNode<'a>> {
        bin_op!(self, term, {
            (Greater, _) => BinaryOp::GreaterThan,
            (GreaterEqual, _) => BinaryOp::GreaterThanOrEqual,
            (Less, _) => BinaryOp::LessThan,
            (LessEqual, _) => BinaryOp::LessThanOrEqual,
        })
    }

    ///       term := factor ( ( "+" | "-" ) factor )* ;
    fn term(&mut self) -> Result<ExprNode<'a>> {
        bin_op!(self, factor, {
            (Plus, _) => BinaryOp::Add,
            (Minus, _) => BinaryOp::Sub,
        })
    }

    ///     factor := unary ( ( "*" | "/" ) unary )* ;
    fn factor(&mut self) -> Result<ExprNode<'a>> {
        bin_op!(self, unary, {
            (Star, _) => BinaryOp::Mul,
            (Slash, _) => BinaryOp::Div,
        })
    }

    ///      unary := ( "!" | "-" ) unary | primary ;
    fn unary(&mut self) -> Result<ExprNode<'a>> {
        let (op, span) = match self.tokens.peek() {
            Some(&(Bang, span)) => (UnaryOp::Not, span),
            Some(&(Minus, span)) => (UnaryOp::Neg, span),
            _ => return self.primary(),
        };
        let _ = self.tokens.next();
        let inner = self.unary()?;
        let span = span.union(inner.span);
        Ok(Self::mk_node(Expr::unary(op, inner), span))
    }

    ///    primary := NUMBER | STRING | "true" | "false" | "(" expression ")" ;
    fn primary(&mut self) -> Result<ExprNode<'a>> {
        fn expected() -> TokenSet {
            TokenSet::from_iter([LeftParen, String, Number, False, Nil, True])
        }

        let (node, span) = match self.tokens.next() {
            Some((LeftParen, span)) => {
                let inner = self.expression()?;
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
            Some((Identifier, span)) => {
                let ident = self.source.slice(span);
                (Expr::var(ident), span)
            }
            Some((False, span)) => (Expr::fals(), span),
            Some((Nil, span)) => (Expr::nil(), span),
            Some((True, span)) => (Expr::tru(), span),
            Some((typ, span)) => {
                let kind = CroxErrorKind::of((typ, expected()));
                return Err(CroxError::new(kind, span));
            }
            None => {
                let kind = CroxErrorKind::of(expected());
                let end = self.source.source.len();
                return Err(CroxError::new(kind, end..end));
            }
        };

        Ok(Self::mk_node(node, span))
    }

    fn expect(&mut self, expected: impl Into<TokenSet>, on_eoi: EndOfInput) -> Result<Span> {
        let expected = expected.into();
        match self.tokens.next() {
            Some((typ, span)) if expected.contains(typ) => Ok(span),
            Some((typ, span)) => Err(CroxError::new(CroxErrorKind::of((typ, expected)), span)),
            None => Err(match on_eoi {
                EndOfInput::Unclosed(unclosed, span) => {
                    CroxError::new(CroxErrorKind::UnclosedDelimiter { unclosed }, span)
                }
                EndOfInput::Expected(typ, span) => {
                    CroxError::new(CroxErrorKind::from(TokenSet::from(typ)), span)
                }
            }),
        }
    }

    fn mk_node(expr: Expr<'a>, span: impl Into<Span>) -> ExprNode<'a> {
        expr.node(span)
    }

    fn mk_stmt(stmt: Stmt<'a>, span: impl Into<Span>) -> StmtNode<'a> {
        stmt.node(span)
    }
}

impl<R, T: Iterator<Item = Tok>> Parser<'_, R, T> {
    fn synchronize(&mut self) {
        while let Some((tok, _)) = self.tokens.peek() {
            match *tok {
                Semicolon => {
                    let _ = self.tokens.next();
                    break;
                }
                Class | Fun | For | If | Print | Return | Var | While => break,
                _ => {}
            }
        }
    }
}

impl<'a, T: Iterator<Item = Tok>> Iterator for Parser<'a, ExpressionRule, T> {
    type Item = Result<ExprNode<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        // check if we are at EOF since the previous iteration
        // could have reported an 'unexpected EOI'
        let _ = self.tokens.peek()?;
        Some(self.expression())
    }
}

impl<'a, T: Iterator<Item = Tok>> Iterator for Parser<'a, StatementRule, T> {
    type Item = Result<StmtNode<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        // check if we are at EOF since the previous iteration
        // could have reported an 'unexpected EOI'
        let _ = self.tokens.peek()?;
        Some(self.declaration())
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
    Expected(TokenType, Span),
}

#[cfg(test)]
mod tests {
    use super::*;

    use pretty_assertions::assert_eq;

    #[test]
    fn test_parse1() {
        let source = Source::new("6 / 3 - 1");

        let tokens = [
            Token::new(TokenType::Number, 0, 1),
            Token::new(TokenType::Slash, 2, 1),
            Token::new(TokenType::Number, 4, 1),
            Token::new(TokenType::Minus, 6, 1),
            Token::new(TokenType::Number, 8, 1),
        ];

        let actual = expr_parser(source, tokens)
            .collect::<Result<Vec<_>>>()
            .unwrap();

        let lhs = Expr::number(6.0).node(0..1);
        let rhs = Expr::number(3.0).node(4..5);
        let div = Expr::binary(lhs, BinaryOp::Div, rhs).node(0..5);

        let rhs = Expr::number(1.0).node(8..9);
        let sub = Expr::binary(div, BinaryOp::Sub, rhs).node(0..9);

        assert_eq!(actual, vec![sub]);
    }

    #[test]
    fn test_parse2() {
        let source = Source::new("6 - 3 / 1");

        let tokens = [
            Token::new(TokenType::Number, 0, 1),
            Token::new(TokenType::Minus, 2, 1),
            Token::new(TokenType::Number, 4, 1),
            Token::new(TokenType::Slash, 6, 1),
            Token::new(TokenType::Number, 8, 1),
        ];

        let actual = expr_parser(source, tokens)
            .collect::<Result<Vec<_>>>()
            .unwrap();

        let first = Expr::number(6.0).node(0..1);

        let lhs = Expr::number(3.0).node(4..5);
        let rhs = Expr::number(1.0).node(8..9);
        let div = Expr::binary(lhs, BinaryOp::Div, rhs).node(4..9);

        let sub = Expr::binary(first, BinaryOp::Sub, div).node(0..9);

        assert_eq!(actual, vec![sub]);
    }

    #[test]
    fn test_parse_stmt1() -> Result<()> {
        let source = Source::new("print 1;");
        let tokens = source.into_iter().collect::<Result<Vec<_>>>()?;

        let stmts = stmt_parser(source, tokens).collect::<Result<Vec<_>>>()?;

        let expected = Stmt::print(Expr::number(1.0).node(6..7)).node(0..8);
        assert_eq!(stmts, vec![expected]);
        Ok(())
    }

    #[test]
    fn test_parse_stmt2() -> Result<()> {
        let source = Source::new("print 1 + 3 + 3 + 7;");
        let tokens = source.into_iter().collect::<Result<Vec<_>>>()?;

        let stmts = stmt_parser(source, tokens).collect::<Result<Vec<_>>>()?;

        let one = Expr::number(1.0).node(6..7);
        let three = Expr::number(3.0).node(10..11);
        let sum = Expr::add(one, three).node(6..11);

        let three = Expr::number(3.0).node(14..15);
        let sum = Expr::add(sum, three).node(6..15);

        let seven = Expr::number(7.0).node(18..19);
        let sum = Expr::add(sum, seven).node(6..19);

        let expected = Stmt::print(sum).node(0..20);
        assert_eq!(stmts, vec![expected]);
        Ok(())
    }
}
