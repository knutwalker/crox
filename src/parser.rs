//! Book-flavored BNF-ish:
//!
//! ```bnf
//!     program := declaration* EOF ;
//! declaration := varDecl | statement ;
//!   statement := exprStmt | ifStmt | printStmt | block;
//!
//!     varDecl := "var" IDENTIFIER ( "=" expression )? ";" ;
//!    exprStmt := expression ";" ;
//!      ifStmt := "if" "(" expression ")" statement ( "else" statement )? ;
//!   printStmt := "print" expression ";" ;
//!       block := "{" declaration* "}" ;
//!
//!  expression := assignment ;
//!  assignment := IDENTIFIER "=" assignment | eqaulity ;
//!    eqaulity := comparison ( ( "==" | "!=" ) comparison )* ;
//!  comparison := term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
//!        term := factor ( ( "+" | "-" ) factor )* ;
//!      factor := unary ( ( "*" | "/" ) unary )* ;
//!       unary := ( "!" | "-" ) unary | primary ;
//!     primary := NUMBER | STRING | IDENTIFIER | "true" | "false" | "nil" | "(" expression ")" ;
//!```
use crate::{
    BinaryOp, CroxError, CroxErrorKind, Expr, ExprNode, ExpressionRule, Node, Range, Result,
    Source, Span, StatementRule, Stmt, StmtNode, Token, TokenSet, TokenType, UnaryOp,
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
            lhs = Expr::binary(lhs, op, rhs).at(span);
        }
        Ok(lhs)
    }};
}

impl<'a, R, T: Iterator<Item = Tok>> Parser<'a, R, T> {
    fn new(source: Source<'a>, tokens: Peekable<T>) -> Self {
        Self {
            source,
            tokens,
            _rule: PhantomData,
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

        Ok(Stmt::var(name, init).at(span.union(end_span)))
    }

    ///   statement := exprStmt | ifStmt | printStmt | block;
    fn statement(&mut self) -> Result<StmtNode<'a>> {
        let stmt = peek!(self, {
            (If, span) => self.if_statement(span),
            (Print, span) => self.print_statement(span),
            (LeftBrace, span) => self.block(span).map(|n| n.map(Stmt::block)),
        });
        match stmt {
            Some(Ok(stmt)) => Ok(stmt),
            Some(Err(err)) => Err(err),
            None => self.expr_statement(),
        }
    }

    ///      ifStmt := "if" "(" expression ")" statement ( "else" statement )? ;
    fn if_statement(&mut self, span: Span) -> Result<StmtNode<'a>> {
        self.expect(LeftParen, EndOfInput::Expected(LeftParen, span))?;
        let cond = self.expression()?;
        self.expect(RightParen, EndOfInput::Unclosed(LeftParen, span))?;

        let then_ = self.statement()?;
        let stmt = match self.tokens.peek() {
            Some((Else, _)) => {
                let _ = self.tokens.next();
                let else_ = self.statement()?;
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
    fn print_statement(&mut self, print_span: Span) -> Result<StmtNode<'a>> {
        let expr = self.expression()?;
        let end_span = self.expect(Semicolon, EndOfInput::Unclosed(Print, print_span))?;
        let stmt = Stmt::print(expr);
        Ok(stmt.at(print_span.union(end_span)))
    }

    ///    exprStmt := expression ";" ;
    fn expr_statement(&mut self) -> Result<StmtNode<'a>> {
        let expr = self.expression()?;
        let end_span = self.expect(Semicolon, EndOfInput::Expected(Semicolon, expr.span))?;
        let span = expr.span.union(end_span);
        let stmt = Stmt::expression(expr);
        Ok(stmt.at(span))
    }

    ///       block := "{" declaration* "}" ;
    fn block(&mut self, start: Span) -> Result<Node<Vec<StmtNode<'a>>>> {
        let mut stmts = Vec::new();

        let end = loop {
            match self.tokens.peek() {
                Some(&(RightBrace, end)) => {
                    let _ = self.tokens.next();
                    break end;
                }
                Some(_) => {
                    stmts.push(self.declaration()?);
                }
                None => {
                    return Err(EndOfInput::Unclosed(LeftBrace, start).into());
                }
            }
        };

        Ok(Node::new(stmts, start.union(end)))
    }

    ///  expression := assignment ;
    fn expression(&mut self) -> Result<ExprNode<'a>> {
        self.assignment()
    }

    ///  assignment := IDENTIFIER "=" assignment | eqaulity ;
    fn assignment(&mut self) -> Result<ExprNode<'a>> {
        let expr = self.equality()?;

        if let Some((Equal, _)) = self.tokens.peek() {
            let _ = self.tokens.next();

            let value = self.assignment()?;
            let Expr::Var(name) = &*expr.item else {
                return Err(CroxErrorKind::InvalidAssignmentTarget.at(expr.span));
            };

            let span = expr.span.union(value.span);
            return Ok(Expr::assign(name, value).at(span));
        }

        Ok(expr)
    }

    ///    eqaulity := comparison ( ( "==" | "!=" ) comparison )* ;
    fn equality(&mut self) -> Result<ExprNode<'a>> {
        bin_op!(self, comparison, {
            (BangEqual, _) => BinaryOp::Equals,
            (EqualEqual, _) => BinaryOp::NotEquals,
        })
    }

    ///  comparison := term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
    fn comparison(&mut self) -> Result<ExprNode<'a>> {
        bin_op!(self, term, {
            (Greater, _) => BinaryOp::GreaterThan,
            (GreaterEqual, _) => BinaryOp::GreaterThanOrEqual,
            (Less, _) => BinaryOp::LessThan,
            (LessEqual, _) => BinaryOp::LessThanOrEqual,
        })
    }

    ///        term := factor ( ( "+" | "-" ) factor )* ;
    fn term(&mut self) -> Result<ExprNode<'a>> {
        bin_op!(self, factor, {
            (Plus, _) => BinaryOp::Add,
            (Minus, _) => BinaryOp::Sub,
        })
    }

    ///      factor := unary ( ( "*" | "/" ) unary )* ;
    fn factor(&mut self) -> Result<ExprNode<'a>> {
        bin_op!(self, unary, {
            (Star, _) => BinaryOp::Mul,
            (Slash, _) => BinaryOp::Div,
        })
    }

    ///       unary := ( "!" | "-" ) unary | primary ;
    fn unary(&mut self) -> Result<ExprNode<'a>> {
        let (op, span) = match self.tokens.peek() {
            Some(&(Bang, span)) => (UnaryOp::Not, span),
            Some(&(Minus, span)) => (UnaryOp::Neg, span),
            _ => return self.primary(),
        };
        let _ = self.tokens.next();
        let inner = self.unary()?;
        let span = span.union(inner.span);
        Ok(Expr::unary(op, inner).at(span))
    }

    ///     primary := NUMBER | STRING | IDENTIFIER | "true" | "false" | "nil" | "(" expression ")" ;
    fn primary(&mut self) -> Result<ExprNode<'a>> {
        fn expected() -> TokenSet {
            TokenSet::from_iter([LeftParen, String, Number, Identifier, False, Nil, True])
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
            Some((typ, span)) => return Err(CroxErrorKind::of((typ, expected())).at(span)),
            None => {
                let kind = CroxErrorKind::of(expected());
                let end = self.source.source.len();
                return Err(CroxError::new(kind, end..end));
            }
        };

        Ok(node.at(span))
    }

    fn expect(&mut self, expected: impl Into<TokenSet>, on_eoi: EndOfInput) -> Result<Span> {
        let expected = expected.into();
        match self.tokens.next() {
            Some((typ, span)) if expected.contains(typ) => Ok(span),
            Some((typ, span)) => Err(CroxError::new(CroxErrorKind::of((typ, expected)), span)),
            None => Err(CroxError::from(on_eoi)),
        }
    }
}

impl<R, T: Iterator<Item = Tok>> Parser<'_, R, T> {
    fn synchronize(&mut self) {
        while let Some((tok, _)) = self.tokens.peek() {
            match *tok {
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

impl<'a, T: Iterator<Item = Tok>, R: ParserRule> Iterator for Parser<'a, R, T> {
    type Item = Result<R::Parsed<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        // check if we are at EOF since the previous iteration
        // could have reported an 'unexpected EOI'
        let _ = self.tokens.peek()?;
        Some(R::rule(self))
    }
}

pub trait ParserRule: Sized {
    type Parsed<'a>;

    fn rule<'a, T>(parser: &mut Parser<'a, Self, T>) -> Result<Self::Parsed<'a>>
    where
        T: Iterator<Item = Tok>;
}

impl ParserRule for ExpressionRule {
    type Parsed<'a> = ExprNode<'a>;

    fn rule<'a, T>(parser: &mut Parser<'a, Self, T>) -> Result<Self::Parsed<'a>>
    where
        T: Iterator<Item = Tok>,
    {
        parser.expression()
    }
}

impl ParserRule for StatementRule {
    type Parsed<'a> = StmtNode<'a>;

    fn rule<'a, T>(parser: &mut Parser<'a, Self, T>) -> Result<Self::Parsed<'a>>
    where
        T: Iterator<Item = Tok>,
    {
        parser.declaration()
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
            EndOfInput::Expected(typ, span) => CroxErrorKind::from(TokenSet::from(typ)).at(span),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use pretty_assertions::assert_eq;

    fn parse<T: ParserRule>(source: &str) -> Vec<T::Parsed<'_>> {
        let source = Source::new(source);
        let tokens = source.scan_all().unwrap();

        let parser = any_parser::<T, _>(source, tokens);
        parser.collect::<Result<Vec<_>>>().unwrap()
    }

    #[test]
    fn test_parse1() {
        let actual = parse::<ExpressionRule>("6 / 3 - 1");

        let lhs = Expr::number(6.0).at(0..1);
        let rhs = Expr::number(3.0).at(4..5);
        let div = Expr::binary(lhs, BinaryOp::Div, rhs).at(0..5);

        let rhs = Expr::number(1.0).at(8..9);
        let sub = Expr::binary(div, BinaryOp::Sub, rhs).at(0..9);

        assert_eq!(actual, vec![sub]);
    }

    #[test]
    fn test_parse2() {
        let actual = parse::<ExpressionRule>("6 - 3 / 1");

        let first = Expr::number(6.0).at(0..1);

        let lhs = Expr::number(3.0).at(4..5);
        let rhs = Expr::number(1.0).at(8..9);
        let div = Expr::binary(lhs, BinaryOp::Div, rhs).at(4..9);

        let sub = Expr::binary(first, BinaryOp::Sub, div).at(0..9);

        assert_eq!(actual, vec![sub]);
    }

    #[test]
    fn test_parse_stmt1() {
        let actual = parse::<StatementRule>("print 1;");

        let expected = Stmt::print(Expr::number(1.0).at(6..7)).at(0..8);
        assert_eq!(actual, vec![expected]);
    }

    #[test]
    fn test_parse_stmt2() {
        let actual = parse::<StatementRule>("print 1 + 3 + 3 + 7;");

        let one = Expr::number(1.0).at(6..7);
        let three = Expr::number(3.0).at(10..11);
        let sum = Expr::add(one, three).at(6..11);

        let three = Expr::number(3.0).at(14..15);
        let sum = Expr::add(sum, three).at(6..15);

        let seven = Expr::number(7.0).at(18..19);
        let sum = Expr::add(sum, seven).at(6..19);

        let expected = Stmt::print(sum).at(0..20);
        assert_eq!(actual, vec![expected]);
    }

    #[test]
    fn test_parse_block() {
        let actual = parse::<StatementRule>("{ print 1; print 2; }");

        let one = Expr::number(1.0).at(8..9);
        let two = Expr::number(2.0).at(17..18);

        let first = Stmt::print(one).at(2..10);
        let second = Stmt::print(two).at(11..19);

        let expected = Stmt::block(vec![first, second]).at(0..21);
        assert_eq!(actual, vec![expected]);
    }
}
