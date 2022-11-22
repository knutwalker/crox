use crate::{
    BinaryOp, CroxError, CroxErrorKind, Expr, ExprNode, Range, Result, Source, Span, Token,
    TokenSet, TokenType, UnaryOp,
};
use std::iter::Peekable;
use TokenType::*;

type Tok = (TokenType, Span);

/// Book-flavored BNF-ish:
///
/// ```bnf
/// expression := equality ;
///    equlity := comparison ( ( "==" | "!=" ) comparison )* ;
/// comparison := term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
///       term := factor ( ( "+" | "-" ) factor )* ;
///     factor := unary ( ( "*" | "/" ) unary )* ;
///      unary := ( "!" | "-" ) unary | primary ;
///    primary := NUMBER | STRING | "true" | "false" | "nil" | "(" expression ")" ;
/// ```
pub fn parse(
    source: Source<'_>,
    tokens: impl IntoIterator<Item = Token>,
) -> Result<Vec<ExprNode<'_>>> {
    parser(source, tokens).collect::<Result<Vec<_>, _>>()
}

/// Book-flavored BNF-ish:
///
/// ```bnf
/// expression := equality ;
///    equlity := comparison ( ( "==" | "!=" ) comparison )* ;
/// comparison := term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
///       term := factor ( ( "+" | "-" ) factor )* ;
///     factor := unary ( ( "*" | "/" ) unary )* ;
///      unary := ( "!" | "-" ) unary | primary ;
///    primary := NUMBER | STRING | "true" | "false" | "nil" | "(" expression ")" ;
/// ```
pub fn parser<I>(source: Source<'_>, tokens: I) -> Parser<UnpackToken<I::IntoIter>>
where
    I: IntoIterator<Item = Token>,
{
    let tokens = UnpackToken {
        inner: tokens.into_iter(),
    }
    .peekable();
    Parser::new(source, tokens)
}

/// Book-flavored BNF-ish:
///
/// ```bnf
/// expression := equality ;
///    equlity := comparison ( ( "==" | "!=" ) comparison )* ;
/// comparison := term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
///       term := factor ( ( "+" | "-" ) factor )* ;
///     factor := unary ( ( "*" | "/" ) unary )* ;
///      unary := ( "!" | "-" ) unary | primary ;
///    primary := NUMBER | STRING | "true" | "false" | "nil" | "(" expression ")" ;
/// ```
pub struct Parser<'a, T: Iterator<Item = Tok>> {
    source: Source<'a>,
    tokens: Peekable<T>,
}

macro_rules! rule {
    ($this:ident, $descent:ident, { $($pat:pat => $expr:expr),+ $(,)? }) => {{
        let mut lhs = $this.$descent()?;
        loop {
            let op = match $this.tokens.peek() {
                $(Some(&$pat) => $expr),+,
                _ => break,
            };
            let _ = $this.tokens.next();
            let rhs = $this.$descent()?;
            let span = lhs.span.union(rhs.span);
            lhs = Self::mk_node(Expr::binary(lhs, op, rhs), span);
        }
        Ok(lhs)
    }};
}

impl<'a, T: Iterator<Item = Tok>> Parser<'a, T> {
    fn new(source: Source<'a>, tokens: Peekable<T>) -> Self {
        Self { source, tokens }
    }
}

impl<'a, T: Iterator<Item = Tok>> Parser<'a, T> {
    /// expression := equality ;
    fn expression(&mut self) -> Result<ExprNode<'a>> {
        self.equality()
    }

    ///    equlity := comparison ( ( "==" | "!=" ) comparison )* ;
    fn equality(&mut self) -> Result<ExprNode<'a>> {
        rule!(self, comparison, {
            (BangEqual, _) => BinaryOp::Equals,
            (EqualEqual, _) => BinaryOp::NotEquals,
        })
    }

    /// comparison := term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
    fn comparison(&mut self) -> Result<ExprNode<'a>> {
        rule!(self, term, {
            (Greater, _) => BinaryOp::GreaterThan,
            (GreaterEqual, _) => BinaryOp::GreaterThanOrEqual,
            (Less, _) => BinaryOp::LessThan,
            (LessEqual, _) => BinaryOp::LessThanOrEqual,
        })
    }

    ///       term := factor ( ( "+" | "-" ) factor )* ;
    fn term(&mut self) -> Result<ExprNode<'a>> {
        rule!(self, factor, {
            (Plus, _) => BinaryOp::Add,
            (Minus, _) => BinaryOp::Sub,
        })
    }

    ///     factor := unary ( ( "*" | "/" ) unary )* ;
    fn factor(&mut self) -> Result<ExprNode<'a>> {
        rule!(self, unary, {
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
                match self.tokens.next() {
                    Some((RightParen, end_span)) => {
                        (Expr::group(inner), Span::from(span.union(end_span)))
                    }
                    Some((typ, span)) => {
                        let kind = CroxErrorKind::of((typ, RightParen));
                        return Err(CroxError::new(kind, span));
                    }
                    None => {
                        let kind = CroxErrorKind::UnclosedDelimiter {
                            unclosed: LeftParen,
                        };
                        return Err(CroxError::new(kind, span));
                    }
                }
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

    fn mk_node(expr: Expr<'a>, span: impl Into<Span>) -> ExprNode<'a> {
        expr.node(span)
    }
}

impl<T: Iterator<Item = Tok>> Parser<'_, T> {
    fn _synchronize(&mut self) {
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

impl<'a, T: Iterator<Item = Tok>> Iterator for Parser<'a, T> {
    type Item = Result<ExprNode<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        // check if we are at EOF since the previous iteration
        // could have reported an 'unexpected EOI'
        let _ = self.tokens.peek()?;
        Some(self.expression())
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse1() {
        use pretty_assertions::assert_eq;

        let source = Source::new("6 / 3 - 1");

        let tokens = [
            Token::new(TokenType::Number, 0, 1),
            Token::new(TokenType::Slash, 2, 1),
            Token::new(TokenType::Number, 4, 1),
            Token::new(TokenType::Minus, 6, 1),
            Token::new(TokenType::Number, 8, 1),
        ];

        let actual = parse(source, tokens).unwrap();

        let lhs = Expr::number(6.0).node(0..1);
        let rhs = Expr::number(3.0).node(4..5);
        let div = Expr::binary(lhs, BinaryOp::Div, rhs).node(0..5);

        let rhs = Expr::number(1.0).node(8..9);
        let sub = Expr::binary(div, BinaryOp::Sub, rhs).node(0..9);

        assert_eq!(actual, vec![sub]);
    }

    #[test]
    fn test_parse2() {
        use pretty_assertions::assert_eq;

        let source = Source::new("6 - 3 / 1");

        let tokens = [
            Token::new(TokenType::Number, 0, 1),
            Token::new(TokenType::Minus, 2, 1),
            Token::new(TokenType::Number, 4, 1),
            Token::new(TokenType::Slash, 6, 1),
            Token::new(TokenType::Number, 8, 1),
        ];

        let actual = parse(source, tokens).unwrap();

        let first = Expr::number(6.0).node(0..1);

        let lhs = Expr::number(3.0).node(4..5);
        let rhs = Expr::number(1.0).node(8..9);
        let div = Expr::binary(lhs, BinaryOp::Div, rhs).node(4..9);

        let sub = Expr::binary(first, BinaryOp::Sub, div).node(0..9);

        assert_eq!(actual, vec![sub]);
    }
}
