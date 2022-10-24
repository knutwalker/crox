use crate::{BinaryOp, Expr, Node, Span, Token, TokenType, UnaryOp};
use std::iter::Peekable;

type Tok = (TokenType, Span);
type Exp = Result<Expr, (String, Span)>;

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
pub fn parser(tokens: impl Iterator<Item = Token>) -> Exp {
    use TokenType::{String as TString, *};

    /// expression := equality ;
    fn expression(tokens: &mut Peekable<impl Iterator<Item = Tok>>) -> Exp {
        equality(tokens)
    }

    macro_rules! try_match {
        ($tokens:ident, { $($pat:pat => $expr:expr),+ $(,)? }) => {{
            let op = match $tokens.peek() {
                $(Some(&$pat) => $expr),+,
                _ => break,
            };
            let _ = $tokens.next();
            op
        }};
    }

    macro_rules! rule {
        ($tokens:ident, $descent:ident, { $($pat:pat => $expr:expr),+ $(,)? }) => {{
            let mut lhs = $descent($tokens)?;
            loop {
                let op = try_match!($tokens, { $($pat => $expr),+ });
                let rhs = $descent($tokens)?;
                let span = lhs.span.union(rhs.span);
                lhs = Node::binary(lhs, op, rhs).into_expr(span);
            }
            Ok(lhs)
        }};
    }

    ///    equlity := comparison ( ( "==" | "!=" ) comparison )* ;
    fn equality(tokens: &mut Peekable<impl Iterator<Item = Tok>>) -> Exp {
        rule!(tokens, comparison, {
            (BangEqual, _) => BinaryOp::Equals,
            (EqualEqual, _) => BinaryOp::NotEquals,
        })
    }

    /// comparison := term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
    fn comparison(tokens: &mut Peekable<impl Iterator<Item = Tok>>) -> Exp {
        rule!(tokens, term, {
            (Greater, _) => BinaryOp::GreaterThan,
            (GreaterEqual, _) => BinaryOp::GreaterThanOrEqual,
            (Less, _) => BinaryOp::LessThan,
            (LessEqual, _) => BinaryOp::LessThanOrEqual,
        })
    }

    ///       term := factor ( ( "+" | "-" ) factor )* ;
    fn term(tokens: &mut Peekable<impl Iterator<Item = Tok>>) -> Exp {
        rule!(tokens, factor, {
            (Plus, _) => BinaryOp::Add,
            (Minus, _) => BinaryOp::Sub,
        })
    }

    ///     factor := unary ( ( "*" | "/" ) unary )* ;
    fn factor(tokens: &mut Peekable<impl Iterator<Item = Tok>>) -> Exp {
        rule!(tokens, unary, {
            (Star, _) => BinaryOp::Mul,
            (Slash, _) => BinaryOp::Div,
        })
    }

    ///      unary := ( "!" | "-" ) unary | primary ;
    fn unary(tokens: &mut Peekable<impl Iterator<Item = Tok>>) -> Exp {
        loop {
            let (op, span) = try_match!(tokens, {
                (Bang, span) => (UnaryOp::Not, span),
                (Minus, span) => (UnaryOp::Neg, span),
            });

            let inner = unary(tokens)?;
            let span = span.union(inner.span);
            return Ok(Node::unary(op, inner).into_expr(span));
        }

        primary(tokens)
    }

    ///    primary := NUMBER | STRING | "true" | "false" | "(" expression ")" ;
    fn primary(tokens: &mut Peekable<impl Iterator<Item = Tok>>) -> Exp {
        Ok(match tokens.next() {
            Some((LeftParen, span)) => {
                let inner = expression(tokens)?;
                match tokens.next() {
                    Some((RightParen, end_span)) => {
                        Node::group(inner).into_expr(span.union(end_span))
                    }
                    Some((typ, span)) => {
                        return Err((format!("Unexpected token, expected ): {:?}", typ), span))
                    }
                    None => return Err(("Unclosed delimiter: (".into(), span)),
                }
            }
            Some((TString, span)) => Node::string().into_expr(span),
            Some((Number, span)) => Node::number().into_expr(span),
            Some((False, span)) => Node::fals().into_expr(span),
            Some((Nil, span)) => Node::nil().into_expr(span),
            Some((True, span)) => Node::tru().into_expr(span),
            Some((typ, span)) => {
                return Err((
                    format!("Unexpected token, expected primary: {:?}", typ),
                    span,
                ))
            }
            None => return Err(("Unexpected EOF".into(), Span::from(0..0))),
        })
    }

    let mut tokens = tokens.map(|t| (t.typ, t.span)).peekable();
    expression(&mut tokens)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse() {
        use pretty_assertions::assert_eq;

        // 6 / 3 - 1
        let tokens = [
            Token::new(TokenType::Number, 0, 1),
            Token::new(TokenType::Slash, 2, 1),
            Token::new(TokenType::Number, 4, 1),
            Token::new(TokenType::Minus, 6, 1),
            Token::new(TokenType::Number, 8, 1),
        ];

        let actual = parser(tokens.into_iter()).unwrap();
        let expected = Node::binary(
            Node::binary(
                Node::number().into_expr(0..1),
                BinaryOp::Div,
                Node::number().into_expr(4..5),
            )
            .into_expr(0..5),
            BinaryOp::Sub,
            Node::number().into_expr(8..9),
        )
        .into_expr(0..9);

        assert_eq!(actual, expected);
    }
}
