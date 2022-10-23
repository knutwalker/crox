use std::iter::Peekable;

use crate::{BinaryOp, Expr, Node, Span, Token, TokenType, UnaryOp};

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
    use TokenType::*;

    /// expression := equality ;
    fn expression(tokens: &mut Peekable<impl Iterator<Item = Tok>>) -> Exp {
        equality(tokens)
    }

    ///    equlity := comparison ( ( "==" | "!=" ) comparison )* ;
    fn equality(tokens: &mut Peekable<impl Iterator<Item = Tok>>) -> Exp {
        let mut lhs = comparison(tokens)?;

        loop {
            let op = match tokens.peek() {
                Some((EqualEqual, _)) => BinaryOp::Equals,
                Some((BangEqual, _)) => BinaryOp::NotEquals,
                _ => return Ok(lhs),
            };
            tokens.next();
            let rhs = comparison(tokens)?;
            let span = lhs.span.union(rhs.span);
            lhs = Node::binary(lhs, op, rhs).into_expr(span);
        }
    }

    /// comparison := term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
    fn comparison(tokens: &mut Peekable<impl Iterator<Item = Tok>>) -> Exp {
        let mut lhs = term(tokens)?;

        loop {
            let op = match tokens.peek() {
                Some((Greater, _)) => BinaryOp::GreaterThan,
                Some((GreaterEqual, _)) => BinaryOp::GreaterThanOrEqual,
                Some((Less, _)) => BinaryOp::LessThan,
                Some((LessEqual, _)) => BinaryOp::LessThanOrEqual,
                _ => return Ok(lhs),
            };
            tokens.next();
            let rhs = term(tokens)?;
            let span = lhs.span.union(rhs.span);
            lhs = Node::binary(lhs, op, rhs).into_expr(span);
        }
    }

    ///       term := factor ( ( "+" | "-" ) factor )* ;
    fn term(tokens: &mut Peekable<impl Iterator<Item = Tok>>) -> Exp {
        let mut lhs = factor(tokens)?;

        loop {
            let op = match tokens.peek() {
                Some((Plus, _)) => BinaryOp::Add,
                Some((Minus, _)) => BinaryOp::Sub,
                _ => return Ok(lhs),
            };
            tokens.next();
            let rhs = factor(tokens)?;
            let span = lhs.span.union(rhs.span);
            lhs = Node::binary(lhs, op, rhs).into_expr(span);
        }
    }

    ///     factor := unary ( ( "*" | "/" ) unary )* ;
    fn factor(tokens: &mut Peekable<impl Iterator<Item = Tok>>) -> Exp {
        let mut lhs = unary(tokens)?;

        loop {
            let op = match tokens.peek() {
                Some((Star, _)) => BinaryOp::Mul,
                Some((Slash, _)) => BinaryOp::Div,
                _ => return Ok(lhs),
            };
            tokens.next();
            let rhs = unary(tokens)?;
            let span = lhs.span.union(rhs.span);
            lhs = Node::binary(lhs, op, rhs).into_expr(span);
        }
    }

    ///      unary := ( "!" | "-" ) unary | primary ;
    fn unary(tokens: &mut Peekable<impl Iterator<Item = Tok>>) -> Exp {
        let (op, span) = match tokens.peek() {
            Some((Bang, span)) => (UnaryOp::Not, *span),
            Some((Minus, span)) => (UnaryOp::Neg, *span),
            _ => return primary(tokens),
        };
        tokens.next();
        let inner = unary(tokens)?;
        let span = span.union(inner.span);
        Ok(Node::unary(op, inner).into_expr(span))
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
            Some((String, span)) => Node::string().into_expr(span),
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
