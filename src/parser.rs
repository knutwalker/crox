use crate::{Ast, AstBuilder, BinaryOp, Expr, Node, Resolve, Span, Token, TokenType, UnaryOp};
use std::iter::Peekable;
use std::string::String;
use TokenType::{String as TString, *};

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
pub fn parse(tokens: impl IntoIterator<Item = Token>) -> Result<(Vec<Expr>, Ast), (String, Span)> {
    let mut parser = parser(tokens);
    let exprs = parser.by_ref().collect::<Result<Vec<_>, _>>()?;
    Ok((exprs, parser.into_ast()))
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
pub fn parser<I>(tokens: I) -> Parser<UnpackToken<I::IntoIter>>
where
    I: IntoIterator<Item = Token>,
{
    let tokens = UnpackToken {
        inner: tokens.into_iter(),
    }
    .peekable();
    Parser::new(tokens)
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
pub struct Parser<T: Iterator<Item = Tok>> {
    tokens: Peekable<T>,
    nodes: AstBuilder,
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
            lhs = $this.mk_expr(Node::binary(lhs, op, rhs), span);
        }
        Ok(lhs)
    }};
}

impl<T: Iterator<Item = Tok>> Parser<T> {
    fn new(tokens: Peekable<T>) -> Self {
        Self {
            tokens,
            nodes: AstBuilder::default(),
        }
    }

    pub fn into_ast(self) -> Ast {
        self.nodes.build()
    }
}

impl<T: Iterator<Item = Tok>> Resolve<Expr> for Parser<T> {
    type Output = Node;

    fn resolve(&self, context: &Expr) -> Self::Output {
        self.nodes.resolve(&context.idx)
    }
}

impl<T: Iterator<Item = Tok>> Parser<T> {
    /// expression := equality ;
    fn expression(&mut self) -> Exp {
        self.equality()
    }

    ///    equlity := comparison ( ( "==" | "!=" ) comparison )* ;
    fn equality(&mut self) -> Exp {
        rule!(self, comparison, {
            (BangEqual, _) => BinaryOp::Equals,
            (EqualEqual, _) => BinaryOp::NotEquals,
        })
    }

    /// comparison := term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
    fn comparison(&mut self) -> Exp {
        rule!(self, term, {
            (Greater, _) => BinaryOp::GreaterThan,
            (GreaterEqual, _) => BinaryOp::GreaterThanOrEqual,
            (Less, _) => BinaryOp::LessThan,
            (LessEqual, _) => BinaryOp::LessThanOrEqual,
        })
    }

    ///       term := factor ( ( "+" | "-" ) factor )* ;
    fn term(&mut self) -> Exp {
        rule!(self, factor, {
            (Plus, _) => BinaryOp::Add,
            (Minus, _) => BinaryOp::Sub,
        })
    }

    ///     factor := unary ( ( "*" | "/" ) unary )* ;
    fn factor(&mut self) -> Exp {
        rule!(self, unary, {
            (Star, _) => BinaryOp::Mul,
            (Slash, _) => BinaryOp::Div,
        })
    }

    ///      unary := ( "!" | "-" ) unary | primary ;
    fn unary(&mut self) -> Exp {
        let (op, span) = match self.tokens.peek() {
            Some(&(Bang, span)) => (UnaryOp::Not, span),
            Some(&(Minus, span)) => (UnaryOp::Neg, span),
            _ => return self.primary(),
        };
        let _ = self.tokens.next();
        let inner = self.unary()?;
        let span = span.union(inner.span);
        Ok(self.mk_expr(Node::unary(op, inner), span))
    }

    ///    primary := NUMBER | STRING | "true" | "false" | "(" expression ")" ;
    fn primary(&mut self) -> Exp {
        let (node, span) = match self.tokens.next() {
            Some((LeftParen, span)) => {
                let inner = self.expression()?;
                match self.tokens.next() {
                    Some((RightParen, end_span)) => {
                        (Node::group(inner), Span::from(span.union(end_span)))
                    }
                    Some((typ, span)) => {
                        return Err((format!("Unexpected token, expected ): {:?}", typ), span))
                    }
                    None => return Err(("Unclosed delimiter: (".into(), span)),
                }
            }
            Some((TString, span)) => (Node::string(), span),
            Some((Number, span)) => (Node::number(), span),
            Some((False, span)) => (Node::fals(), span),
            Some((Nil, span)) => (Node::nil(), span),
            Some((True, span)) => (Node::tru(), span),
            Some((typ, span)) => {
                return Err((
                    format!("Unexpected token, expected primary: {:?}", typ),
                    span,
                ))
            }
            None => return Err(("Unexpected EOF".into(), Span::from(0..0))),
        };

        Ok(self.mk_expr(node, span))
    }

    fn mk_expr(&mut self, node: Node, span: impl Into<Span>) -> Expr {
        let idx = self.nodes.add(node);
        Expr::new(idx, span.into())
    }
}

impl<T: Iterator<Item = Tok>> Iterator for Parser<T> {
    type Item = Exp;

    fn next(&mut self) -> Option<Self::Item> {
        match self.expression() {
            Ok(exp) => Some(Ok(exp)),
            Err((reason, _span)) if reason == "Unexpected EOF" => None,
            Err(e) => Some(Err(e)),
        }
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

        // 6 / 3 - 1
        let tokens = [
            Token::new(TokenType::Number, 0, 1),
            Token::new(TokenType::Slash, 2, 1),
            Token::new(TokenType::Number, 4, 1),
            Token::new(TokenType::Minus, 6, 1),
            Token::new(TokenType::Number, 8, 1),
        ];

        let (actual, ast) = parse(tokens).unwrap();

        let mut ast_builder = AstBuilder::default();
        let lhs = ast_builder.add(Node::number()).into_expr(0..1);
        let rhs = ast_builder.add(Node::number()).into_expr(4..5);
        let div = ast_builder
            .add(Node::binary(lhs, BinaryOp::Div, rhs))
            .into_expr(0..5);

        let rhs = ast_builder.add(Node::number()).into_expr(8..9);
        let sub = ast_builder
            .add(Node::binary(div, BinaryOp::Sub, rhs))
            .into_expr(0..9);

        let expected = ast_builder.build();

        assert_eq!(actual, vec![sub]);
        assert_eq!(ast, expected);
    }

    #[test]
    fn test_parse2() {
        use pretty_assertions::assert_eq;

        // 6 - 3 / 1
        let tokens = [
            Token::new(TokenType::Number, 0, 1),
            Token::new(TokenType::Minus, 2, 1),
            Token::new(TokenType::Number, 4, 1),
            Token::new(TokenType::Slash, 6, 1),
            Token::new(TokenType::Number, 8, 1),
        ];

        let (actual, ast) = parse(tokens).unwrap();

        let mut ast_builder = AstBuilder::default();

        let first = ast_builder.add(Node::number()).into_expr(0..1);

        let lhs = ast_builder.add(Node::number()).into_expr(4..5);
        let rhs = ast_builder.add(Node::number()).into_expr(8..9);
        let div = ast_builder
            .add(Node::binary(lhs, BinaryOp::Div, rhs))
            .into_expr(4..9);

        let sub = ast_builder
            .add(Node::binary(first, BinaryOp::Sub, div))
            .into_expr(0..9);

        let expected = ast_builder.build();

        assert_eq!(actual, vec![sub]);
        assert_eq!(ast, expected);
    }
}
