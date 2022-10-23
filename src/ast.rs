use crate::token::Span;
use std::fmt::{Debug, Display};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    pub node: Box<Node>,
    pub span: Span,
}

impl Expr {
    pub fn new(node: Box<Node>, span: Span) -> Self {
        Self { node, span }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Node<T: Sized = Expr> {
    Literal(Literal),
    Unary(UnaryOp, T),
    Binary(T, BinaryOp, T),
    Group(T),
}

impl<T: Sized> Node<T> {
    pub fn nil() -> Self {
        Self::Literal(Literal::Nil)
    }

    pub fn tru() -> Self {
        Self::Literal(Literal::True)
    }

    pub fn fals() -> Self {
        Self::Literal(Literal::False)
    }

    pub fn number() -> Self {
        Self::Literal(Literal::Number)
    }

    pub fn string() -> Self {
        Self::Literal(Literal::String)
    }

    pub fn neg(expr: T) -> Self {
        Self::Unary(UnaryOp::Neg, expr)
    }

    pub fn not(expr: T) -> Self {
        Self::Unary(UnaryOp::Not, expr)
    }

    pub fn unary(op: UnaryOp, expr: T) -> Self {
        Self::Unary(op, expr)
    }

    pub fn add(lhs: T, rhs: T) -> Self {
        Self::Binary(lhs, BinaryOp::Add, rhs)
    }

    pub fn sub(lhs: T, rhs: T) -> Self {
        Self::Binary(lhs, BinaryOp::Sub, rhs)
    }

    pub fn mul(lhs: T, rhs: T) -> Self {
        Self::Binary(lhs, BinaryOp::Mul, rhs)
    }

    pub fn div(lhs: T, rhs: T) -> Self {
        Self::Binary(lhs, BinaryOp::Div, rhs)
    }

    pub fn equals(lhs: T, rhs: T) -> Self {
        Self::Binary(lhs, BinaryOp::Equals, rhs)
    }

    pub fn not_equals(lhs: T, rhs: T) -> Self {
        Self::Binary(lhs, BinaryOp::NotEquals, rhs)
    }

    pub fn less_than(lhs: T, rhs: T) -> Self {
        Self::Binary(lhs, BinaryOp::LessThan, rhs)
    }

    pub fn less_than_or_equal(lhs: T, rhs: T) -> Self {
        Self::Binary(lhs, BinaryOp::LessThanOrEqual, rhs)
    }

    pub fn greater_than(lhs: T, rhs: T) -> Self {
        Self::Binary(lhs, BinaryOp::GreaterThan, rhs)
    }

    pub fn greater_than_or_equal(lhs: T, rhs: T) -> Self {
        Self::Binary(lhs, BinaryOp::GreaterThanOrEqual, rhs)
    }

    pub fn binary(lhs: T, op: BinaryOp, rhs: T) -> Self {
        Self::Binary(lhs, op, rhs)
    }

    pub fn group(expr: T) -> Self {
        Self::Group(expr)
    }

    pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> Node<U> {
        match self {
            Self::Literal(lit) => Node::Literal(lit),
            Self::Unary(op, expr) => Node::Unary(op, f(expr)),
            Self::Binary(lhs, op, rhs) => Node::Binary(f(lhs), op, f(rhs)),
            Self::Group(expr) => Node::Group(f(expr)),
        }
    }

    pub fn try_map<U, E>(self, mut f: impl FnMut(T) -> Result<U, E>) -> Result<Node<U>, E> {
        match self {
            Self::Literal(lit) => Ok(Node::Literal(lit)),
            Self::Unary(op, expr) => Ok(Node::Unary(op, f(expr)?)),
            Self::Binary(lhs, op, rhs) => Ok(Node::Binary(f(lhs)?, op, f(rhs)?)),
            Self::Group(expr) => Ok(Node::Group(f(expr)?)),
        }
    }
}

impl Node {
    pub fn into_expr(self, range: impl Into<Span>) -> Expr {
        Expr::new(Box::new(self), range.into())
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Literal {
    Nil,
    True,
    False,
    Number,
    String,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum BinaryOp {
    Equals,
    NotEquals,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum OpGroup {
    Equality,
    Comparison,
    Term,
    Factor,
    Unary,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Associativity {
    Left,
    Right,
}

pub trait Precedence {
    fn precedence(&self) -> OpGroup;
}

impl Precedence for BinaryOp {
    fn precedence(&self) -> OpGroup {
        match self {
            BinaryOp::Equals => OpGroup::Equality,
            BinaryOp::NotEquals => OpGroup::Equality,
            BinaryOp::LessThan => OpGroup::Comparison,
            BinaryOp::LessThanOrEqual => OpGroup::Comparison,
            BinaryOp::GreaterThan => OpGroup::Comparison,
            BinaryOp::GreaterThanOrEqual => OpGroup::Comparison,
            BinaryOp::Add => OpGroup::Term,
            BinaryOp::Sub => OpGroup::Term,
            BinaryOp::Mul => OpGroup::Factor,
            BinaryOp::Div => OpGroup::Factor,
        }
    }
}

impl Precedence for UnaryOp {
    fn precedence(&self) -> OpGroup {
        OpGroup::Unary
    }
}

pub trait Associate {
    fn associate(&self) -> Associativity;
}

impl Associate for BinaryOp {
    fn associate(&self) -> Associativity {
        Associativity::Left
    }
}

impl Associate for UnaryOp {
    fn associate(&self) -> Associativity {
        Associativity::Right
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Ast(Node<Box<Self>>);

impl Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Neg => f.write_str("-"),
            Self::Not => f.write_str("!"),
        }
    }
}

impl Display for BinaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Equals => f.write_str("=="),
            Self::NotEquals => f.write_str("!="),
            Self::LessThan => f.write_str("<"),
            Self::LessThanOrEqual => f.write_str("<="),
            Self::GreaterThan => f.write_str(">"),
            Self::GreaterThanOrEqual => f.write_str(">="),
            Self::Add => f.write_str("+"),
            Self::Sub => f.write_str("-"),
            Self::Mul => f.write_str("*"),
            Self::Div => f.write_str("/"),
        }
    }
}

#[cfg(test)]
fn print_expr(expr: Expr, source: &str) -> String {
    use crate::Range;

    fn inner(source: &str, expr: Expr, res: &mut String) {
        match *expr.node {
            Node::Literal(_) => res.push_str(&source[Range::from(expr.span)]),
            Node::Unary(op, expr) => parens(source, res, op, Some(expr)),
            Node::Binary(lhs, op, rhs) => parens(source, res, op, [lhs, rhs]),
            Node::Group(expr) => parens(source, res, "group", Some(expr)),
        }
    }

    fn parens(
        source: &str,
        res: &mut String,
        name: impl Display,
        exprs: impl IntoIterator<Item = Expr>,
    ) {
        use std::fmt::Write;

        res.push('(');
        write!(res, "{}", name).unwrap();

        for expr in exprs {
            res.push(' ');
            inner(source, expr, res);
        }

        res.push(')');
    }

    let mut res = String::new();
    inner(source, expr, &mut res);
    res
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_print() {
        let input = "-123 * (45.67)";

        let neg = Node::number().into_expr(1..4);
        let neg = Node::neg(neg).into_expr(0..4);

        let group = Node::number().into_expr(8..13);
        let group = Node::group(group).into_expr(7..14);

        let ast = Node::mul(neg, group).into_expr(0..14);

        assert_eq!(print_expr(ast, input), "(* (- 123) (group 45.67))");
    }
}
