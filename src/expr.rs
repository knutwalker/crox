use crate::{Node, Span};
use std::fmt::{Debug, Display};

pub type ExprNode<'a> = Node<Box<Expr<'a>>>;

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<'a> {
    Literal(Literal<'a>),
    Unary(UnaryOp, ExprNode<'a>),
    Binary(ExprNode<'a>, BinaryOp, ExprNode<'a>),
    Group(ExprNode<'a>),
}

impl<'a> Expr<'a> {
    pub fn nil() -> Self {
        Self::Literal(Literal::Nil)
    }

    pub fn tru() -> Self {
        Self::Literal(Literal::True)
    }

    pub fn fals() -> Self {
        Self::Literal(Literal::False)
    }

    pub fn number(num: f64) -> Self {
        Self::Literal(Literal::Number(num))
    }

    pub fn string(s: &'a str) -> Self {
        Self::Literal(Literal::String(s))
    }

    pub fn neg(expr: ExprNode<'a>) -> Self {
        Self::Unary(UnaryOp::Neg, expr)
    }

    pub fn not(expr: ExprNode<'a>) -> Self {
        Self::Unary(UnaryOp::Not, expr)
    }

    pub fn unary(op: UnaryOp, expr: ExprNode<'a>) -> Self {
        Self::Unary(op, expr)
    }

    pub fn add(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary(lhs, BinaryOp::Add, rhs)
    }

    pub fn sub(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary(lhs, BinaryOp::Sub, rhs)
    }

    pub fn mul(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary(lhs, BinaryOp::Mul, rhs)
    }

    pub fn div(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary(lhs, BinaryOp::Div, rhs)
    }

    pub fn equals(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary(lhs, BinaryOp::Equals, rhs)
    }

    pub fn not_equals(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary(lhs, BinaryOp::NotEquals, rhs)
    }

    pub fn less_than(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary(lhs, BinaryOp::LessThan, rhs)
    }

    pub fn less_than_or_equal(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary(lhs, BinaryOp::LessThanOrEqual, rhs)
    }

    pub fn greater_than(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary(lhs, BinaryOp::GreaterThan, rhs)
    }

    pub fn greater_than_or_equal(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary(lhs, BinaryOp::GreaterThanOrEqual, rhs)
    }

    pub fn binary(lhs: ExprNode<'a>, op: BinaryOp, rhs: ExprNode<'a>) -> Self {
        Self::Binary(lhs, op, rhs)
    }

    pub fn group(expr: ExprNode<'a>) -> Self {
        Self::Group(expr)
    }

    pub fn node(self, span: impl Into<Span>) -> ExprNode<'a> {
        Node::new(Box::new(self), span)
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Literal<'a> {
    Nil,
    True,
    False,
    Number(f64),
    String(&'a str),
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
fn print_expr(node: ExprNode, source: &str) -> String {
    use crate::Range;

    fn inner(source: &str, node: ExprNode, res: &mut String) {
        match *node.item {
            Expr::Literal(_) => res.push_str(&source[Range::from(node.span)]),
            Expr::Unary(op, expr) => parens(source, res, op, Some(expr)),
            Expr::Binary(lhs, op, rhs) => parens(source, res, op, [lhs, rhs]),
            Expr::Group(expr) => parens(source, res, "group", Some(expr)),
        }
    }

    fn parens<'a>(
        source: &'a str,
        res: &mut String,
        name: impl Display,
        nodes: impl IntoIterator<Item = ExprNode<'a>>,
    ) {
        use std::fmt::Write;

        res.push('(');
        write!(res, "{}", name).unwrap();

        for node in nodes {
            res.push(' ');
            inner(source, node, res);
        }

        res.push(')');
    }

    let mut res = String::new();
    inner(source, node, &mut res);
    res
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_print() {
        let input = "-123 * (45.67)";

        let neg = Expr::number(123.0).node(1..4);
        let neg = Expr::neg(neg).node(0..4);

        let group = Expr::number(45.67).node(8..13);
        let group = Expr::group(group).node(7..14);

        let ast = Expr::mul(neg, group).node(0..14);

        assert_eq!(print_expr(ast, input), "(* (- 123) (group 45.67))");
    }
}
