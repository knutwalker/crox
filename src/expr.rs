use crate::{Node, Span};
use std::{
    fmt::{Debug, Display},
    rc::Rc,
};

pub type ExprNode<'a> = Node<Rc<Expr<'a>>>;

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<'a> {
    Literal(Literal<'a>),
    Var(&'a str),
    Assignment(&'a str, ExprNode<'a>),
    Unary(UnaryOp, ExprNode<'a>),
    Logical(ExprNode<'a>, LogicalOp, ExprNode<'a>),
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

    pub fn var(s: &'a str) -> Self {
        Self::Var(s)
    }

    pub fn assign(s: &'a str, expr: ExprNode<'a>) -> Self {
        Self::Assignment(s, expr)
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

    pub fn and(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Logical(lhs, LogicalOp::And, rhs)
    }

    pub fn or(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Logical(lhs, LogicalOp::Or, rhs)
    }

    pub fn logical(lhs: ExprNode<'a>, op: LogicalOp, rhs: ExprNode<'a>) -> Self {
        Self::Logical(lhs, op, rhs)
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

    pub fn at(self, span: impl Into<Span>) -> ExprNode<'a> {
        Node::new(Rc::new(self), span)
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
pub enum LogicalOp {
    And,
    Or,
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

impl Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Neg => f.write_str("-"),
            Self::Not => f.write_str("!"),
        }
    }
}

impl Display for LogicalOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::And => f.write_str("and"),
            Self::Or => f.write_str("or"),
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

    fn inner(source: &str, node: &ExprNode, res: &mut String) {
        match &*node.item {
            Expr::Literal(_) => res.push_str(&source[Range::from(node.span)]),
            Expr::Var(ident) => res.push_str(ident),
            Expr::Assignment(ident, expr) => {
                res.push_str(ident);
                parens(source, res, "=", Some(expr));
            }
            Expr::Unary(op, expr) => parens(source, res, op, Some(expr)),
            Expr::Logical(lhs, op, rhs) => parens(source, res, op, [lhs, rhs]),
            Expr::Binary(lhs, op, rhs) => parens(source, res, op, [lhs, rhs]),
            Expr::Group(expr) => parens(source, res, "group", Some(expr)),
        }
    }

    fn parens<'x, 'a: 'x>(
        source: &'a str,
        res: &mut String,
        name: impl Display,
        nodes: impl IntoIterator<Item = &'x ExprNode<'a>> + 'x,
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
    inner(source, &node, &mut res);
    res
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_print() {
        let input = "-123 * (45.67)";

        let neg = Expr::number(123.0).at(1..4);
        let neg = Expr::neg(neg).at(0..4);

        let group = Expr::number(45.67).at(8..13);
        let group = Expr::group(group).at(7..14);

        let ast = Expr::mul(neg, group).at(0..14);

        assert_eq!(print_expr(ast, input), "(* (- 123) (group 45.67))");
    }
}
