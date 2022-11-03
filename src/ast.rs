use crate::Span;
use std::fmt::{Debug, Display};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    pub idx: Idx,
    pub span: Span,
}

impl Expr {
    pub fn new(idx: Idx, span: Span) -> Self {
        Self { idx, span }
    }
}

#[derive(Clone, PartialEq)]
pub struct BoxedExpr<'a> {
    pub node: Box<Node<'a, BoxedExpr<'a>>>,
    pub span: Span,
}

impl<'a> BoxedExpr<'a> {
    pub fn new(node: Box<Node<'a, Self>>, span: Span) -> Self {
        Self { node, span }
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[repr(transparent)]
pub struct Idx(pub usize);

impl Idx {
    pub fn into_expr(self, range: impl Into<Span>) -> Expr {
        Expr::new(self, range.into())
    }
}
#[derive(Clone, Debug, Default)]
pub struct AstBuilder<'a> {
    nodes: Vec<Node<'a>>,
}

impl<'a> AstBuilder<'a> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(&mut self, node: Node<'a>) -> Idx {
        let idx = self.nodes.len();
        self.nodes.push(node);
        Idx(idx)
    }

    pub fn build(self) -> Ast<'a> {
        Ast { nodes: self.nodes }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Ast<'a> {
    nodes: Vec<Node<'a>>,
}

pub trait Resolve<'a, C = Idx> {
    fn resolve(&self, context: &C) -> Node<'a>;
}

impl<'a> Resolve<'a> for Ast<'a> {
    fn resolve(&self, context: &Idx) -> Node<'a> {
        self.nodes[context.0]
    }
}

impl<'a> Resolve<'a> for AstBuilder<'a> {
    fn resolve(&self, context: &Idx) -> Node<'a> {
        self.nodes[context.0]
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Node<'a, T: Sized = Expr> {
    Literal(Literal<'a>),
    Unary(UnaryOp, T),
    Binary(T, BinaryOp, T),
    Group(T),
}

impl<'a, T: Sized> Node<'a, T> {
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

    pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> Node<'a, U> {
        match self {
            Self::Literal(lit) => Node::Literal(lit),
            Self::Unary(op, expr) => Node::Unary(op, f(expr)),
            Self::Binary(lhs, op, rhs) => Node::Binary(f(lhs), op, f(rhs)),
            Self::Group(expr) => Node::Group(f(expr)),
        }
    }
}

impl<'a> Node<'a, BoxedExpr<'a>> {
    pub fn into_boxed_expr(self, range: impl Into<Span>) -> BoxedExpr<'a> {
        BoxedExpr::new(Box::new(self), range.into())
    }
}

impl Expr {
    pub fn resolve<'a, R: Resolve<'a>>(self, resolver: &'a R) -> BoxedExpr {
        let node = resolver.resolve(&self.idx);
        let node = node.map(|e| e.resolve(resolver));
        node.into_boxed_expr(self.span)
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

impl Debug for BoxedExpr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.node, f)?;
        f.write_str(" @ ")?;
        Debug::fmt(&self.span, f)
    }
}

#[cfg(test)]
fn print_expr(expr: BoxedExpr, source: &str) -> String {
    use crate::Range;

    fn inner(source: &str, expr: BoxedExpr, res: &mut String) {
        match *expr.node {
            Node::Literal(_) => res.push_str(&source[Range::from(expr.span)]),
            Node::Unary(op, expr) => parens(source, res, op, Some(expr)),
            Node::Binary(lhs, op, rhs) => parens(source, res, op, [lhs, rhs]),
            Node::Group(expr) => parens(source, res, "group", Some(expr)),
        }
    }

    fn parens<'a>(
        source: &'a str,
        res: &mut String,
        name: impl Display,
        exprs: impl IntoIterator<Item = BoxedExpr<'a>>,
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

        let neg = Node::number(123.0).into_boxed_expr(1..4);
        let neg = Node::neg(neg).into_boxed_expr(0..4);

        let group = Node::number(45.67).into_boxed_expr(8..13);
        let group = Node::group(group).into_boxed_expr(7..14);

        let ast = Node::mul(neg, group).into_boxed_expr(0..14);

        assert_eq!(print_expr(ast, input), "(* (- 123) (group 45.67))");
    }
}
