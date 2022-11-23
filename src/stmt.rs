use crate::{ExprNode, Node, Span};
use std::fmt::Debug;

pub type StmtNode<'a> = Node<Stmt<'a>>;

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt<'a> {
    Expression(ExprNode<'a>),
    Print(ExprNode<'a>),
}

impl<'a> Stmt<'a> {
    pub fn expression(expr: ExprNode<'a>) -> Self {
        Self::Expression(expr)
    }

    pub fn print(expr: ExprNode<'a>) -> Self {
        Self::Print(expr)
    }

    pub fn node(self, span: impl Into<Span>) -> StmtNode<'a> {
        Node::new(self, span)
    }
}
