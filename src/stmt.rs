use crate::{ExprNode, Node, Span};
use std::{fmt::Debug, rc::Rc};

pub type StmtNode<'a> = Node<Stmt<'a>>;
pub type BoxedStmt<'a> = Node<Rc<Stmt<'a>>>;

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt<'a> {
    Expression(ExprNode<'a>),
    If(ExprNode<'a>, BoxedStmt<'a>, Option<BoxedStmt<'a>>),
    Print(ExprNode<'a>),
    Var(&'a str, Option<ExprNode<'a>>),
    Block(Rc<[StmtNode<'a>]>),
}

impl<'a> Stmt<'a> {
    pub fn expression(expr: ExprNode<'a>) -> Self {
        Self::Expression(expr)
    }

    pub fn if_(condition: ExprNode<'a>, then_: StmtNode<'a>) -> Self {
        Self::If(condition, then_.map(Rc::new), None)
    }

    pub fn if_else(condition: ExprNode<'a>, then_: StmtNode<'a>, else_: StmtNode<'a>) -> Self {
        Self::If(condition, then_.map(Rc::new), Some(else_.map(Rc::new)))
    }

    pub fn print(expr: ExprNode<'a>) -> Self {
        Self::Print(expr)
    }

    pub fn var(name: &'a str, initializer: impl Into<Option<ExprNode<'a>>>) -> Self {
        Self::Var(name, initializer.into())
    }

    pub fn block(stmts: impl Into<Rc<[StmtNode<'a>]>>) -> Self {
        Self::Block(stmts.into())
    }

    pub fn at(self, span: impl Into<Span>) -> StmtNode<'a> {
        Node::new(self, span)
    }
}
