use crate::{ExprNode, Node, Span};
use std::{fmt::Debug, rc::Rc};

pub type StmtNode<'a> = Node<Stmt<'a>>;
pub type BoxedStmt<'a> = Node<Rc<Stmt<'a>>>;

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt<'a> {
    Expression {
        expr: ExprNode<'a>,
    },
    If {
        condition: ExprNode<'a>,
        then_: BoxedStmt<'a>,
        else_: Option<BoxedStmt<'a>>,
    },
    // Function(&'a str, Rc<[ExprNode<'a>]>, Rc<[StmtNode<'a>]>),
    Print {
        expr: ExprNode<'a>,
    },
    Var {
        name: &'a str,
        initializer: Option<ExprNode<'a>>,
    },
    While {
        condition: ExprNode<'a>,
        body: BoxedStmt<'a>,
    },
    Block {
        stmts: Rc<[StmtNode<'a>]>,
    },
}

impl<'a> Stmt<'a> {
    pub fn expression(expr: ExprNode<'a>) -> Self {
        Self::Expression { expr }
    }

    pub fn if_(condition: ExprNode<'a>, then_: StmtNode<'a>) -> Self {
        Self::If {
            condition,
            then_: then_.map(Rc::new),
            else_: None,
        }
    }

    pub fn if_else(condition: ExprNode<'a>, then_: StmtNode<'a>, else_: StmtNode<'a>) -> Self {
        Self::If {
            condition,
            then_: then_.map(Rc::new),
            else_: Some(else_.map(Rc::new)),
        }
    }

    pub fn print(expr: ExprNode<'a>) -> Self {
        Self::Print { expr }
    }

    pub fn var(name: &'a str, initializer: impl Into<Option<ExprNode<'a>>>) -> Self {
        Self::Var {
            name,
            initializer: initializer.into(),
        }
    }

    pub fn while_(condition: ExprNode<'a>, body: StmtNode<'a>) -> Self {
        Self::While {
            condition,
            body: body.map(Rc::new),
        }
    }

    pub fn block(stmts: impl Into<Rc<[StmtNode<'a>]>>) -> Self {
        Self::Block {
            stmts: stmts.into(),
        }
    }

    pub fn at(self, span: impl Into<Span>) -> StmtNode<'a> {
        Node::new(self, span)
    }
}
