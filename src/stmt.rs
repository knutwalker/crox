use crate::{ExprNode, Node, Span};
use std::{fmt::Debug, rc::Rc};

pub type StmtNode<'a> = Node<Stmt<'a>>;
pub type BoxedStmt<'a> = Node<Rc<Stmt<'a>>>;

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt<'a> {
    Expression {
        expr: ExprNode<'a>,
    },
    Function(FunctionDecl<'a>),
    If {
        condition: ExprNode<'a>,
        then_: BoxedStmt<'a>,
        else_: Option<BoxedStmt<'a>>,
    },
    Print {
        expr: ExprNode<'a>,
    },
    Return {
        expr: Option<ExprNode<'a>>,
    },
    Var {
        name: Node<&'a str>,
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

    pub fn fun(
        name: Node<&'a str>,
        params: impl Into<Rc<[Node<&'a str>]>>,
        body: impl Into<Rc<[StmtNode<'a>]>>,
    ) -> Self {
        Self::Function(FunctionDecl {
            name,
            params: params.into(),
            body: body.into(),
        })
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

    pub fn return_(expr: impl Into<Option<ExprNode<'a>>>) -> Self {
        Self::Return { expr: expr.into() }
    }

    pub fn var(name: Node<&'a str>, initializer: impl Into<Option<ExprNode<'a>>>) -> Self {
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

#[derive(Clone, Debug, PartialEq)]
pub struct FunctionDecl<'a> {
    pub name: Node<&'a str>,
    pub params: Rc<[Node<&'a str>]>,
    pub body: Rc<[StmtNode<'a>]>,
}
