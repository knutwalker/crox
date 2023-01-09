use crate::{ExprNode, FunctionDef, Node, Span};
use std::{fmt::Debug, rc::Rc};

pub type StmtNode<'a> = Node<Stmt<'a>>;
pub type BoxedStmt<'a> = Node<Rc<Stmt<'a>>>;

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt<'a> {
    Expression {
        expr: ExprNode<'a>,
    },
    Class(ClassDecl<'a>),
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

pub trait StmtArg<'a> {
    fn stmt(&self) -> &Stmt<'a>;
    fn span(&self) -> Span;
}

impl<'a> StmtArg<'a> for StmtNode<'a> {
    fn stmt(&self) -> &Stmt<'a> {
        &self.item
    }

    fn span(&self) -> Span {
        self.span
    }
}

impl<'a> StmtArg<'a> for BoxedStmt<'a> {
    fn stmt(&self) -> &Stmt<'a> {
        &self.item
    }

    fn span(&self) -> Span {
        self.span
    }
}

impl<'a> Stmt<'a> {
    pub fn expression(expr: ExprNode<'a>) -> Self {
        Self::Expression { expr }
    }

    pub fn class(name: Node<&'a str>, methods: impl Into<Rc<[Node<FunctionDecl<'a>>]>>) -> Self {
        Self::Class(ClassDecl {
            name,
            methods: methods.into(),
        })
    }

    pub fn fun(name: Node<&'a str>, fun: FunctionDef<'a>) -> FunctionDecl<'a> {
        FunctionDecl { name, fun }
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
pub struct ClassDecl<'a> {
    pub name: Node<&'a str>,
    pub methods: Rc<[Node<FunctionDecl<'a>>]>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct FunctionDecl<'a> {
    pub name: Node<&'a str>,
    pub fun: FunctionDef<'a>,
}
