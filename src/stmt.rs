use crate::{BoxedExpr, FunctionDef, Ident, Members, Node, Var};
use std::fmt::Debug;

pub type StmtNode<'env> = Node<Stmt<'env>>;
pub type BoxedStmt<'env> = Node<&'env Stmt<'env>>;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Stmt<'env> {
    Expression {
        expr: BoxedExpr<'env>,
    },
    Class(ClassDecl<'env>),
    Function(FunctionDecl<'env>),
    If {
        condition: BoxedExpr<'env>,
        then_: BoxedStmt<'env>,
        else_: Option<BoxedStmt<'env>>,
    },
    Print {
        expr: BoxedExpr<'env>,
    },
    Return {
        expr: Option<BoxedExpr<'env>>,
    },
    Var {
        name: Ident<'env>,
        initializer: Option<BoxedExpr<'env>>,
    },
    While {
        condition: BoxedExpr<'env>,
        body: BoxedStmt<'env>,
    },
    Block {
        stmts: &'env [StmtNode<'env>],
    },
}

impl<'env> Stmt<'env> {
    pub fn expression(expr: BoxedExpr<'env>) -> Self {
        Self::Expression { expr }
    }

    pub fn class(
        name: Ident<'env>,
        superclass: Option<Node<Var<'env>>>,
        members: &'env mut [Node<FunctionDecl<'env>>],
    ) -> Self {
        Self::Class(ClassDecl::new(name, superclass, members))
    }

    pub fn fun(
        name: Ident<'env>,
        kind: FunctionKind,
        fun: FunctionDef<'env>,
    ) -> FunctionDecl<'env> {
        FunctionDecl { name, kind, fun }
    }

    pub fn if_(condition: BoxedExpr<'env>, then_: BoxedStmt<'env>) -> Self {
        Self::If {
            condition,
            then_,
            else_: None,
        }
    }

    pub fn if_else(
        condition: BoxedExpr<'env>,
        then_: BoxedStmt<'env>,
        else_: BoxedStmt<'env>,
    ) -> Self {
        Self::If {
            condition,
            then_,
            else_: Some(else_),
        }
    }

    pub fn print(expr: BoxedExpr<'env>) -> Self {
        Self::Print { expr }
    }

    pub fn return_(expr: impl Into<Option<BoxedExpr<'env>>>) -> Self {
        Self::Return { expr: expr.into() }
    }

    pub fn var(name: Ident<'env>, initializer: impl Into<Option<BoxedExpr<'env>>>) -> Self {
        Self::Var {
            name,
            initializer: initializer.into(),
        }
    }

    pub fn while_(condition: BoxedExpr<'env>, body: BoxedStmt<'env>) -> Self {
        Self::While { condition, body }
    }

    pub fn block(stmts: &'env [StmtNode<'env>]) -> Self {
        Self::Block { stmts }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct ClassDecl<'env> {
    pub name: Ident<'env>,
    pub superclass: Option<Node<Var<'env>>>,
    members: Members<'env, Node<FunctionDecl<'env>>>,
}

impl<'env> ClassDecl<'env> {
    pub fn new(
        name: Ident<'env>,
        superclass: Option<Node<Var<'env>>>,
        members: &'env mut [Node<FunctionDecl<'env>>],
    ) -> Self {
        let members = Members::new(members);
        Self {
            name,
            superclass,
            members,
        }
    }

    pub fn members(&self) -> &Members<'env, Node<FunctionDecl<'env>>> {
        &self.members
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct FunctionDecl<'env> {
    pub name: Ident<'env>,
    pub kind: FunctionKind,
    pub fun: FunctionDef<'env>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum FunctionKind {
    Class,
    Superclass,
    Function,
    Method,
    ClassMethod,
    Property,
}
