use bumpalo::Bump;

use crate::{BoxedExpr, FunctionDef, Node, Span, Var};
use std::fmt::Debug;

pub type StmtNode<'a> = Node<Stmt<'a>>;
pub type BoxedStmt<'a> = Node<&'a Stmt<'a>>;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Stmt<'a> {
    Expression {
        expr: BoxedExpr<'a>,
    },
    Class(ClassDecl<'a>),
    Function(FunctionDecl<'a>),
    If {
        condition: BoxedExpr<'a>,
        then_: BoxedStmt<'a>,
        else_: Option<BoxedStmt<'a>>,
    },
    Print {
        expr: BoxedExpr<'a>,
    },
    Return {
        expr: Option<BoxedExpr<'a>>,
    },
    Var {
        name: Node<&'a str>,
        initializer: Option<BoxedExpr<'a>>,
    },
    While {
        condition: BoxedExpr<'a>,
        body: BoxedStmt<'a>,
    },
    Block {
        stmts: &'a [StmtNode<'a>],
    },
}

impl<'a> Stmt<'a> {
    pub fn expression(expr: BoxedExpr<'a>) -> Self {
        Self::Expression { expr }
    }

    pub fn class(
        name: Node<&'a str>,
        superclass: Option<Node<Var<'a>>>,
        members: &'a mut [Node<FunctionDecl<'a>>],
    ) -> Self {
        Self::Class(ClassDecl::new(name, superclass, members))
    }

    pub fn fun(name: Node<&'a str>, kind: FunctionKind, fun: FunctionDef<'a>) -> FunctionDecl<'a> {
        FunctionDecl { name, kind, fun }
    }

    pub fn if_(condition: BoxedExpr<'a>, then_: BoxedStmt<'a>) -> Self {
        Self::If {
            condition,
            then_,
            else_: None,
        }
    }

    pub fn if_else(condition: BoxedExpr<'a>, then_: BoxedStmt<'a>, else_: BoxedStmt<'a>) -> Self {
        Self::If {
            condition,
            then_,
            else_: Some(else_),
        }
    }

    pub fn print(expr: BoxedExpr<'a>) -> Self {
        Self::Print { expr }
    }

    pub fn return_(expr: impl Into<Option<BoxedExpr<'a>>>) -> Self {
        Self::Return { expr: expr.into() }
    }

    pub fn var(name: Node<&'a str>, initializer: impl Into<Option<BoxedExpr<'a>>>) -> Self {
        Self::Var {
            name,
            initializer: initializer.into(),
        }
    }

    pub fn while_(condition: BoxedExpr<'a>, body: BoxedStmt<'a>) -> Self {
        Self::While { condition, body }
    }

    pub fn block(stmts: &'a [StmtNode<'a>]) -> Self {
        Self::Block { stmts }
    }

    pub fn at(self, span: impl Into<Span>) -> StmtNode<'a> {
        Node::new(self, span)
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct ClassDecl<'a> {
    pub name: Node<&'a str>,
    pub superclass: Option<Node<Var<'a>>>,
    members: Members<'a, Node<FunctionDecl<'a>>>,
}

impl<'a> ClassDecl<'a> {
    pub fn new(
        name: Node<&'a str>,
        superclass: Option<Node<Var<'a>>>,
        members: &'a mut [Node<FunctionDecl<'a>>],
    ) -> Self {
        let members = Members::new(members, |m| m.item.kind);
        Self {
            name,
            superclass,
            members,
        }
    }

    pub fn members(&self) -> &Members<'a, Node<FunctionDecl<'a>>> {
        &self.members
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct FunctionDecl<'a> {
    pub name: Node<&'a str>,
    pub kind: FunctionKind,
    pub fun: FunctionDef<'a>,
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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Members<'a, T> {
    members: &'a [T],
    methods: usize,
    class_methods: usize,
}

impl<'a, T> Members<'a, T> {
    pub fn new(members: &'a mut [T], to_kind: impl Fn(&T) -> FunctionKind) -> Self {
        members.sort_by_key(|m| to_kind(m));

        let (methods, class_methods) =
            members
                .iter()
                .fold((0, 0), |(methods, class_methods), member| {
                    match to_kind(member) {
                        FunctionKind::Method => (methods + 1, class_methods + 1),
                        FunctionKind::ClassMethod => (methods, class_methods + 1),
                        FunctionKind::Property => (methods, class_methods),
                        otherwise => panic!("unsupported class member of kind {otherwise}"),
                    }
                });

        Self {
            members,
            methods,
            class_methods,
        }
    }

    pub fn methods(&self) -> impl Iterator<Item = &T> {
        self.members[..self.methods].iter()
    }

    pub fn class_methods(&self) -> impl Iterator<Item = &T> {
        self.members[self.methods..self.class_methods].iter()
    }

    pub fn properties(&self) -> impl Iterator<Item = &T> {
        self.members[self.class_methods..].iter()
    }

    pub fn map<U>(&self, arena: &'a Bump, map: impl FnMut(&T) -> U) -> Members<'a, U> {
        let members = self.members.iter().map(map);
        let members = arena.alloc_slice_fill_iter(members);

        Members {
            members,
            methods: self.methods,
            class_methods: self.class_methods,
        }
    }
}
