use crate::{BoxedExpr, Bump, Function, FunctionDef, Ident, Node, Var};
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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Members<'env, T> {
    members: &'env [T],
    methods: usize,
    class_methods: usize,
}

impl<'env, T: MemberConstructor<'env>> Members<'env, T> {
    pub fn new(members: &'env mut [T]) -> Self {
        members.sort_by_key(|m| (m.kind(), m.name()));

        let (methods, class_methods) =
            members
                .iter()
                .fold((0, 0), |(methods, class_methods), member| {
                    match member.kind() {
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
}

impl<'env, T: MemberItem<'env>> Members<'env, T> {
    pub fn method(&self, name: &str) -> Option<&T> {
        let methods = &self.members[..self.methods];
        Self::find_by_name(methods, name)
    }

    pub fn class_method(&self, name: &str) -> Option<&T> {
        let methods = &self.members[self.methods..self.class_methods];
        Self::find_by_name(methods, name)
    }

    pub fn property(&self, name: &str) -> Option<&T> {
        let methods = &self.members[self.class_methods..];
        Self::find_by_name(methods, name)
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

    fn find_by_name<'this>(methods: &'this [T], name: &str) -> Option<&'this T> {
        methods.iter().find(|m| m.name() == name)
    }
}

impl<'env, T> Members<'env, T> {
    pub fn map<U>(&self, arena: &'env Bump, map: impl FnMut(&T) -> U) -> Members<'env, U> {
        let members = self.members.iter().map(map);
        let members = arena.alloc_slice_fill_iter(members);

        Members {
            members,
            methods: self.methods,
            class_methods: self.class_methods,
        }
    }
}

pub trait MemberItem<'env> {
    fn name(&self) -> &'env str;
}

pub trait MemberConstructor<'env>: MemberItem<'env> {
    fn kind(&self) -> FunctionKind;
}

impl<'env> MemberItem<'env> for Node<FunctionDecl<'env>> {
    fn name(&self) -> &'env str {
        self.item.name.item
    }
}

impl<'env> MemberConstructor<'env> for Node<FunctionDecl<'env>> {
    fn kind(&self) -> FunctionKind {
        self.item.kind
    }
}

impl<'env> MemberItem<'env> for &'env Function<'env> {
    fn name(&self) -> &'env str {
        self.name
    }
}
