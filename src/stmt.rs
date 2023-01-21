use crate::{ExprNode, FunctionDef, Node, Span, Var};
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

    pub fn class(
        name: Node<&'a str>,
        superclass: Option<Node<Var<'a>>>,
        members: Vec<Node<FunctionDecl<'a>>>,
    ) -> Self {
        Self::Class(ClassDecl::new(name, superclass, members))
    }

    pub fn fun(name: Node<&'a str>, kind: FunctionKind, fun: FunctionDef<'a>) -> FunctionDecl<'a> {
        FunctionDecl { name, kind, fun }
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
    pub superclass: Option<Node<Var<'a>>>,
    members: Members<Node<FunctionDecl<'a>>>,
}

impl<'a> ClassDecl<'a> {
    pub fn new(
        name: Node<&'a str>,
        superclass: Option<Node<Var<'a>>>,
        members: Vec<Node<FunctionDecl<'a>>>,
    ) -> Self {
        let members = Members::new(members, |m| m.item.kind);
        Self {
            name,
            superclass,
            members,
        }
    }

    pub fn members(&self) -> &Members<Node<FunctionDecl<'a>>> {
        &self.members
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct FunctionDecl<'a> {
    pub name: Node<&'a str>,
    pub kind: FunctionKind,
    pub fun: FunctionDef<'a>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum FunctionKind {
    Class,
    Function,
    Method,
    ClassMethod,
    Property,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Members<T> {
    members: Rc<[T]>,
    methods: usize,
    class_methods: usize,
}

impl<T> Members<T> {
    pub fn new(mut members: Vec<T>, to_kind: impl Fn(&T) -> FunctionKind) -> Self {
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
            members: members.into(),
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

    pub fn map<U>(&self, map: impl FnMut(&T) -> U) -> Members<U> {
        let members = self.members.iter().map(map).collect();

        Members {
            members,
            methods: self.methods,
            class_methods: self.class_methods,
        }
    }
}
