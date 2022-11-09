use crate::{Expr, Idx, Node, Resolve, Result, Type, Value};
use std::{fmt::Debug, ops::Deref};

#[derive(Clone, Debug, Default)]
pub struct UntypedAstBuilder<'a> {
    exprs: Vec<Expr<'a>>,
}

impl<'a> UntypedAstBuilder<'a> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(&mut self, expr: Expr<'a>) -> Idx {
        let idx = self.exprs.len();
        self.exprs.push(expr);
        Idx(idx)
    }

    pub fn build(self) -> UntypedAst<'a> {
        UntypedAst { exprs: self.exprs }
    }
}

impl<'a> Resolve<'a, Expr<'a>> for UntypedAstBuilder<'a> {
    fn resolve(&self, idx: Idx) -> Expr<'a> {
        self.exprs[idx.0]
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct UntypedAst<'a> {
    exprs: Vec<Expr<'a>>,
}

impl<'a> UntypedAst<'a> {
    pub fn exprs(&self) -> &[Expr<'a>] {
        &self.exprs
    }

    pub fn into_inner(self) -> Vec<Expr<'a>> {
        self.exprs
    }
}

impl<'a> Deref for UntypedAst<'a> {
    type Target = [Expr<'a>];

    fn deref(&self) -> &Self::Target {
        &self.exprs
    }
}

impl<'a> Resolve<'a, Expr<'a>> for UntypedAst<'a> {
    fn resolve(&self, idx: Idx) -> Expr<'a> {
        self.exprs[idx.0]
    }
}

pub struct Adder<'a, T>(&'a mut Vec<T>);

impl<T> Adder<'_, T> {
    pub fn add(&mut self, item: T) {
        self.0.push(item);
    }
}

impl<T: Clone> Resolve<'_, Result<T>> for Adder<'_, T> {
    fn resolve(&self, idx: Idx) -> Result<T> {
        Ok(self.0[idx.0].clone())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct TypedAstBuilder<'a> {
    ast: UntypedAst<'a>,
    types: Vec<Type>,
}

impl<'a> TypedAstBuilder<'a> {
    pub fn new(ast: UntypedAst<'a>) -> Self {
        let types = Vec::with_capacity(ast.len());
        Self { ast, types }
    }

    pub fn split(&mut self) -> (&[Expr<'a>], Adder<'_, Type>) {
        (&self.ast, Adder(&mut self.types))
    }

    pub fn add(&mut self, typ: Type) {
        self.types.push(typ);
    }

    pub fn build(self) -> TypedAst<'a> {
        assert_eq!(self.ast.len(), self.types.len());

        TypedAst {
            exprs: self.ast.into_inner(),
            types: self.types,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct TypedAst<'a> {
    exprs: Vec<Expr<'a>>,
    types: Vec<Type>,
}

impl<'a> TypedAst<'a> {
    pub fn exprs(&self) -> &[Expr<'a>] {
        &self.exprs
    }

    pub fn types(&self) -> &[Type] {
        &self.types
    }

    pub fn into_inner(self) -> (Vec<Expr<'a>>, Vec<Type>) {
        (self.exprs, self.types)
    }
}

impl<'a> Deref for TypedAst<'a> {
    type Target = [Expr<'a>];

    fn deref(&self) -> &Self::Target {
        &self.exprs
    }
}

impl<'a> Resolve<'a, Expr<'a>> for TypedAst<'a> {
    fn resolve(&self, idx: Idx) -> Expr<'a> {
        self.exprs[idx.0]
    }
}

impl<'a> Resolve<'a, Type> for TypedAst<'a> {
    fn resolve(&self, idx: Idx) -> Type {
        self.types[idx.0]
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ValuedAstBuilder<'a> {
    ast: TypedAst<'a>,
    values: Vec<Value>,
}

impl<'a> ValuedAstBuilder<'a> {
    pub fn new(ast: TypedAst<'a>) -> Self {
        let values = Vec::with_capacity(ast.len());
        Self { ast, values }
    }

    pub fn split(&mut self) -> (&[Expr<'a>], Adder<'_, Value>) {
        (&self.ast, Adder(&mut self.values))
    }

    pub fn add(&mut self, value: Value) {
        self.values.push(value);
    }

    pub fn build(self) -> ValuedAst<'a> {
        assert_eq!(self.ast.len(), self.values.len());

        let (exprs, types) = self.ast.into_inner();
        ValuedAst {
            exprs,
            types,
            values: self.values,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ValuedAst<'a> {
    exprs: Vec<Expr<'a>>,
    types: Vec<Type>,
    values: Vec<Value>,
}

impl<'a> ValuedAst<'a> {
    pub fn value(&self, idx: Idx) -> &Value {
        &self.values[idx.0]
    }
}

impl<'a> ValuedAst<'a> {
    pub fn exprs(&self) -> &[Expr<'a>] {
        &self.exprs
    }

    pub fn types(&self) -> &[Type] {
        &self.types
    }

    pub fn values(&self) -> &[Value] {
        &self.values
    }

    pub fn into_inner(self) -> (Vec<Expr<'a>>, Vec<Type>, Vec<Value>) {
        (self.exprs, self.types, self.values)
    }
}

impl<'a> Deref for ValuedAst<'a> {
    type Target = [Expr<'a>];

    fn deref(&self) -> &Self::Target {
        &self.exprs
    }
}

impl<'a> Resolve<'a, Expr<'a>> for ValuedAst<'a> {
    fn resolve(&self, idx: Idx) -> Expr<'a> {
        self.exprs[idx.0]
    }
}

impl<'a> Resolve<'a, Type> for ValuedAst<'a> {
    fn resolve(&self, idx: Idx) -> Type {
        self.types[idx.0]
    }
}

impl<'a> Resolve<'a, Value> for ValuedAst<'a> {
    fn resolve(&self, idx: Idx) -> Value {
        self.values[idx.0].clone()
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Ast<'a> {
    nodes: Vec<Node>,
    ast: ValuedAst<'a>,
}

impl<'a> Ast<'a> {
    pub fn new(nodes: Vec<Node>, ast: ValuedAst<'a>) -> Self {
        Self { nodes, ast }
    }

    pub fn value(&self, node: Node) -> &Value {
        self.ast.value(node.idx)
    }
}

impl<'a> Deref for Ast<'a> {
    type Target = [Node];

    fn deref(&self) -> &Self::Target {
        &self.nodes
    }
}

impl<'a> Resolve<'a, Expr<'a>> for Ast<'a> {
    fn resolve(&self, idx: Idx) -> Expr<'a> {
        self.ast.resolve(idx)
    }
}

impl<'a> Resolve<'a, Type> for Ast<'a> {
    fn resolve(&self, idx: Idx) -> Type {
        self.ast.resolve(idx)
    }
}

impl<'a> Resolve<'a, Value> for Ast<'a> {
    fn resolve(&self, idx: Idx) -> Value {
        self.ast.resolve(idx)
    }
}
