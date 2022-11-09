use crate::{Expr, ExprNode, Idx, Resolve, Result, Type, Value};
use std::ops::Deref;

#[derive(Clone, Debug, Default)]
pub struct UntypedAstBuilder<'a> {
    nodes: Vec<ExprNode<'a>>,
}

impl<'a> UntypedAstBuilder<'a> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(&mut self, node: ExprNode<'a>) -> Idx {
        let idx = self.nodes.len();
        self.nodes.push(node);
        Idx(idx)
    }

    pub fn build(self) -> UntypedAst<'a> {
        UntypedAst { nodes: self.nodes }
    }
}

impl<'a> Resolve<'a> for UntypedAstBuilder<'a> {
    fn resolve(&self, idx: Idx) -> ExprNode<'a> {
        self.nodes[idx.0]
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct UntypedAst<'a> {
    nodes: Vec<ExprNode<'a>>,
}

impl<'a> UntypedAst<'a> {
    pub fn nodes(&self) -> &[ExprNode<'a>] {
        &self.nodes
    }

    pub fn into_inner(self) -> Vec<ExprNode<'a>> {
        self.nodes
    }
}

impl<'a> Deref for UntypedAst<'a> {
    type Target = [ExprNode<'a>];

    fn deref(&self) -> &Self::Target {
        &self.nodes
    }
}

impl<'a> Resolve<'a> for UntypedAst<'a> {
    fn resolve(&self, idx: Idx) -> ExprNode<'a> {
        self.nodes[idx.0]
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

    pub fn split(&mut self) -> (&[ExprNode<'a>], Adder<'_, Type>) {
        (&self.ast, Adder(&mut self.types))
    }

    pub fn add(&mut self, typ: Type) {
        self.types.push(typ);
    }

    pub fn build(self) -> TypedAst<'a> {
        assert_eq!(self.ast.len(), self.types.len());

        TypedAst {
            nodes: self.ast.into_inner(),
            types: self.types,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct TypedAst<'a> {
    nodes: Vec<ExprNode<'a>>,
    types: Vec<Type>,
}

impl<'a> TypedAst<'a> {
    pub fn nodes(&self) -> &[ExprNode<'a>] {
        &self.nodes
    }

    pub fn types(&self) -> &[Type] {
        &self.types
    }

    pub fn into_inner(self) -> (Vec<ExprNode<'a>>, Vec<Type>) {
        (self.nodes, self.types)
    }
}

impl<'a> Deref for TypedAst<'a> {
    type Target = [ExprNode<'a>];

    fn deref(&self) -> &Self::Target {
        &self.nodes
    }
}

impl<'a> Resolve<'a> for TypedAst<'a> {
    fn resolve(&self, idx: Idx) -> ExprNode<'a> {
        self.nodes[idx.0]
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

    pub fn split(&mut self) -> (&[ExprNode<'a>], Adder<'_, Value>) {
        (&self.ast, Adder(&mut self.values))
    }

    pub fn add(&mut self, value: Value) {
        self.values.push(value);
    }

    pub fn build(self) -> ValuedAst<'a> {
        assert_eq!(self.ast.len(), self.values.len());

        let (nodes, types) = self.ast.into_inner();
        ValuedAst {
            nodes,
            types,
            values: self.values,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ValuedAst<'a> {
    nodes: Vec<ExprNode<'a>>,
    types: Vec<Type>,
    values: Vec<Value>,
}

impl<'a> ValuedAst<'a> {
    pub fn value(&self, idx: Idx) -> &Value {
        &self.values[idx.0]
    }
}

impl<'a> ValuedAst<'a> {
    pub fn nodes(&self) -> &[ExprNode<'a>] {
        &self.nodes
    }

    pub fn types(&self) -> &[Type] {
        &self.types
    }

    pub fn values(&self) -> &[Value] {
        &self.values
    }

    pub fn into_inner(self) -> (Vec<ExprNode<'a>>, Vec<Type>, Vec<Value>) {
        (self.nodes, self.types, self.values)
    }
}

impl<'a> Deref for ValuedAst<'a> {
    type Target = [ExprNode<'a>];

    fn deref(&self) -> &Self::Target {
        &self.nodes
    }
}

impl<'a> Resolve<'a> for ValuedAst<'a> {
    fn resolve(&self, idx: Idx) -> ExprNode<'a> {
        self.nodes[idx.0]
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
    exprs: Vec<Expr>,
    ast: ValuedAst<'a>,
}

impl<'a> Ast<'a> {
    pub fn new(exprs: Vec<Expr>, ast: ValuedAst<'a>) -> Self {
        Self { exprs, ast }
    }

    pub fn value(&self, expr: Expr) -> &Value {
        self.ast.value(expr.idx)
    }
}

impl<'a> Deref for Ast<'a> {
    type Target = [Expr];

    fn deref(&self) -> &Self::Target {
        &self.exprs
    }
}

impl<'a> Resolve<'a> for Ast<'a> {
    fn resolve(&self, idx: Idx) -> ExprNode<'a> {
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
