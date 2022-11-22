use crate::{eval::ValueExpr, eval_node, Node, TypedExpr};
use std::{fmt::Debug, ops::Deref};

#[derive(Clone, Debug, PartialEq)]
pub struct Ast<'a> {
    nodes: Vec<Node<ValueExpr<'a>>>,
}

impl<'a> Ast<'a> {
    pub fn new(nodes: Vec<Node<ValueExpr<'a>>>) -> Self {
        Self { nodes }
    }
}

impl<'a> Deref for Ast<'a> {
    type Target = [Node<ValueExpr<'a>>];

    fn deref(&self) -> &Self::Target {
        &self.nodes
    }
}

impl<'a> FromIterator<Node<TypedExpr<'a>>> for Ast<'a> {
    fn from_iter<T: IntoIterator<Item = Node<TypedExpr<'a>>>>(iter: T) -> Self {
        Self {
            nodes: iter.into_iter().map(eval_node).collect(),
        }
    }
}

impl<'a> FromIterator<Node<ValueExpr<'a>>> for Ast<'a> {
    fn from_iter<T: IntoIterator<Item = Node<ValueExpr<'a>>>>(iter: T) -> Self {
        Self {
            nodes: iter.into_iter().collect(),
        }
    }
}
