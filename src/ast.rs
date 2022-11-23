use crate::{Node, Valued};
use std::{fmt::Debug, ops::Deref};

#[derive(Clone, Debug, PartialEq)]
pub struct Ast<T> {
    nodes: Vec<Node<Valued<T>>>,
}

impl<T> Ast<T> {
    pub fn new(nodes: Vec<Node<Valued<T>>>) -> Self {
        Self { nodes }
    }
}

impl<T> Deref for Ast<T> {
    type Target = [Node<Valued<T>>];

    fn deref(&self) -> &Self::Target {
        &self.nodes
    }
}

impl<T> FromIterator<Node<Valued<T>>> for Ast<T> {
    fn from_iter<I: IntoIterator<Item = Node<Valued<T>>>>(iter: I) -> Self {
        Self {
            nodes: iter.into_iter().collect(),
        }
    }
}
