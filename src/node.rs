use crate::{Bump, Span};
use std::fmt::Debug;

pub type Ident<'a> = Node<&'a str>;

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Node<T> {
    pub item: T,
    pub span: Span,
}

impl<T> Node<T> {
    fn new(item: T, span: impl Into<Span>) -> Self {
        Self {
            item,
            span: span.into(),
        }
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Node<U> {
        Node::new(f(self.item), self.span)
    }

    pub fn alloc(self, arena: &Bump) -> Node<&'_ T> {
        let item = arena.alloc(self.item);
        Node::new(item, self.span)
    }
}

pub trait Spannable: Sized {
    fn at(self, span: impl Into<Span>) -> Node<Self> {
        Node::new(self, span)
    }
}

impl<T> Spannable for T {}

impl<T: Debug> Debug for Node<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.item, f)?;
        f.write_str(" @ ")?;
        Debug::fmt(&self.span, f)
    }
}
