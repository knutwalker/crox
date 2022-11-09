use crate::Span;
use std::fmt::Debug;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Node {
    pub idx: Idx,
    pub span: Span,
}

impl Node {
    pub fn new(idx: Idx, span: Span) -> Self {
        Self { idx, span }
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[repr(transparent)]
pub struct Idx(pub usize);

impl Idx {
    pub fn into_node(self, range: impl Into<Span>) -> Node {
        Node::new(self, range.into())
    }
}

pub trait Resolve<'a, R> {
    fn resolve(&self, idx: Idx) -> R;
}
