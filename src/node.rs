use crate::Span;
use std::fmt::Debug;

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Node<T> {
    pub item: T,
    pub span: Span,
}

impl<T> Node<T> {
    pub fn new(item: T, span: impl Into<Span>) -> Self {
        Self {
            item,
            span: span.into(),
        }
    }
}

impl<T: Debug> Debug for Node<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.item, f)?;
        f.write_str(" @ ")?;
        Debug::fmt(&self.span, f)
    }
}
