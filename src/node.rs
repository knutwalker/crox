use crate::Span;
use std::fmt::Debug;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    pub idx: Idx,
    pub span: Span,
}

impl Expr {
    pub fn new(idx: Idx, span: Span) -> Self {
        Self { idx, span }
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[repr(transparent)]
pub struct Idx(pub usize);

impl Idx {
    pub fn into_expr(self, range: impl Into<Span>) -> Expr {
        Expr::new(self, range.into())
    }
}

pub trait Resolve<'a, R> {
    fn resolve(&self, idx: Idx) -> R;
}
