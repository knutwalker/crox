use crate::{Callable, CroxErrorKind, Literal, Type, TypeSet};

use std::{borrow::Cow, cmp::Ordering, fmt, ops::Deref, rc::Rc};

#[derive(Clone, Debug, Default)]
pub enum Value<'a> {
    #[default]
    Nil,
    Bool(bool),
    Number(f64),
    Str(Cow<'a, str>),
    Fn(Rc<dyn Callable<'a>>),
}

impl Value<'_> {
    pub fn as_num(&self) -> Result<f64, CroxErrorKind> {
        match self {
            Self::Number(n) => Ok(*n),
            otherwise => Err(CroxErrorKind::InvalidType {
                expected: TypeSet::from(Type::Number),
                actual: otherwise.typ(),
            }),
        }
    }

    pub fn as_bool(&self) -> bool {
        match self {
            Self::Bool(b) => *b,
            Self::Nil => false,
            _ => true,
        }
    }

    pub fn neg(&self) -> Result<Self, CroxErrorKind> {
        let num = self.as_num()?;
        Ok((-num).into())
    }

    pub fn not(&self) -> Self {
        let b = self.as_bool();
        (!b).into()
    }

    pub fn add(&self, rhs: &Self) -> Result<Self, Result<CroxErrorKind, CroxErrorKind>> {
        match (self, rhs) {
            (lhs, rhs @ Self::Str(_)) | (lhs @ Self::Str(_), rhs) => {
                Ok(format!("{lhs}{rhs}").into())
            }
            (Self::Number(lhs), rhs) => {
                let rhs = rhs.as_num().map_err(Err)?;
                Ok((lhs + rhs).into())
            }
            (lhs, Self::Number(rhs)) => {
                let lhs = lhs.as_num().map_err(Ok)?;
                Ok((lhs + rhs).into())
            }
            (lhs, _) => Err(Ok(CroxErrorKind::InvalidType {
                expected: TypeSet::from_iter([Type::Number, Type::String]),
                actual: lhs.typ(),
            })),
        }
    }

    pub fn sub(&self, rhs: &Self) -> Result<Self, Result<CroxErrorKind, CroxErrorKind>> {
        Self::num_op(self, rhs, |lhs, rhs| lhs - rhs)
    }

    pub fn mul(&self, rhs: &Self) -> Result<Self, Result<CroxErrorKind, CroxErrorKind>> {
        Self::num_op(self, rhs, |lhs, rhs| lhs * rhs)
    }

    pub fn div(&self, rhs: &Self) -> Result<Self, Result<CroxErrorKind, CroxErrorKind>> {
        Self::num_op(self, rhs, |lhs, rhs| lhs / rhs)
    }

    pub fn eq(&self, other: &Self) -> Self {
        self.partial_cmp(other)
            .map_or(false, |ord| ord == Ordering::Equal)
            .into()
    }

    pub fn not_eq(&self, other: &Self) -> Self {
        self.partial_cmp(other)
            .map_or(false, |ord| ord != Ordering::Equal)
            .into()
    }

    pub fn lt(&self, other: &Self) -> Self {
        self.partial_cmp(other)
            .map_or(false, |ord| ord == Ordering::Less)
            .into()
    }

    pub fn gt(&self, other: &Self) -> Self {
        self.partial_cmp(other)
            .map_or(false, |ord| ord == Ordering::Greater)
            .into()
    }

    pub fn lte(&self, other: &Self) -> Self {
        self.partial_cmp(other)
            .map_or(false, |ord| ord != Ordering::Greater)
            .into()
    }

    pub fn gte(&self, other: &Self) -> Self {
        self.partial_cmp(other)
            .map_or(false, |ord| ord != Ordering::Less)
            .into()
    }

    fn num_op(
        lhs: &Self,
        rhs: &Self,
        num_op: impl FnOnce(f64, f64) -> f64,
    ) -> Result<Self, Result<CroxErrorKind, CroxErrorKind>> {
        let lhs = lhs.as_num().map_err(Ok)?;
        let rhs = rhs.as_num().map_err(Err)?;
        Ok(num_op(lhs, rhs).into())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Valued<'a, T> {
    pub item: T,
    pub value: Value<'a>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Ast<'a, T> {
    values: Vec<Valued<'a, T>>,
}

impl<'a, T> Ast<'a, T> {
    pub fn new(values: Vec<Valued<'a, T>>) -> Self {
        Self { values }
    }
}

impl<'a, T> Deref for Ast<'a, T> {
    type Target = [Valued<'a, T>];

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

impl<'a, T> FromIterator<Valued<'a, T>> for Ast<'a, T> {
    fn from_iter<I: IntoIterator<Item = Valued<'a, T>>>(iter: I) -> Self {
        Self {
            values: iter.into_iter().collect(),
        }
    }
}

impl PartialEq for Value<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Nil, Self::Nil) => true,
            (Self::Bool(lhs), Self::Bool(rhs)) => lhs == rhs,
            (Self::Number(lhs), Self::Number(rhs)) => lhs == rhs,
            (Self::Str(lhs), Self::Str(rhs)) => lhs == rhs,
            (Self::Fn(_), Self::Fn(_)) => false,
            _ => false,
        }
    }
}

impl PartialOrd for Value<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (&self, &other) {
            (Self::Number(n), Self::Number(o)) => n.partial_cmp(o),
            (Self::Str(s), Self::Str(o)) => s.partial_cmp(o),
            (Self::Bool(b), Self::Bool(o)) => b.partial_cmp(o),
            (Self::Nil, Self::Nil) => Some(Ordering::Equal),
            _ => None,
        }
    }
}

impl<'a> From<Literal<'a>> for Value<'a> {
    fn from(literal: Literal<'a>) -> Self {
        match literal {
            Literal::Nil => Value::Nil,
            Literal::True => Value::Bool(true),
            Literal::False => Value::Bool(false),
            Literal::Number(num) => Value::Number(num),
            Literal::String(s) => Value::from(s),
        }
    }
}

impl<'a> From<&Literal<'a>> for Value<'a> {
    fn from(literal: &Literal<'a>) -> Self {
        match literal {
            Literal::Nil => Value::Nil,
            Literal::True => Value::Bool(true),
            Literal::False => Value::Bool(false),
            Literal::Number(num) => Value::Number(*num),
            Literal::String(s) => Value::from(*s),
        }
    }
}

impl From<f64> for Value<'_> {
    fn from(num: f64) -> Self {
        Self::Number(num)
    }
}

impl From<bool> for Value<'_> {
    fn from(b: bool) -> Self {
        Self::Bool(b)
    }
}

impl<'a> From<&'a str> for Value<'a> {
    fn from(s: &'a str) -> Self {
        Self::Str(s.into())
    }
}

impl From<String> for Value<'_> {
    fn from(s: String) -> Self {
        Self::Str(s.into())
    }
}

impl fmt::Display for Value<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Nil => f.write_str("nil"),
            Value::Bool(b) => fmt::Display::fmt(b, f),
            Value::Number(n) => fmt::Display::fmt(n, f),
            Value::Str(s) => fmt::Display::fmt(s, f),
            Value::Fn(fun) => fmt::Debug::fmt(fun, f),
        }
    }
}
