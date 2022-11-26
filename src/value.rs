use crate::Literal;

use std::{cmp::Ordering, fmt, ops::Deref, rc::Rc};

#[derive(Clone, Debug, Default, PartialEq)]
pub enum Value {
    #[default]
    Nil,
    Bool(bool),
    Number(f64),
    Str(Rc<str>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Valued<T> {
    pub item: T,
    pub value: Value,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Ast<T> {
    values: Vec<Valued<T>>,
}

impl<T> Ast<T> {
    pub fn new(values: Vec<Valued<T>>) -> Self {
        Self { values }
    }
}

impl<T> Deref for Ast<T> {
    type Target = [Valued<T>];

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

impl<T> FromIterator<Valued<T>> for Ast<T> {
    fn from_iter<I: IntoIterator<Item = Valued<T>>>(iter: I) -> Self {
        Self {
            values: iter.into_iter().collect(),
        }
    }
}

impl PartialOrd for Value {
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

impl From<Literal<'_>> for Value {
    fn from(literal: Literal) -> Self {
        match literal {
            Literal::Nil => Value::Nil,
            Literal::True => Value::Bool(true),
            Literal::False => Value::Bool(false),
            Literal::Number(num) => Value::Number(num),
            Literal::String(s) => Value::Str(s.into()),
        }
    }
}

impl From<&Literal<'_>> for Value {
    fn from(literal: &Literal) -> Self {
        match literal {
            Literal::Nil => Value::Nil,
            Literal::True => Value::Bool(true),
            Literal::False => Value::Bool(false),
            Literal::Number(num) => Value::Number(*num),
            Literal::String(s) => Value::Str((*s).into()),
        }
    }
}

impl From<f64> for Value {
    fn from(num: f64) -> Self {
        Self::Number(num)
    }
}

impl From<bool> for Value {
    fn from(b: bool) -> Self {
        Self::Bool(b)
    }
}

impl From<&str> for Value {
    fn from(s: &str) -> Self {
        Self::Str(s.into())
    }
}

impl From<String> for Value {
    fn from(s: String) -> Self {
        Self::Str(s.into())
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Nil => f.write_str("nil"),
            Value::Bool(b) => fmt::Display::fmt(b, f),
            Value::Number(n) => fmt::Display::fmt(n, f),
            Value::Str(s) => fmt::Display::fmt(s, f),
        }
    }
}
