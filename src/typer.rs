use crate::{EnumSet, Literal, Value, ValueEnum};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Type {
    Bool,
    Number,
    String,
    Callable,
    Class,
    Instance,
    Nil,
}

impl Literal<'_> {
    pub fn typ(&self) -> Type {
        match self {
            Self::Nil => Type::Nil,
            Self::True | Self::False => Type::Bool,
            Self::Number(_) => Type::Number,
            Self::String(_) => Type::String,
        }
    }
}

impl Value<'_> {
    pub fn typ(&self) -> Type {
        match self {
            Self::Nil => Type::Nil,
            Self::Bool(_) => Type::Bool,
            Self::Number(_) => Type::Number,
            Self::Str(_) => Type::String,
            Self::Fn(_) | Self::Method(_) | Self::Builtin(_) => Type::Callable,
            Self::Instance(_) => Type::Instance,
            Self::Class(_) => Type::Class,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Typed<T> {
    pub item: T,
    pub typ: Type,
}

impl ValueEnum for Type {
    fn to_ord(&self) -> u8 {
        *self as u8
    }

    unsafe fn from_ord(ord: u8) -> Self {
        std::mem::transmute_copy(&ord)
    }
}

pub type TypeSet = EnumSet<Type>;
