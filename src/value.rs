use crate::{
    Bump, Callable, Class, CroxError, CroxErrorKind, Function, Instance, InterpreterContext,
    Literal, Node, Result, Span, Timings, Type, TypeSet,
};

use std::{cmp::Ordering, fmt, ops::Deref, rc::Rc};

#[derive(Clone, Debug, Default)]
pub enum Value<'a> {
    #[default]
    Nil,
    Bool(bool),
    Number(f64),
    Str(&'a str),
    Fn(&'a Function<'a>),
    Instance(&'a Instance<'a>),
    Class(Rc<Class<'a>>),
    Callable(Rc<dyn Callable<'a>>),
}

type BinOpResult<'a> = Result<Value<'a>, Result<CroxErrorKind, CroxErrorKind>>;

impl<'env> Value<'env> {
    pub fn get(
        &self,
        ctx: &mut InterpreterContext<'env, '_>,
        name: &Node<&'env str>,
        caller: Span,
    ) -> Result<Value<'env>> {
        match self {
            Value::Instance(instance) => instance
                .lookup(name.item)
                .into_value(ctx, instance, name, caller),
            Value::Class(class) => class
                .class_method_lookup(name.item)
                .map(Value::Fn)
                .ok_or_else(|| self.invalid_type(caller, Type::Instance)),
            _ => Err(self.invalid_type(caller, Type::Instance)),
        }
    }

    pub fn set(
        &self,
        name: &'env str,
        value: impl FnOnce() -> Value<'env>,
        caller: Span,
    ) -> Result<()> {
        match self {
            Value::Instance(instance) => {
                instance.insert(name, value());
                Ok(())
            }
            _ => Err(self.invalid_type(caller, Type::Instance)),
        }
    }

    pub fn as_callable(&self, span: Span) -> Result<&dyn Callable<'env>> {
        match self {
            Value::Fn(fun) => Ok(&**fun),
            Value::Callable(fun) => Ok(&**fun),
            Value::Class(class) => Ok(&**class),
            _ => Err(CroxErrorKind::InvalidType {
                expected: TypeSet::from(Type::Callable),
                actual: self.typ(),
            }
            .at(span)
            .with_payload(format!("{self:?}"))),
        }
    }

    pub fn as_num(&self) -> Result<f64, CroxErrorKind> {
        match self {
            Self::Number(n) => Ok(*n),
            otherwise => Err(CroxErrorKind::InvalidType {
                expected: TypeSet::from(Type::Number),
                actual: otherwise.typ(),
            }),
        }
    }

    fn invalid_type(&self, span: Span, expected: impl Into<TypeSet>) -> CroxError {
        CroxErrorKind::InvalidType {
            expected: expected.into(),
            actual: self.typ(),
        }
        .at(span)
        .with_payload(format!("{self:?}"))
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

    pub fn add(&self, rhs: &Self, arena: Option<&'env Bump>) -> BinOpResult<'env> {
        match (self, rhs) {
            (lhs, rhs @ Self::Str(_)) | (lhs @ Self::Str(_), rhs) => {
                let value = format!("{lhs}{rhs}");
                let value = match arena {
                    Some(arena) => arena.alloc(value),
                    None => Box::leak(Box::new(value)),
                };
                Ok(Value::from(value.as_str()))
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

    pub fn sub(&self, rhs: &Self) -> BinOpResult<'env> {
        Self::num_op(self, rhs, |lhs, rhs| lhs - rhs)
    }

    pub fn mul(&self, rhs: &Self) -> BinOpResult<'env> {
        Self::num_op(self, rhs, |lhs, rhs| lhs * rhs)
    }

    pub fn div(&self, rhs: &Self) -> BinOpResult<'env> {
        Self::num_op(self, rhs, |lhs, rhs| lhs / rhs)
    }

    pub fn eq(&self, other: &Self) -> Self {
        (self == other).into()
    }

    pub fn not_eq(&self, other: &Self) -> Self {
        (self != other).into()
    }

    pub fn lt(&self, other: &Self) -> BinOpResult<'env> {
        self.partial_cmp(other)
            .map(|ord| Self::from(ord == Ordering::Less))
            .ok_or_else(|| {
                Err(CroxErrorKind::InvalidType {
                    expected: self.typ().into(),
                    actual: other.typ(),
                })
            })
    }

    pub fn gt(&self, other: &Self) -> BinOpResult<'env> {
        self.partial_cmp(other)
            .map(|ord| Self::from(ord == Ordering::Greater))
            .ok_or_else(|| {
                Err(CroxErrorKind::InvalidType {
                    expected: self.typ().into(),
                    actual: other.typ(),
                })
            })
    }

    pub fn lte(&self, other: &Self) -> BinOpResult<'env> {
        self.partial_cmp(other)
            .map(|ord| Self::from(ord != Ordering::Greater))
            .ok_or_else(|| {
                Err(CroxErrorKind::InvalidType {
                    expected: self.typ().into(),
                    actual: other.typ(),
                })
            })
    }

    pub fn gte(&self, other: &Self) -> BinOpResult<'env> {
        self.partial_cmp(other)
            .map(|ord| Self::from(ord != Ordering::Less))
            .ok_or_else(|| {
                Err(CroxErrorKind::InvalidType {
                    expected: self.typ().into(),
                    actual: other.typ(),
                })
            })
    }

    fn num_op(lhs: &Self, rhs: &Self, num_op: impl FnOnce(f64, f64) -> f64) -> BinOpResult<'env> {
        let lhs = lhs.as_num().map_err(Ok)?;
        let rhs = rhs.as_num().map_err(Err)?;
        Ok(num_op(lhs, rhs).into())
    }
}

pub type Valued<'a> = Node<Value<'a>>;

#[derive(Clone, Debug, PartialEq)]
pub struct Ast<'a> {
    values: Vec<Valued<'a>>,
    pub timings: Timings,
}

impl<'a> Ast<'a> {
    pub fn new(values: Vec<Valued<'a>>, timings: Timings) -> Self {
        Self { values, timings }
    }
}

impl<'a> Deref for Ast<'a> {
    type Target = [Valued<'a>];

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

impl PartialEq for Value<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Nil, Self::Nil) => true,
            (Self::Bool(lhs), Self::Bool(rhs)) => lhs == rhs,
            (Self::Number(lhs), Self::Number(rhs)) => lhs == rhs,
            (Self::Str(lhs), Self::Str(rhs)) => lhs == rhs,
            (Self::Callable(lhs), Self::Callable(rhs)) => {
                let lhs = std::ptr::addr_of!(**lhs).cast::<()>();
                let rhs = std::ptr::addr_of!(**rhs).cast::<()>();
                std::ptr::eq(lhs, rhs)
            }
            (Self::Fn(lhs), Self::Fn(rhs)) => {
                let lhs = std::ptr::addr_of!(**lhs).cast::<()>();
                let rhs = std::ptr::addr_of!(**rhs).cast::<()>();
                std::ptr::eq(lhs, rhs)
            }
            (Self::Class(lhs), Self::Class(rhs)) => {
                let lhs = std::ptr::addr_of!(**lhs);
                let rhs = std::ptr::addr_of!(**rhs);
                std::ptr::eq(lhs, rhs)
            }
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
            (Self::Callable(_), Self::Callable(_)) if self == other => Some(Ordering::Equal),
            (Self::Fn(_), Self::Fn(_)) if self == other => Some(Ordering::Equal),
            (Self::Class(_), Self::Class(_)) if self == other => Some(Ordering::Equal),
            _ => None,
        }
    }
}

impl<'a> From<Literal<'a>> for Value<'a> {
    fn from(literal: Literal<'a>) -> Self {
        Value::from(&literal)
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
        Self::Str(s)
    }
}

impl<'a> From<&'a Function<'a>> for Value<'a> {
    fn from(value: &'a Function<'a>) -> Self {
        Self::Fn(value)
    }
}

impl<'a> From<Class<'a>> for Value<'a> {
    fn from(value: Class<'a>) -> Self {
        Self::Class(Rc::new(value))
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
            Value::Callable(fun) => fmt::Debug::fmt(fun, f),
            Value::Instance(inst) => fmt::Debug::fmt(inst, f),
            Value::Class(inst) => fmt::Debug::fmt(inst, f),
        }
    }
}
