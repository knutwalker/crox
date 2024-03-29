use crate::{
    Builtins, Bump, Callable, Class, CroxError, CroxErrorKind, Function, Instance,
    InterpreterContext, Literal, Node, Range, Result, Slotted, Span, Timings, Type, TypeSet,
};

use std::{cmp::Ordering, fmt, ops::Deref, rc::Rc};

#[derive(Clone, Debug, Default)]
pub enum Value<'env> {
    #[default]
    Nil,
    Bool(bool),
    Number(f64),
    Str(&'env str),
    Fn(&'env Function<'env>),
    Method(Rc<Function<'env>>),
    Instance(Rc<Instance<'env>>),
    Class(&'env Class<'env>),
    Builtin(Builtins),
}

impl<'env> Value<'env> {
    pub fn get(
        &self,
        ctx: &mut InterpreterContext<'env, '_>,
        name: &Node<&'env str>,
        slot: &'env Slotted,
        caller: Span,
    ) -> Result<Value<'env>> {
        match self {
            Self::Instance(instance) => instance
                .lookup(name.item, slot)
                .into_value(ctx, instance, name, caller),
            Self::Class(class) => class
                .class_method_lookup(name.item, slot)
                .map(Self::Fn)
                .ok_or_else(|| self.invalid_type(caller, Type::Instance)),
            _ => Err(self.invalid_type(caller, Type::Instance)),
        }
    }

    pub fn set(&self, name: &'env str, value: Value<'env>, caller: Span) -> Result<()> {
        match self {
            Self::Instance(instance) => {
                instance.insert(name, value);
                Ok(())
            }
            _ => Err(self.invalid_type(caller, Type::Instance)),
        }
    }

    pub fn as_callable(self, span: Span) -> Result<Callable<'env>> {
        match self {
            Self::Fn(fun) => Ok(Callable::Fn(fun)),
            Self::Method(fun) => Ok(Callable::Method(fun)),
            Self::Class(class) => Ok(Callable::Class(class)),
            Self::Builtin(builtins) => Ok(Callable::Builtin(builtins)),
            _ => Err(self.invalid_type(span, Type::Callable)),
        }
    }

    pub fn as_num(&self, span: impl Into<Range>) -> Result<f64> {
        match self {
            Self::Number(n) => Ok(*n),
            _ => Err(self.invalid_type(span, Type::Number)),
        }
    }

    pub fn as_bool(&self) -> bool {
        match self {
            Self::Bool(b) => *b,
            Self::Nil => false,
            _ => true,
        }
    }

    pub fn neg(&self, span: impl Into<Range>) -> Result<Self> {
        let num = self.as_num(span)?;
        Ok((-num).into())
    }

    pub fn not(&self) -> Self {
        let b = self.as_bool();
        (!b).into()
    }

    pub fn add(
        &self,
        rhs: &Node<Self>,
        left: impl Into<Range>,
        arena: Option<&'env Bump>,
    ) -> Result<Self> {
        let right = rhs.span;
        match (self, &rhs.item) {
            (lhs, rhs @ Self::Str(_)) | (lhs @ Self::Str(_), rhs) => {
                let value = format!("{lhs}{rhs}");
                let value = match arena {
                    Some(arena) => arena.alloc(value),
                    None => Box::leak(Box::new(value)),
                };
                Ok(Value::from(value.as_str()))
            }
            (Self::Number(lhs), rhs) => {
                let rhs = rhs.as_num(right)?;
                Ok((lhs + rhs).into())
            }
            (lhs, Self::Number(rhs)) => {
                let lhs = lhs.as_num(left)?;
                Ok((lhs + rhs).into())
            }
            _ => Err(self.invalid_type(left, [Type::Number, Type::String])),
        }
    }

    pub fn sub(&self, rhs: &Node<Self>, left: impl Into<Range>) -> Result<Self> {
        Self::num_op(self, rhs, left, |lhs, rhs| lhs - rhs)
    }

    pub fn mul(&self, rhs: &Node<Self>, left: impl Into<Range>) -> Result<Self> {
        Self::num_op(self, rhs, left, |lhs, rhs| lhs * rhs)
    }

    pub fn div(&self, rhs: &Node<Self>, left: impl Into<Range>) -> Result<Self> {
        Self::num_op(self, rhs, left, |lhs, rhs| lhs / rhs)
    }

    pub fn eq(&self, other: &Self) -> Self {
        (self == other).into()
    }

    pub fn not_eq(&self, other: &Self) -> Self {
        (self != other).into()
    }

    pub fn lt(&self, other: &Node<Self>) -> Result<Self> {
        self.partial_cmp(&other.item)
            .map(|ord| Self::from(ord == Ordering::Less))
            .ok_or_else(|| other.item.invalid_type(other.span, self.typ()))
    }

    pub fn gt(&self, other: &Node<Self>) -> Result<Self> {
        self.partial_cmp(&other.item)
            .map(|ord| Self::from(ord == Ordering::Greater))
            .ok_or_else(|| other.item.invalid_type(other.span, self.typ()))
    }

    pub fn lte(&self, other: &Node<Self>) -> Result<Self> {
        self.partial_cmp(&other.item)
            .map(|ord| Self::from(ord != Ordering::Greater))
            .ok_or_else(|| other.item.invalid_type(other.span, self.typ()))
    }

    pub fn gte(&self, other: &Node<Self>) -> Result<Self> {
        self.partial_cmp(&other.item)
            .map(|ord| Self::from(ord != Ordering::Less))
            .ok_or_else(|| other.item.invalid_type(other.span, self.typ()))
    }

    fn num_op(
        lhs: &Self,
        rhs: &Node<Self>,
        left: impl Into<Range>,
        num_op: impl FnOnce(f64, f64) -> f64,
    ) -> Result<Self> {
        let lhs = lhs.as_num(left)?;
        let rhs = rhs.item.as_num(rhs.span)?;
        Ok(num_op(lhs, rhs).into())
    }

    fn invalid_type(&self, span: impl Into<Range>, expected: impl Into<TypeSet>) -> CroxError {
        CroxErrorKind::InvalidType {
            expected: expected.into(),
            actual: self.typ(),
        }
        .at(span)
        .with_payload(format!("{self:?}"))
    }
}

pub type Valued<'env> = Node<Value<'env>>;

#[derive(Clone, Debug, PartialEq)]
pub struct Ast<'env> {
    values: Vec<Valued<'env>>,
    pub timings: Timings,
}

impl<'env> Ast<'env> {
    pub fn new(values: Vec<Valued<'env>>, timings: Timings) -> Self {
        Self { values, timings }
    }
}

impl<'env> Deref for Ast<'env> {
    type Target = [Valued<'env>];

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
            (Self::Builtin(lhs), Self::Builtin(rhs)) => lhs == rhs,
            (Self::Method(lhs), Self::Method(rhs)) => {
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
            (Self::Builtin(_), Self::Builtin(_)) if self == other => Some(Ordering::Equal),
            (Self::Fn(_), Self::Fn(_)) if self == other => Some(Ordering::Equal),
            (Self::Method(_), Self::Method(_)) if self == other => Some(Ordering::Equal),
            (Self::Class(_), Self::Class(_)) if self == other => Some(Ordering::Equal),
            _ => None,
        }
    }
}

impl<'env> From<Literal<'env>> for Value<'env> {
    fn from(literal: Literal<'env>) -> Self {
        Value::from(&literal)
    }
}

impl<'env> From<&Literal<'env>> for Value<'env> {
    fn from(literal: &Literal<'env>) -> Self {
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

impl<'env> From<&'env str> for Value<'env> {
    fn from(s: &'env str) -> Self {
        Self::Str(s)
    }
}

impl<'env> From<&'env Function<'env>> for Value<'env> {
    fn from(value: &'env Function<'env>) -> Self {
        Self::Fn(value)
    }
}

impl<'env> From<Function<'env>> for Value<'env> {
    fn from(value: Function<'env>) -> Self {
        Self::Method(Rc::new(value))
    }
}

impl<'env> From<&'env Class<'env>> for Value<'env> {
    fn from(value: &'env Class<'env>) -> Self {
        Self::Class(value)
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
            Value::Method(fun) => fmt::Debug::fmt(fun, f),
            Value::Builtin(fun) => fmt::Debug::fmt(fun, f),
            Value::Instance(inst) => fmt::Debug::fmt(inst, f),
            Value::Class(inst) => fmt::Debug::fmt(inst, f),
        }
    }
}
