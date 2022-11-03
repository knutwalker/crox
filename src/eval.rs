use crate::{CroxError, CroxErrorKind, EnumSet, Expr, Literal, Node, Resolve, UnaryOp, ValueEnum};
use std::{cmp::Ordering, fmt, sync::Arc};

pub fn eval<'a, R: Resolve<'a>>(resolver: &R, expr: Expr) -> Result<ValueExpr, CroxError> {
    let res = match resolver.resolve(&expr.idx) {
        Node::Literal(literal) => Ok(Value::from(literal)),
        Node::Unary(op, expr) => {
            let value = eval(resolver, expr)?;
            match op {
                UnaryOp::Neg => value.neg(),
                UnaryOp::Not => value.not(),
            }
        }
        Node::Binary(lhs_expr, op, rhs_expr) => {
            let lhs = eval(resolver, lhs_expr)?;
            let rhs = eval(resolver, rhs_expr)?;
            match op {
                crate::BinaryOp::Equals => lhs.eq(&rhs),
                crate::BinaryOp::NotEquals => lhs.not_eq(&rhs),
                crate::BinaryOp::LessThan => lhs.lt(&rhs),
                crate::BinaryOp::LessThanOrEqual => lhs.lte(&rhs),
                crate::BinaryOp::GreaterThan => lhs.gt(&rhs),
                crate::BinaryOp::GreaterThanOrEqual => lhs.gte(&rhs),
                crate::BinaryOp::Add => lhs.add(&rhs),
                crate::BinaryOp::Sub => lhs.sub(&rhs),
                crate::BinaryOp::Mul => lhs.mul(&rhs),
                crate::BinaryOp::Div => lhs.div(&rhs),
            }
        }
        Node::Group(inner) => return eval(resolver, inner),
    };
    res.map(|value| ValueExpr { expr, value })
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Type {
    Bool,
    Number,
    String,
    Function,
    Class,
    Nil,
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

#[derive(Clone, Debug, PartialEq)]
pub struct ValueExpr {
    pub expr: Expr,
    pub value: Value,
}

impl ValueExpr {
    fn as_num(&self) -> Result<f64, CroxError> {
        match &self.value {
            Value::Number(n) => Ok(*n),
            otherwise => Err(CroxError::new(
                CroxErrorKind::InvalidType {
                    expected: TypeSet::from(Type::Number),
                    actual: otherwise.typ(),
                },
                self.expr.span,
            )),
        }
    }

    fn as_str(&self) -> Result<Arc<str>, CroxError> {
        match &self.value {
            Value::Str(s) => Ok(Arc::clone(s)),
            otherwise => Err(CroxError::new(
                CroxErrorKind::InvalidType {
                    expected: TypeSet::from(Type::String),
                    actual: otherwise.typ(),
                },
                self.expr.span,
            )),
        }
    }

    fn as_bool(&self) -> Result<bool, CroxError> {
        match &self.value {
            Value::Bool(b) => Ok(*b),
            otherwise => Err(CroxError::new(
                CroxErrorKind::InvalidType {
                    expected: TypeSet::from(Type::Bool),
                    actual: otherwise.typ(),
                },
                self.expr.span,
            )),
        }
    }

    fn coerce_bool(&self) -> bool {
        match &self.value {
            Value::Bool(b) => *b,
            Value::Nil => false,
            _ => true,
        }
    }

    fn neg(&self) -> Result<Value, CroxError> {
        let num = self.as_num()?;
        Ok(Value::Number(-num))
    }

    fn not(&self) -> Result<Value, CroxError> {
        let b = self.coerce_bool();
        Ok(Value::Bool(!b))
    }

    fn add(&self, rhs: &Self) -> Result<Value, CroxError> {
        Self::op(
            self,
            rhs,
            |lhs, rhs| lhs + rhs,
            |lhs, rhs| Arc::from(format!("{}{}", lhs, rhs)),
        )
    }

    fn sub(&self, rhs: &Self) -> Result<Value, CroxError> {
        Self::num_op(self, rhs, |lhs, rhs| lhs - rhs)
    }

    fn mul(&self, rhs: &Self) -> Result<Value, CroxError> {
        Self::num_op(self, rhs, |lhs, rhs| lhs * rhs)
    }

    fn div(&self, rhs: &Self) -> Result<Value, CroxError> {
        Self::num_op(self, rhs, |lhs, rhs| lhs / rhs)
    }

    fn eq(&self, other: &Self) -> Result<Value, CroxError> {
        self.cmp(other)
            .map(|ord| Value::Bool(ord.map_or(false, |ord| ord == Ordering::Equal)))
    }

    fn not_eq(&self, other: &Self) -> Result<Value, CroxError> {
        self.cmp(other)
            .map(|ord| Value::Bool(ord.map_or(false, |ord| ord != Ordering::Equal)))
    }

    fn lt(&self, other: &Self) -> Result<Value, CroxError> {
        self.cmp(other)
            .map(|ord| Value::Bool(ord.map_or(false, |ord| ord == Ordering::Less)))
    }

    fn gt(&self, other: &Self) -> Result<Value, CroxError> {
        self.cmp(other)
            .map(|ord| Value::Bool(ord.map_or(false, |ord| ord == Ordering::Greater)))
    }

    fn lte(&self, other: &Self) -> Result<Value, CroxError> {
        self.cmp(other)
            .map(|ord| Value::Bool(ord.map_or(false, |ord| ord != Ordering::Greater)))
    }

    fn gte(&self, other: &Self) -> Result<Value, CroxError> {
        self.cmp(other)
            .map(|ord| Value::Bool(ord.map_or(false, |ord| ord != Ordering::Less)))
    }

    fn op(
        lhs: &Self,
        rhs: &Self,
        num_op: impl FnOnce(f64, f64) -> f64,
        str_op: impl FnOnce(Arc<str>, Arc<str>) -> Arc<str>,
    ) -> Result<Value, CroxError> {
        match &lhs.value {
            Value::Number(lhs) => {
                let rhs = rhs.as_num()?;
                Ok(Value::Number(num_op(*lhs, rhs)))
            }
            Value::Str(lhs) => {
                let rhs = rhs.as_str()?;
                Ok(Value::Str(str_op(Arc::clone(lhs), rhs)))
            }
            otherwise => Err(CroxError::new(
                CroxErrorKind::InvalidType {
                    expected: TypeSet::from_iter([Type::Number, Type::String]),
                    actual: otherwise.typ(),
                },
                lhs.expr.span,
            )),
        }
    }

    fn num_op(
        lhs: &Self,
        rhs: &Self,
        num_op: impl FnOnce(f64, f64) -> f64,
    ) -> Result<Value, CroxError> {
        let lhs = lhs.as_num()?;
        let rhs = rhs.as_num()?;
        Ok(Value::Number(num_op(lhs, rhs)))
    }

    fn cmp(&self, other: &Self) -> Result<Option<Ordering>, CroxError> {
        match (&self.value, &other.value) {
            (Value::Number(n), Value::Number(o)) => Ok(n.partial_cmp(o)),
            (Value::Str(s), Value::Str(o)) => Ok(s.partial_cmp(o)),
            (Value::Bool(b), Value::Bool(o)) => Ok(b.partial_cmp(o)),
            (Value::Nil, Value::Nil) => Ok(Some(Ordering::Equal)),
            _ => Ok(None),
            // (lhs, rhs) => Err(CroxError::new(
            //     CroxErrorKind::InvalidType {
            //         expected: TypeSet::from(lhs.typ()),
            //         actual: rhs.typ(),
            //     },
            //     self.expr.span,
            // )),
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq)]
pub enum Value {
    #[default]
    Nil,
    Bool(bool),
    Number(f64),
    Str(Arc<str>),
}

impl Value {
    pub fn typ(&self) -> Type {
        match self {
            Value::Nil => Type::Nil,
            Value::Bool(_) => Type::Bool,
            Value::Number(_) => Type::Number,
            Value::Str(_) => Type::String,
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

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Nil => f.write_str("nil"),
            Value::Bool(b) => b.fmt(f),
            Value::Number(n) => n.fmt(f),
            Value::Str(s) => s.fmt(f),
        }
    }
}
