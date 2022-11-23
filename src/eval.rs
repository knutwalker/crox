use crate::{
    BinaryOp, CroxErrorKind, Expr, ExprNode, Literal, Node, Result, Type, TypeSet, UnaryOp,
};
use std::{cmp::Ordering, fmt, rc::Rc};

#[derive(Clone, Debug, Default, PartialEq)]
pub enum Value {
    #[default]
    Nil,
    Bool(bool),
    Number(f64),
    Str(Rc<str>),
}

pub fn evaluator<'a, I>(tokens: I) -> impl Iterator<Item = Result<Node<ValueExpr<'a>>>>
where
    I: IntoIterator<Item = ExprNode<'a>>,
{
    tokens.into_iter().map(eval_node)
}

pub fn eval_node(node: ExprNode<'_>) -> Result<Node<ValueExpr<'_>>> {
    let value = eval(&node.item)?;
    Ok(Node::new(
        ValueExpr {
            expr: *node.item,
            value,
        },
        node.span,
    ))
}

pub fn eval(expr: &Expr<'_>) -> Result<Value> {
    match expr {
        Expr::Literal(literal) => Ok(Value::from(literal)),
        Expr::Unary(op, node) => {
            let value = eval(&node.item)?;
            match op {
                UnaryOp::Neg => value.neg().map_err(|e| e.at(node.span)),
                UnaryOp::Not => Ok(value.not()),
            }
        }
        Expr::Binary(lhs_node, op, rhs_node) => {
            let lhs = eval(&lhs_node.item)?;
            let rhs = eval(&rhs_node.item)?;
            let to_error = |e: Result<CroxErrorKind, CroxErrorKind>| match e {
                Ok(e) => e.at(lhs_node.span),
                Err(e) => e.at(rhs_node.span),
            };
            match op {
                BinaryOp::Equals => Ok(lhs.eq(&rhs)),
                BinaryOp::NotEquals => Ok(lhs.not_eq(&rhs)),
                BinaryOp::LessThan => Ok(lhs.lt(&rhs)),
                BinaryOp::LessThanOrEqual => Ok(lhs.lte(&rhs)),
                BinaryOp::GreaterThan => Ok(lhs.gt(&rhs)),
                BinaryOp::GreaterThanOrEqual => Ok(lhs.gte(&rhs)),
                BinaryOp::Add => lhs.add(&rhs).map_err(to_error),
                BinaryOp::Sub => lhs.sub(&rhs).map_err(to_error),
                BinaryOp::Mul => lhs.mul(&rhs).map_err(to_error),
                BinaryOp::Div => lhs.div(&rhs).map_err(to_error),
            }
        }
        Expr::Group(inner) => eval(&inner.item),
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ValueExpr<'a> {
    pub expr: Expr<'a>,
    pub value: Value,
}

impl Value {
    fn as_num(&self) -> Result<f64, CroxErrorKind> {
        match self {
            Self::Number(n) => Ok(*n),
            otherwise => Err(CroxErrorKind::InvalidType {
                expected: TypeSet::from(Type::Number),
                actual: otherwise.typ(),
            }),
        }
    }

    fn as_str(&self) -> Result<&str, CroxErrorKind> {
        match self {
            Self::Str(s) => Ok(s),
            otherwise => Err(CroxErrorKind::InvalidType {
                expected: TypeSet::from(Type::String),
                actual: otherwise.typ(),
            }),
        }
    }

    fn as_bool(&self) -> bool {
        match self {
            Self::Bool(b) => *b,
            Self::Nil => false,
            _ => true,
        }
    }

    fn neg(&self) -> Result<Self, CroxErrorKind> {
        let num = self.as_num()?;
        Ok((-num).into())
    }

    fn not(&self) -> Self {
        let b = self.as_bool();
        (!b).into()
    }

    fn add(&self, rhs: &Self) -> Result<Self, Result<CroxErrorKind, CroxErrorKind>> {
        match self {
            Self::Number(lhs) => {
                let rhs = rhs.as_num().map_err(Err)?;
                Ok((*lhs + rhs).into())
            }
            Self::Str(lhs) => {
                let rhs = rhs.as_str().map_err(Err)?;
                Ok(format!("{}{}", lhs, rhs).into())
            }
            otherwise => Err(Ok(CroxErrorKind::InvalidType {
                expected: TypeSet::from_iter([Type::Number, Type::String]),
                actual: otherwise.typ(),
            })),
        }
    }

    fn sub(&self, rhs: &Self) -> Result<Self, Result<CroxErrorKind, CroxErrorKind>> {
        Self::num_op(self, rhs, |lhs, rhs| lhs - rhs)
    }

    fn mul(&self, rhs: &Self) -> Result<Self, Result<CroxErrorKind, CroxErrorKind>> {
        Self::num_op(self, rhs, |lhs, rhs| lhs * rhs)
    }

    fn div(&self, rhs: &Self) -> Result<Self, Result<CroxErrorKind, CroxErrorKind>> {
        Self::num_op(self, rhs, |lhs, rhs| lhs / rhs)
    }

    fn eq(&self, other: &Self) -> Self {
        self.partial_cmp(other)
            .map_or(false, |ord| ord == Ordering::Equal)
            .into()
    }

    fn not_eq(&self, other: &Self) -> Self {
        self.partial_cmp(other)
            .map_or(false, |ord| ord != Ordering::Equal)
            .into()
    }

    fn lt(&self, other: &Self) -> Self {
        self.partial_cmp(other)
            .map_or(false, |ord| ord == Ordering::Less)
            .into()
    }

    fn gt(&self, other: &Self) -> Self {
        self.partial_cmp(other)
            .map_or(false, |ord| ord == Ordering::Greater)
            .into()
    }

    fn lte(&self, other: &Self) -> Self {
        self.partial_cmp(other)
            .map_or(false, |ord| ord != Ordering::Greater)
            .into()
    }

    fn gte(&self, other: &Self) -> Self {
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
            Value::Bool(b) => b.fmt(f),
            Value::Number(n) => n.fmt(f),
            Value::Str(s) => s.fmt(f),
        }
    }
}
