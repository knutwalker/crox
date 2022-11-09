use crate::{
    Expr, ExprNode, Idx, Literal, Resolve, Result, TypedAst, UnaryOp, ValuedAst, ValuedAstBuilder,
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

pub fn eval_ast(ast: TypedAst<'_>) -> ValuedAst<'_> {
    let mut builder = ValuedAstBuilder::new(ast);
    let (nodes, mut adder) = builder.split();
    for node in nodes {
        let value = eval(&adder, node).unwrap();
        adder.add(value);
    }
    builder.build()
}

pub fn eval_expr<'a, R: Resolve<'a, ExprNode<'a>> + ?Sized>(
    resolver: &R,
    expr: Expr,
) -> Result<ValueExpr> {
    struct ExprResolver<'x, R: ?Sized>(&'x R);

    impl<'a, 'x, R: Resolve<'a, ExprNode<'a>> + ?Sized> Resolve<'a, Result<Value>>
        for ExprResolver<'x, R>
    {
        fn resolve(&self, idx: Idx) -> Result<Value> {
            let node = self.0.resolve(idx);
            eval(self, &node)
        }
    }

    let node = resolver.resolve(expr.idx);
    let value = eval(&ExprResolver(resolver), &node)?;

    Ok(ValueExpr { expr, value })
}

pub fn eval<'a, R: Resolve<'a, Result<Value>> + ?Sized>(
    resolver: &R,
    node: &ExprNode<'a>,
) -> Result<Value> {
    Ok(match node {
        ExprNode::Literal(literal) => Value::from(literal),
        ExprNode::Unary(op, expr) => {
            let value = resolver.resolve(expr.idx)?;
            match op {
                UnaryOp::Neg => value.neg(),
                UnaryOp::Not => value.not(),
            }
        }
        ExprNode::Binary(lhs_expr, op, rhs_expr) => {
            let lhs = resolver.resolve(lhs_expr.idx)?;
            let rhs = resolver.resolve(rhs_expr.idx)?;
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
        ExprNode::Group(inner) => resolver.resolve(inner.idx)?,
    })
}

#[derive(Clone, Debug, PartialEq)]
pub struct ValueExpr {
    pub expr: Expr,
    pub value: Value,
}

impl Value {
    fn as_num(&self) -> f64 {
        let Value::Number(num) = self else {
            panic!("expected number, got {:?}", self);
        };
        *num
    }

    fn as_str(&self) -> Rc<str> {
        let Value::Str(s) = self else {
            panic!("expected string, got {:?}", self);
        };
        Rc::clone(s)
    }

    fn as_bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Nil => false,
            _ => true,
        }
    }

    fn neg(&self) -> Value {
        let num = self.as_num();
        Value::Number(-num)
    }

    fn not(&self) -> Value {
        let b = self.as_bool();
        Value::Bool(!b)
    }

    fn add(&self, rhs: &Self) -> Value {
        match self {
            Value::Number(lhs) => {
                let rhs = rhs.as_num();
                Value::Number(*lhs + rhs)
            }
            Value::Str(lhs) => {
                let rhs = rhs.as_str();
                Value::Str(Rc::from(format!("{}{}", lhs, rhs)))
            }
            _ => panic!("Unexpected types: lhs={:?}, rhs={:?}", self, rhs),
        }
    }

    fn sub(&self, rhs: &Self) -> Value {
        Self::num_op(self, rhs, |lhs, rhs| lhs - rhs)
    }

    fn mul(&self, rhs: &Self) -> Value {
        Self::num_op(self, rhs, |lhs, rhs| lhs * rhs)
    }

    fn div(&self, rhs: &Self) -> Value {
        Self::num_op(self, rhs, |lhs, rhs| lhs / rhs)
    }

    fn eq(&self, other: &Self) -> Value {
        Value::Bool(self.cmp(other).map_or(false, |ord| ord == Ordering::Equal))
    }

    fn not_eq(&self, other: &Self) -> Value {
        Value::Bool(self.cmp(other).map_or(false, |ord| ord != Ordering::Equal))
    }

    fn lt(&self, other: &Self) -> Value {
        Value::Bool(self.cmp(other).map_or(false, |ord| ord == Ordering::Less))
    }

    fn gt(&self, other: &Self) -> Value {
        Value::Bool(
            self.cmp(other)
                .map_or(false, |ord| ord == Ordering::Greater),
        )
    }

    fn lte(&self, other: &Self) -> Value {
        Value::Bool(
            self.cmp(other)
                .map_or(false, |ord| ord != Ordering::Greater),
        )
    }

    fn gte(&self, other: &Self) -> Value {
        Value::Bool(self.cmp(other).map_or(false, |ord| ord != Ordering::Less))
    }

    fn num_op(lhs: &Self, rhs: &Self, num_op: impl FnOnce(f64, f64) -> f64) -> Value {
        let lhs = lhs.as_num();
        let rhs = rhs.as_num();
        Value::Number(num_op(lhs, rhs))
    }

    fn cmp(&self, other: &Self) -> Option<Ordering> {
        match (&self, &other) {
            (Value::Number(n), Value::Number(o)) => n.partial_cmp(o),
            (Value::Str(s), Value::Str(o)) => s.partial_cmp(o),
            (Value::Bool(b), Value::Bool(o)) => b.partial_cmp(o),
            (Value::Nil, Value::Nil) => Some(Ordering::Equal),
            _ => None,
        }
    }
}
