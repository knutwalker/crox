use crate::{
    BinaryOp, CroxErrorKind, Environment, Expr, Literal, Node, Result, Span, Stmt, StmtNode, Type,
    TypeSet, UnaryOp,
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

#[derive(Clone, Debug, PartialEq)]
pub struct Valued<T> {
    pub item: T,
    pub value: Value,
}

pub type ValueExpr<'a> = Valued<Expr<'a>>;
pub type ValueStmt<'a> = Valued<Stmt<'a>>;

#[derive(Clone, Debug, Default)]
pub struct Evaluator<'a, I> {
    env: Environment<'a>,
    statements: I,
}

impl<'a, I> Evaluator<'a, I> {
    pub fn new(tokens: I) -> Self {
        Self {
            env: Environment::default(),
            statements: tokens,
        }
    }
}

impl<'a, I> Evaluator<'a, I>
where
    I: Iterator<Item = StmtNode<'a>>,
{
    pub fn eval_stmt(&mut self, stmt: StmtNode<'a>) -> Result<Node<ValueStmt<'a>>> {
        match &stmt.item {
            Stmt::Expression(expr) => {
                let _ = self.eval(&expr.item, expr.span)?;
            }
            Stmt::Print(expr) => {
                let val = self.eval(&expr.item, expr.span)?;
                println!("{}", val);
            }
            Stmt::Var(name, expr) => {
                let value = expr
                    .as_ref()
                    .map(|e| self.eval(&e.item, e.span))
                    .transpose()?
                    .unwrap_or_default();
                self.env.define(name, value);
            }
        }

        Ok(Node::new(
            ValueStmt {
                item: stmt.item,
                value: Value::Nil,
            },
            stmt.span,
        ))
    }

    pub fn eval(&self, expr: &Expr<'_>, span: Span) -> Result<Value> {
        match expr {
            Expr::Literal(literal) => Ok(Value::from(literal)),
            Expr::Var(name) => self
                .env
                .get(name)
                .ok_or_else(|| {
                    CroxErrorKind::UndefinedVariable {
                        name: (*name).to_owned(),
                    }
                    .at(span)
                })
                .cloned(),
            Expr::Unary(op, node) => {
                let value = self.eval(&node.item, node.span)?;
                match op {
                    UnaryOp::Neg => value.neg().map_err(|e| e.at(node.span)),
                    UnaryOp::Not => Ok(value.not()),
                }
            }
            Expr::Binary(lhs_node, op, rhs_node) => {
                let lhs = self.eval(&lhs_node.item, lhs_node.span)?;
                let rhs = self.eval(&rhs_node.item, rhs_node.span)?;
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
            Expr::Group(inner) => self.eval(&inner.item, inner.span),
        }
    }
}

pub fn evaluator<'a, I>(tokens: I) -> impl Iterator<Item = Result<Node<ValueStmt<'a>>>>
where
    I: IntoIterator<Item = StmtNode<'a>>,
{
    Evaluator::new(tokens.into_iter())
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

impl<'a, I> Iterator for Evaluator<'a, I>
where
    I: Iterator<Item = StmtNode<'a>>,
{
    type Item = Result<Node<ValueStmt<'a>>>;

    fn next(&mut self) -> Option<Self::Item> {
        let stmt = self.statements.next()?;
        Some(self.eval_stmt(stmt))
    }
}
