use crate::{
    BinaryOp, CroxErrorKind, Environment, Expr, ExprNode, ExpressionRule, LogicalOp, Result, Span,
    StatementRule, Stmt, StmtNode, Type, TypeSet, UnaryOp, Value, Valued,
};
use std::{cmp::Ordering, marker::PhantomData};

#[derive(Clone, Debug, Default)]
pub struct Interpreter<'a, R, I> {
    env: Environment<'a>,
    input: I,
    _rule: PhantomData<R>,
}

impl<'a, R, I> Interpreter<'a, R, I> {
    pub fn new(tokens: I) -> Self {
        Self {
            env: Environment::default(),
            input: tokens,
            _rule: PhantomData,
        }
    }
}

impl<'a, R, I> Interpreter<'a, R, I> {
    pub fn eval_stmt(&self, stmt: &Stmt<'a>, span: Span) -> Result<Valued<StmtNode<'a>>> {
        match &stmt {
            Stmt::Expression(expr) => {
                let _ = self.eval_expr(expr)?;
            }
            Stmt::If(cond, then_, else_) => {
                if self.eval_expr(cond)?.value.as_bool() {
                    self.eval_stmt(&then_.item, then_.span)?;
                } else if let Some(else_) = else_ {
                    self.eval_stmt(&else_.item, else_.span)?;
                }
            }
            Stmt::Print(expr) => {
                let val = self.eval_expr(expr)?.value;
                println!("{}", val);
            }
            Stmt::Var(name, expr) => {
                let value = expr
                    .as_ref()
                    .map(|e| self.eval_expr(e))
                    .transpose()?
                    .map(|v| v.value)
                    .unwrap_or_default();
                self.env.define(name, value);
            }
            Stmt::While(cond, body) => {
                while self.eval_expr(cond)?.value.as_bool() {
                    self.eval_stmt(&body.item, body.span)?;
                }
            }
            Stmt::Block(stmts) => {
                let _scope = self.env.push_scope();
                for stmt in stmts.iter() {
                    self.eval_stmt(&stmt.item, stmt.span)?;
                }
            }
        }

        Ok(Valued {
            item: stmt.clone().at(span),
            value: Value::Nil,
        })
    }

    pub fn eval_expr(&self, expr: &ExprNode<'a>) -> Result<Valued<ExprNode<'a>>> {
        let span = expr.span;
        let value = match &*expr.item {
            Expr::Literal(literal) => Value::from(literal),
            Expr::Var(name) => self
                .env
                .get(name)
                .ok_or_else(|| {
                    CroxErrorKind::UndefinedVariable {
                        name: (*name).to_owned(),
                    }
                    .at(span)
                })
                .map(|v| v.clone())?,
            Expr::Assignment(name, value) => {
                let span = value.span;
                let value = self.eval_expr(value)?.value;
                let _prev = self.env.assign(name, value.clone()).ok_or_else(|| {
                    CroxErrorKind::UndefinedVariable {
                        name: (*name).to_owned(),
                    }
                    .at(span)
                })?;
                value
            }
            Expr::Unary(op, node) => {
                let value = self.eval_expr(node)?.value;
                match op {
                    UnaryOp::Neg => value.neg().map_err(|e| e.at(node.span))?,
                    UnaryOp::Not => value.not(),
                }
            }
            Expr::Logical(lhs_node, op, rhs_node) => {
                let lhs = self.eval_expr(lhs_node)?.value;
                match op {
                    LogicalOp::And if !lhs.as_bool() => lhs,
                    LogicalOp::Or if lhs.as_bool() => lhs,
                    LogicalOp::And | LogicalOp::Or => self.eval_expr(rhs_node)?.value,
                }
            }
            Expr::Binary(lhs_node, op, rhs_node) => {
                let lhs = self.eval_expr(lhs_node)?.value;
                let rhs = self.eval_expr(rhs_node)?.value;
                let to_error = |e: Result<CroxErrorKind, CroxErrorKind>| match e {
                    Ok(e) => e.at(lhs_node.span),
                    Err(e) => e.at(rhs_node.span),
                };
                match op {
                    BinaryOp::Equals => lhs.eq(&rhs),
                    BinaryOp::NotEquals => lhs.not_eq(&rhs),
                    BinaryOp::LessThan => lhs.lt(&rhs),
                    BinaryOp::LessThanOrEqual => lhs.lte(&rhs),
                    BinaryOp::GreaterThan => lhs.gt(&rhs),
                    BinaryOp::GreaterThanOrEqual => lhs.gte(&rhs),
                    BinaryOp::Add => lhs.add(&rhs).map_err(to_error)?,
                    BinaryOp::Sub => lhs.sub(&rhs).map_err(to_error)?,
                    BinaryOp::Mul => lhs.mul(&rhs).map_err(to_error)?,
                    BinaryOp::Div => lhs.div(&rhs).map_err(to_error)?,
                }
            }
            Expr::Group(inner) => self.eval_expr(inner)?.value,
        };

        Ok(Valued {
            item: expr.clone(),
            value,
        })
    }
}

pub fn stmt_interpreter<'a, I>(tokens: I) -> impl Iterator<Item = Result<Valued<StmtNode<'a>>>>
where
    I: IntoIterator<Item = StmtNode<'a>>,
{
    Interpreter::<StatementRule, _>::new(tokens.into_iter())
}

pub fn expr_interpreter<'a, I>(tokens: I) -> impl Iterator<Item = Result<Valued<ExprNode<'a>>>>
where
    I: IntoIterator<Item = ExprNode<'a>>,
{
    Interpreter::<ExpressionRule, _>::new(tokens.into_iter())
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

impl<'a, R, I> Iterator for Interpreter<'a, R, I>
where
    R: InterpreterRule,
    I: Iterator<Item = R::Input<'a>>,
{
    type Item = Result<R::Interpreted<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        let input = self.input.next()?;
        Some(R::interpret(self, input))
    }
}

pub trait InterpreterRule: Sized {
    type Input<'a>;
    type Interpreted<'a>;

    fn interpret<'a, T>(
        interpreter: &mut Interpreter<'a, Self, T>,
        input: Self::Input<'a>,
    ) -> Result<Self::Interpreted<'a>>
    where
        T: Iterator<Item = Self::Input<'a>>;
}

impl InterpreterRule for ExpressionRule {
    type Input<'a> = ExprNode<'a>;
    type Interpreted<'a> = Valued<ExprNode<'a>>;

    fn interpret<'a, T>(
        interpreter: &mut Interpreter<'a, Self, T>,
        input: Self::Input<'a>,
    ) -> Result<Self::Interpreted<'a>>
    where
        T: Iterator<Item = Self::Input<'a>>,
    {
        interpreter.eval_expr(&input)
    }
}

impl InterpreterRule for StatementRule {
    type Input<'a> = StmtNode<'a>;
    type Interpreted<'a> = Valued<StmtNode<'a>>;

    fn interpret<'a, T>(
        interpreter: &mut Interpreter<'a, Self, T>,
        input: Self::Input<'a>,
    ) -> Result<Self::Interpreted<'a>>
    where
        T: Iterator<Item = Self::Input<'a>>,
    {
        interpreter.eval_stmt(&input.item, input.span)
    }
}
