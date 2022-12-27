use crate::{
    BinaryOp, Callable, CroxError, CroxErrorKind, Environment, Expr, ExprNode, ExpressionRule,
    Function, LogicalOp, Span, StatementRule, Stmt, StmtNode, Type, TypeSet, UnaryOp, Value,
    Valued,
};
use std::marker::PhantomData;

#[derive(Clone, Debug, Default)]
pub struct Interpreter<'a> {
    pub(crate) env: Environment<'a>,
}

impl<'a> Interpreter<'a> {
    pub fn new() -> Self {
        Self {
            env: Environment::default(),
        }
    }
}

impl<'a> Interpreter<'a> {
    pub fn eval_stmts_in_scope(env: &Environment<'a>, stmts: &[StmtNode<'a>]) -> Result<'a, ()> {
        stmts.iter().try_for_each(|stmt| -> Result<'a, ()> {
            Self::eval_stmt(env, &stmt.item, stmt.span)?;
            Ok(())
        })
    }

    pub fn eval_stmt(
        env: &Environment<'a>,
        stmt: &Stmt<'a>,
        span: Span,
    ) -> Result<'a, Valued<'a, StmtNode<'a>>> {
        match &stmt {
            Stmt::Expression { expr } => {
                let _ = Self::eval_expr(env, expr)?;
            }
            Stmt::Function(func) => {
                let name = func.name.item;
                let func = Function::new(name, func.fun.clone(), env.clone());
                let func = func.to_value();
                env.define(name, Some(func));
            }
            Stmt::If {
                condition,
                then_,
                else_,
            } => {
                if Self::eval_expr(env, condition)?.value.as_bool() {
                    Self::eval_stmt(env, &then_.item, then_.span)?;
                } else if let Some(else_) = else_ {
                    Self::eval_stmt(env, &else_.item, else_.span)?;
                }
            }
            Stmt::Print { expr } => {
                let val = Self::eval_expr(env, expr)?.value;
                println!("{val}");
            }
            Stmt::Return { expr } => {
                return Err(InterpreterError::Return(
                    expr.as_ref()
                        .map(|e| Self::eval_expr(env, e).map(|v| v.value))
                        .transpose()?
                        .unwrap_or(Value::Nil),
                ))
            }
            Stmt::Var { name, initializer } => {
                let value = initializer
                    .as_ref()
                    .map(|e| Self::eval_expr(env, e))
                    .transpose()?
                    .map(|v| v.value);
                env.define(name.item, value);
            }
            Stmt::While { condition, body } => {
                while Self::eval_expr(env, condition)?.value.as_bool() {
                    Self::eval_stmt(env, &body.item, body.span)?;
                }
            }
            Stmt::Block { stmts } => {
                env.run_with_new_scope(|env| Self::eval_stmts_in_scope(env, stmts))?;
            }
        }

        Ok(Valued {
            item: stmt.clone().at(span),
            value: Value::Nil,
        })
    }

    pub fn eval_expr(
        env: &Environment<'a>,
        expr: &ExprNode<'a>,
    ) -> crate::Result<Valued<'a, ExprNode<'a>>> {
        let span = expr.span;
        let value = match &*expr.item {
            Expr::Literal(literal) => Value::from(literal),
            Expr::Var(name) => env.get(name).map_err(|e| CroxErrorKind::from(e).at(span))?,
            Expr::Fun(func) => Function::new("<anon>", func.clone(), env.clone()).to_value(),
            Expr::Assignment { name, value } => {
                let span = value.span;
                let value = Self::eval_expr(env, value)?.value;
                env.assign(name, value)
                    .map_err(|e| CroxErrorKind::from(e).at(span))?
            }
            Expr::Unary { op, expr } => {
                let value = Self::eval_expr(env, expr)?.value;
                match op {
                    UnaryOp::Neg => value.neg().map_err(|e| e.at(expr.span))?,
                    UnaryOp::Not => value.not(),
                }
            }
            Expr::Logical { lhs, op, rhs } => {
                let lhs = Self::eval_expr(env, lhs)?.value;
                match op {
                    LogicalOp::And if !lhs.as_bool() => lhs,
                    LogicalOp::Or if lhs.as_bool() => lhs,
                    LogicalOp::And | LogicalOp::Or => Self::eval_expr(env, rhs)?.value,
                }
            }
            Expr::Binary { lhs, op, rhs } => {
                let lhs = Self::eval_expr(env, lhs)?;
                let rhs = Self::eval_expr(env, rhs)?;
                let to_error = |e: crate::Result<CroxErrorKind, CroxErrorKind>| match e {
                    Ok(e) => e.at(lhs.item.span),
                    Err(e) => e.at(rhs.item.span),
                };
                let lhs = lhs.value;
                let rhs = rhs.value;
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
            Expr::Call { callee, arguments } => {
                let callee = Self::eval_expr(env, callee)?;
                let span = callee.item.span;

                let callee = match &callee.value {
                    Value::Fn(callee) => &**callee,
                    _ => {
                        return Err(CroxErrorKind::InvalidType {
                            expected: TypeSet::from_iter([Type::Function, Type::Class]),
                            actual: callee.value.typ(),
                        }
                        .at(span))
                    }
                };

                let arguments = arguments
                    .iter()
                    .map(|arg| Self::eval_expr(env, arg).map(|v| v.value))
                    .collect::<crate::Result<Vec<_>>>()?;

                if callee.arity() != arguments.len() {
                    return Err(CroxErrorKind::ArityMismatch {
                        expected: callee.arity(),
                        actual: arguments.len(),
                    }
                    .at(span));
                }

                callee.call(env, &arguments)?
            }
            Expr::Group { expr } => Self::eval_expr(env, expr)?.value,
        };

        Ok(Valued {
            item: expr.clone(),
            value,
        })
    }
}
impl<'a> Interpreter<'a> {
    pub fn run_with_new_scope<T>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<'a, T>,
    ) -> Result<'a, T> {
        let scope = self.env.new_scope();
        let res = f(self);
        self.env.drop_scope(scope);
        res
    }

    pub fn eval_own_stmts_in_scope(&self, stmts: &[StmtNode<'a>]) -> Result<'a, ()> {
        Self::eval_stmts_in_scope(&self.env, stmts)
    }

    pub fn eval_own_stmt(
        &self,
        stmt: &Stmt<'a>,
        span: Span,
    ) -> Result<'a, Valued<'a, StmtNode<'a>>> {
        Self::eval_stmt(&self.env, stmt, span)
    }

    pub fn eval_own_expr(&self, expr: &ExprNode<'a>) -> crate::Result<Valued<'a, ExprNode<'a>>> {
        Self::eval_expr(&self.env, expr)
    }
}

#[derive(Debug, Clone)]
pub enum InterpreterError<'a> {
    Return(Value<'a>),
    Err(CroxError),
}

impl<'a> From<CroxError> for InterpreterError<'a> {
    fn from(e: CroxError) -> Self {
        Self::Err(e)
    }
}

impl<'a> From<Value<'a>> for InterpreterError<'a> {
    fn from(e: Value<'a>) -> Self {
        Self::Return(e)
    }
}

pub type Result<'a, T, E = InterpreterError<'a>> = std::result::Result<T, E>;

#[derive(Clone, Debug, Default)]
pub struct StreamInterpreter<'a, R, I> {
    interpreter: Interpreter<'a>,
    input: I,
    _rule: PhantomData<R>,
}

impl<'a, R, I> StreamInterpreter<'a, R, I> {
    pub fn new(tokens: I) -> Self {
        Self {
            interpreter: Interpreter::new(),
            input: tokens,
            _rule: PhantomData,
        }
    }
}

pub fn stmt_interpreter<'a, I>(
    tokens: I,
) -> impl Iterator<Item = crate::Result<Valued<'a, StmtNode<'a>>>>
where
    I: IntoIterator<Item = StmtNode<'a>>,
{
    StreamInterpreter::<StatementRule, _>::new(tokens.into_iter())
}

pub fn expr_interpreter<'a, I>(
    tokens: I,
) -> impl Iterator<Item = crate::Result<Valued<'a, ExprNode<'a>>>>
where
    I: IntoIterator<Item = ExprNode<'a>>,
{
    StreamInterpreter::<ExpressionRule, _>::new(tokens.into_iter())
}

impl<'a, R, I> Iterator for StreamInterpreter<'a, R, I>
where
    R: InterpreterRule,
    I: Iterator<Item = R::Input<'a>>,
{
    type Item = crate::Result<R::Interpreted<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        let input = self.input.next()?;
        Some(R::interpret(&mut self.interpreter, input))
    }
}

pub trait InterpreterRule: Sized {
    type Input<'a>;
    type Interpreted<'a>;

    fn interpret<'a>(
        interpreter: &mut Interpreter<'a>,
        input: Self::Input<'a>,
    ) -> crate::Result<Self::Interpreted<'a>>;
}

impl InterpreterRule for ExpressionRule {
    type Input<'a> = ExprNode<'a>;
    type Interpreted<'a> = Valued<'a, ExprNode<'a>>;

    fn interpret<'a>(
        interpreter: &mut Interpreter<'a>,
        input: Self::Input<'a>,
    ) -> crate::Result<Self::Interpreted<'a>> {
        interpreter.eval_own_expr(&input)
    }
}

impl InterpreterRule for StatementRule {
    type Input<'a> = StmtNode<'a>;
    type Interpreted<'a> = Valued<'a, StmtNode<'a>>;

    fn interpret<'a>(
        interpreter: &mut Interpreter<'a>,
        input: Self::Input<'a>,
    ) -> crate::Result<Self::Interpreted<'a>> {
        match interpreter.eval_own_stmt(&input.item, input.span) {
            Ok(value) => Ok(value),
            Err(InterpreterError::Return(value)) => Ok(Valued {
                item: input.clone(),
                value,
            }),
            Err(InterpreterError::Err(e)) => Err(e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_add_nums() {
        let lhs = Value::Number(42.0);
        let rhs = Value::Number(24.0);
        let result = lhs.add(&rhs);
        assert_eq!(result, Ok(Value::Number(66.0)));
    }

    #[test]
    fn test_add_num_to_bool() {
        let lhs = Value::Number(42.0);
        let rhs = Value::Bool(true);
        let result = lhs.add(&rhs);
        assert_eq!(
            result,
            Err(Err(CroxErrorKind::InvalidType {
                expected: TypeSet::from(Type::Number),
                actual: Type::Bool,
            }))
        );
    }

    #[test]
    fn test_add_bool_to_num() {
        let lhs = Value::Bool(true);
        let rhs = Value::Number(42.0);
        let result = lhs.add(&rhs);
        assert_eq!(
            result,
            Err(Ok(CroxErrorKind::InvalidType {
                expected: TypeSet::from(Type::Number),
                actual: Type::Bool,
            }))
        );
    }

    #[test]
    fn test_add_bool_to_bool() {
        let lhs = Value::Bool(true);
        let rhs = Value::Bool(false);
        let result = lhs.add(&rhs);
        assert_eq!(
            result,
            Err(Ok(CroxErrorKind::InvalidType {
                expected: TypeSet::from_iter([Type::Number, Type::String]),
                actual: Type::Bool,
            }))
        );
    }

    #[test]
    fn test_add_str_to_str() {
        let lhs = Value::from("foo");
        let rhs = Value::from("bar");
        let result = lhs.add(&rhs);
        assert_eq!(result, Ok(Value::from("foobar")));
    }

    #[test]
    fn test_add_str_to_num() {
        let lhs = Value::from("foo");
        let rhs = Value::Number(42.0);
        let result = lhs.add(&rhs);
        assert_eq!(result, Ok(Value::from("foo42")));
    }

    #[test]
    fn test_add_num_to_str() {
        let lhs = Value::Number(42.0);
        let rhs = Value::from("foo");
        let result = lhs.add(&rhs);
        assert_eq!(result, Ok(Value::from("42foo")));
    }

    #[test]
    fn test_add_str_to_bool() {
        let lhs = Value::from("foo");
        let rhs = Value::Bool(true);
        let result = lhs.add(&rhs);
        assert_eq!(result, Ok(Value::from("footrue")));
    }

    #[test]
    fn test_add_bool_to_str() {
        let lhs = Value::Bool(true);
        let rhs = Value::from("foo");
        let result = lhs.add(&rhs);
        assert_eq!(result, Ok(Value::from("truefoo")));
    }

    #[test]
    fn test_add_str_to_nil() {
        let lhs = Value::from("foo");
        let rhs = Value::Nil;
        let result = lhs.add(&rhs);
        assert_eq!(result, Ok(Value::from("foonil")));
    }

    #[test]
    fn test_add_nil_to_str() {
        let lhs = Value::Nil;
        let rhs = Value::from("foo");
        let result = lhs.add(&rhs);
        assert_eq!(result, Ok(Value::from("nilfoo")));
    }
}
