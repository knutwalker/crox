use crate::{
    BinaryOp, Callable, Class, CroxError, CroxErrorKind, Environment, Expr, ExprNode,
    ExpressionRule, Function, InterpreterContext, LogicalOp, Span, StatementRule, Stmt, StmtNode,
    UnaryOp, Value, Valued,
};
use std::{io::Write, marker::PhantomData, rc::Rc};

pub struct Interpreter<'a, 'o> {
    context: InterpreterContext<'a, 'o>,
}

impl<'a, 'o> Interpreter<'a, 'o> {
    pub fn new(out: &'o mut dyn Write, env: Environment<'a>) -> Self {
        Self {
            context: InterpreterContext::new(env, out),
        }
    }
}

impl<'a, 'o> Interpreter<'a, 'o> {
    pub fn eval_stmts_in_scope(
        ctx: &mut InterpreterContext<'a, 'o>,
        stmts: &[StmtNode<'a>],
    ) -> Result<'a, ()> {
        stmts.iter().try_for_each(|stmt| -> Result<'a, ()> {
            Self::eval_stmt(ctx, &stmt.item, stmt.span)?;
            Ok(())
        })
    }

    pub fn eval_stmt(
        ctx: &mut InterpreterContext<'a, 'o>,
        stmt: &Stmt<'a>,
        span: Span,
    ) -> Result<'a, Valued<'a>> {
        match &stmt {
            Stmt::Expression { expr } => {
                let _ = Self::eval_expr(ctx, expr)?;
            }
            Stmt::Class(class) => {
                let name = class.name.item;
                ctx.env.define(name, Value::Nil);

                let class_members = class.members().map(|m| {
                    let name = m.item.name.item;
                    let fun = m.item.fun.clone();
                    let fun = Function::method(name, fun, ctx.env.clone());
                    Rc::new(fun)
                });

                let class = Class::new(name, class_members);
                let class = Value::from(class);
                ctx.env.define(name, class);
            }
            Stmt::Function(func) => {
                let name = func.name.item;
                let func = Function::new(name, func.fun.clone(), ctx.env.clone());
                let func = func.to_value();
                ctx.env.define(name, func);
            }
            Stmt::If {
                condition,
                then_,
                else_,
            } => {
                if Self::eval_expr(ctx, condition)?.item.as_bool() {
                    Self::eval_stmt(ctx, &then_.item, then_.span)?;
                } else if let Some(else_) = else_ {
                    Self::eval_stmt(ctx, &else_.item, else_.span)?;
                }
            }
            Stmt::Print { expr } => {
                let val = Self::eval_expr(ctx, expr)?.item;
                writeln!(ctx.data, "{val}").unwrap();
            }
            Stmt::Return { expr } => {
                return Err(InterpreterError::Return(
                    expr.as_ref()
                        .map(|e| Self::eval_expr(ctx, e))
                        .transpose()?
                        .map(|v| v.item)
                        .unwrap_or(Value::Nil),
                ))
            }
            Stmt::Var { name, initializer } => {
                let value = initializer
                    .as_ref()
                    .map(|e| Self::eval_expr(ctx, e))
                    .transpose()?
                    .map(|v| v.item);
                ctx.env.define(name.item, value);
            }
            Stmt::While { condition, body } => {
                while Self::eval_expr(ctx, condition)?.item.as_bool() {
                    Self::eval_stmt(ctx, &body.item, body.span)?;
                }
            }
            Stmt::Block { stmts } => {
                ctx.run_with_new_scope(|ctx| Self::eval_stmts_in_scope(ctx, stmts))?
            }
        }

        Ok(Valued::new(Value::Nil, span))
    }

    pub fn eval_expr(
        ctx: &mut InterpreterContext<'a, 'o>,
        expr: &ExprNode<'a>,
    ) -> crate::Result<Valued<'a>> {
        let span = expr.span;
        let value = match &*expr.item {
            Expr::Literal(literal) => Value::from(literal),
            Expr::Var { name, scope } => ctx
                .env
                .get(name, scope.get())
                .map_err(|e| CroxErrorKind::from(e).at(span))?,
            Expr::Fun(func) => Function::new("<anon>", func.clone(), ctx.env.clone()).to_value(),
            Expr::Assignment { name, scope, value } => {
                let value = Self::eval_expr(ctx, value)?.item;
                ctx.env
                    .assign(name, value, scope.get())
                    .map_err(|e| CroxErrorKind::from(e).at(span))?
            }
            Expr::Unary { op, expr } => {
                let value = Self::eval_expr(ctx, expr)?.item;
                match op {
                    UnaryOp::Neg => value.neg().map_err(|e| e.at(expr.span))?,
                    UnaryOp::Not => value.not(),
                }
            }
            Expr::Logical { lhs, op, rhs } => {
                let lhs = Self::eval_expr(ctx, lhs)?.item;
                match op {
                    LogicalOp::And if !lhs.as_bool() => lhs,
                    LogicalOp::Or if lhs.as_bool() => lhs,
                    LogicalOp::And | LogicalOp::Or => Self::eval_expr(ctx, rhs)?.item,
                }
            }
            Expr::Binary { lhs, op, rhs } => {
                let lhs = Self::eval_expr(ctx, lhs)?;
                let rhs = Self::eval_expr(ctx, rhs)?;
                let to_error = |e: crate::Result<CroxErrorKind, CroxErrorKind>| match e {
                    Ok(e) => e.at(lhs.span),
                    Err(e) => e.at(rhs.span),
                };
                let lhs = lhs.item;
                let rhs = rhs.item;
                match op {
                    BinaryOp::Equals => lhs.eq(&rhs),
                    BinaryOp::NotEquals => lhs.not_eq(&rhs),
                    BinaryOp::LessThan => lhs.lt(&rhs).map_err(to_error)?,
                    BinaryOp::LessThanOrEqual => lhs.lte(&rhs).map_err(to_error)?,
                    BinaryOp::GreaterThan => lhs.gt(&rhs).map_err(to_error)?,
                    BinaryOp::GreaterThanOrEqual => lhs.gte(&rhs).map_err(to_error)?,
                    BinaryOp::Add => lhs.add(&rhs).map_err(to_error)?,
                    BinaryOp::Sub => lhs.sub(&rhs).map_err(to_error)?,
                    BinaryOp::Mul => lhs.mul(&rhs).map_err(to_error)?,
                    BinaryOp::Div => lhs.div(&rhs).map_err(to_error)?,
                }
            }
            Expr::Call { callee, arguments } => {
                let callee = Self::eval_expr(ctx, callee)?;
                let span = callee.span;

                let callee = callee.item.as_callable(callee.span)?;

                let arguments = arguments
                    .iter()
                    .map(|arg| Self::eval_expr(ctx, arg).map(|v| v.item))
                    .collect::<crate::Result<Vec<_>>>()?;

                if callee.arity() != arguments.len() {
                    return Err(CroxErrorKind::ArityMismatch {
                        expected: callee.arity(),
                        actual: arguments.len(),
                    }
                    .at(span));
                }

                callee.call(ctx, &arguments, span)?
            }
            Expr::Get { object, name } => {
                let object = Self::eval_expr(ctx, object)?;
                let instance = object.item.as_instance(span)?;
                instance.get(name, ctx, span)?
            }
            Expr::Set {
                object,
                name,
                value,
            } => {
                let object = Self::eval_expr(ctx, object)?;
                let instance = object.item.as_mut_instance(span)?;
                let value = Self::eval_expr(ctx, value)?.item;
                instance.set(name.item, value.clone());

                value
            }
            Expr::This { scope } => ctx
                .env
                .get("this", scope.get())
                .map_err(|e| CroxErrorKind::from(e).at(span))?,
            Expr::Group { expr } => Self::eval_expr(ctx, expr)?.item,
        };

        Ok(Valued::new(value, span))
    }
}
impl<'a, 'e> Interpreter<'a, 'e> {
    pub fn eval_own_stmts_in_scope(&mut self, stmts: &[StmtNode<'a>]) -> Result<'a, ()> {
        Self::eval_stmts_in_scope(&mut self.context, stmts)
    }

    pub fn eval_own_stmt(&mut self, stmt: &Stmt<'a>, span: Span) -> Result<'a, Valued<'a>> {
        Self::eval_stmt(&mut self.context, stmt, span)
    }

    pub fn eval_own_expr(&mut self, expr: &ExprNode<'a>) -> crate::Result<Valued<'a>> {
        Self::eval_expr(&mut self.context, expr)
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

pub struct StreamInterpreter<'a, 'e, R, I> {
    interpreter: Interpreter<'a, 'e>,
    input: I,
    _rule: PhantomData<R>,
}

impl<'a, 'o, R, I> StreamInterpreter<'a, 'o, R, I> {
    pub fn new(out: &'o mut dyn Write, env: Environment<'a>, tokens: I) -> Self {
        Self {
            interpreter: Interpreter::new(out, env),
            input: tokens,
            _rule: PhantomData,
        }
    }
}

pub fn stmt_interpreter<'a: 'o, 'o, I>(
    out: &'o mut dyn Write,
    env: Environment<'a>,
    tokens: I,
) -> impl Iterator<Item = crate::Result<Valued<'a>>> + 'o
where
    I: IntoIterator<Item = StmtNode<'a>> + 'o,
{
    StreamInterpreter::<StatementRule, _>::new(out, env, tokens.into_iter())
}

pub fn expr_interpreter<'a: 'o, 'o, I>(
    out: &'o mut dyn Write,
    env: Environment<'a>,
    tokens: I,
) -> impl Iterator<Item = crate::Result<Valued<'a>>> + 'o
where
    I: IntoIterator<Item = ExprNode<'a>> + 'o,
{
    StreamInterpreter::<ExpressionRule, _>::new(out, env, tokens.into_iter())
}

impl<'a, 'e, R, I> Iterator for StreamInterpreter<'a, 'e, R, I>
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

    fn interpret<'a, 'e>(
        interpreter: &mut Interpreter<'a, 'e>,
        input: Self::Input<'a>,
    ) -> crate::Result<Self::Interpreted<'a>>;
}

impl InterpreterRule for ExpressionRule {
    type Input<'a> = ExprNode<'a>;
    type Interpreted<'a> = Valued<'a>;

    fn interpret<'a, 'e>(
        interpreter: &mut Interpreter<'a, 'e>,
        input: Self::Input<'a>,
    ) -> crate::Result<Self::Interpreted<'a>> {
        interpreter.eval_own_expr(&input)
    }
}

impl InterpreterRule for StatementRule {
    type Input<'a> = StmtNode<'a>;
    type Interpreted<'a> = Valued<'a>;

    fn interpret<'a, 'e>(
        interpreter: &mut Interpreter<'a, 'e>,
        input: Self::Input<'a>,
    ) -> crate::Result<Self::Interpreted<'a>> {
        match interpreter.eval_own_stmt(&input.item, input.span) {
            Ok(value) => Ok(value),
            Err(InterpreterError::Return(value)) => Ok(Valued::new(value, input.span)),
            Err(InterpreterError::Err(e)) => Err(e),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{Type, TypeSet};

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
