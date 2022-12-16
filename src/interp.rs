use crate::{
    BinaryOp, Callable, CroxErrorKind, Environment, Expr, ExprNode, ExpressionRule, Function,
    LogicalOp, Result, Span, StatementRule, Stmt, StmtNode, Type, TypeSet, UnaryOp, Value, Valued,
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
    pub fn run_with_new_scope<T>(&mut self, f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        let scope = self.env.new_scope();
        let res = f(self);
        self.env.drop_scope(scope);
        res
    }

    pub fn eval_stmts_in_scope(&mut self, stmts: &[StmtNode<'a>]) -> Result<()> {
        stmts.iter().try_for_each(|stmt| -> Result {
            self.eval_stmt(&stmt.item, stmt.span)?;
            Ok(())
        })
    }

    pub fn eval_stmt(&mut self, stmt: &Stmt<'a>, span: Span) -> Result<Valued<'a, StmtNode<'a>>> {
        match &stmt {
            Stmt::Expression { expr } => {
                let _ = self.eval_expr(expr)?;
            }
            Stmt::Function(func) => {
                let name = func.name.item;
                let func = Function::new(func.clone());
                let func = func.to_value();
                self.env.define(name, Some(func));
            }
            Stmt::If {
                condition,
                then_,
                else_,
            } => {
                if self.eval_expr(condition)?.value.as_bool() {
                    self.eval_stmt(&then_.item, then_.span)?;
                } else if let Some(else_) = else_ {
                    self.eval_stmt(&else_.item, else_.span)?;
                }
            }
            Stmt::Print { expr } => {
                let val = self.eval_expr(expr)?.value;
                println!("{val}");
            }
            Stmt::Var { name, initializer } => {
                let value = initializer
                    .as_ref()
                    .map(|e| self.eval_expr(e))
                    .transpose()?
                    .map(|v| v.value);
                self.env.define(name.item, value);
            }
            Stmt::While { condition, body } => {
                while self.eval_expr(condition)?.value.as_bool() {
                    self.eval_stmt(&body.item, body.span)?;
                }
            }
            Stmt::Block { stmts } => {
                self.run_with_new_scope(|this| this.eval_stmts_in_scope(stmts))?;
            }
        }

        Ok(Valued {
            item: stmt.clone().at(span),
            value: Value::Nil,
        })
    }

    pub fn eval_expr(&mut self, expr: &ExprNode<'a>) -> Result<Valued<'a, ExprNode<'a>>> {
        let span = expr.span;
        let value = match &*expr.item {
            Expr::Literal(literal) => Value::from(literal),
            Expr::Var(name) => self
                .env
                .get(name)
                .map_err(|e| CroxErrorKind::from(e).at(span))?
                .clone(),
            Expr::Assignment { name, value } => {
                let span = value.span;
                let value = self.eval_expr(value)?.value;
                self.env
                    .assign(name, value)
                    .map_err(|e| CroxErrorKind::from(e).at(span))?
                    .clone()
            }
            Expr::Unary { op, expr } => {
                let value = self.eval_expr(expr)?.value;
                match op {
                    UnaryOp::Neg => value.neg().map_err(|e| e.at(expr.span))?,
                    UnaryOp::Not => value.not(),
                }
            }
            Expr::Logical { lhs, op, rhs } => {
                let lhs = self.eval_expr(lhs)?.value;
                match op {
                    LogicalOp::And if !lhs.as_bool() => lhs,
                    LogicalOp::Or if lhs.as_bool() => lhs,
                    LogicalOp::And | LogicalOp::Or => self.eval_expr(rhs)?.value,
                }
            }
            Expr::Binary { lhs, op, rhs } => {
                let lhs = self.eval_expr(lhs)?;
                let rhs = self.eval_expr(rhs)?;
                let to_error = |e: Result<CroxErrorKind, CroxErrorKind>| match e {
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
                let callee = self.eval_expr(callee)?;
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
                    .map(|arg| self.eval_expr(arg).map(|v| v.value))
                    .collect::<Result<Vec<_>>>()?;

                if callee.arity() != arguments.len() {
                    return Err(CroxErrorKind::ArityMismatch {
                        expected: callee.arity(),
                        actual: arguments.len(),
                    }
                    .at(span));
                }

                callee.call(self, &arguments)?
            }
            Expr::Group { expr } => self.eval_expr(expr)?.value,
        };

        Ok(Valued {
            item: expr.clone(),
            value,
        })
    }
}

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

pub fn stmt_interpreter<'a, I>(tokens: I) -> impl Iterator<Item = Result<Valued<'a, StmtNode<'a>>>>
where
    I: IntoIterator<Item = StmtNode<'a>>,
{
    StreamInterpreter::<StatementRule, _>::new(tokens.into_iter())
}

pub fn expr_interpreter<'a, I>(tokens: I) -> impl Iterator<Item = Result<Valued<'a, ExprNode<'a>>>>
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
    type Item = Result<R::Interpreted<'a>>;

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
    ) -> Result<Self::Interpreted<'a>>;
}

impl InterpreterRule for ExpressionRule {
    type Input<'a> = ExprNode<'a>;
    type Interpreted<'a> = Valued<'a, ExprNode<'a>>;

    fn interpret<'a>(
        interpreter: &mut Interpreter<'a>,
        input: Self::Input<'a>,
    ) -> Result<Self::Interpreted<'a>> {
        interpreter.eval_expr(&input)
    }
}

impl InterpreterRule for StatementRule {
    type Input<'a> = StmtNode<'a>;
    type Interpreted<'a> = Valued<'a, StmtNode<'a>>;

    fn interpret<'a>(
        interpreter: &mut Interpreter<'a>,
        input: Self::Input<'a>,
    ) -> Result<Self::Interpreted<'a>> {
        interpreter.eval_stmt(&input.item, input.span)
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
