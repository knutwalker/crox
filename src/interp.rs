use crate::{
    BinaryOp, Class, ClassDecl, Context, CroxError, CroxErrorKind, Expr, ExprNode, ExpressionRule,
    Function, Ident, LogicalOp, Node, Scoped, Slotted, Span, Spannable, StatementRule, Stmt,
    StmtNode, Type, TypeSet, UnaryOp, Value, Valued, Var,
};
use std::{io::Write, marker::PhantomData};

pub type InterpreterContext<'env, 'out> = Context<'env, &'out mut dyn Write>;

impl<'env, 'out> InterpreterContext<'env, 'out> {
    pub fn eval_stmts_in_scope(&mut self, stmts: &[StmtNode<'env>]) -> Result<'env, ()> {
        stmts.iter().try_for_each(|stmt| -> Result<'env, ()> {
            self.eval_stmt(&stmt.item, stmt.span)?;
            Ok(())
        })
    }

    pub fn eval_stmt(&mut self, stmt: &Stmt<'env>, span: Span) -> Result<'env, Valued<'env>> {
        match &stmt {
            Stmt::Expression { expr } => {
                let _ = self.eval_expr(expr.item, expr.span)?;
            }
            Stmt::Class(class) => {
                let superclass = class
                    .superclass
                    .as_ref()
                    .map(|s| {
                        let superclass = s.map(Expr::Var);
                        let superclass = self.eval_expr(&superclass.item, superclass.span)?;
                        match superclass.item {
                            Value::Class(class) => Ok(class.at(superclass.span)),
                            _ => Err(CroxErrorKind::SuperClassIsNotAClass.at(s.span)),
                        }
                    })
                    .transpose()?;

                let name = class.name.item;
                self.env.define(name, Value::Nil);

                let class = if let Some(the_superclass) = superclass {
                    self.run_with_new_scope(|ctx| {
                        let the_superclass = the_superclass.item;
                        let the_superclass = Value::Class(the_superclass);
                        ctx.env.define("super", the_superclass);

                        ctx.class_new(name, class, superclass)
                    })
                } else {
                    self.class_new(name, class, superclass)
                };
                self.env.define(name, class);
            }
            Stmt::Function(func) => {
                let name = func.name.item;
                let func = Function::new(name, func.fun, self.env.clone());
                let func = Value::from(func);
                self.env.define(name, func);
            }
            Stmt::If {
                condition,
                then_,
                else_,
            } => {
                if self
                    .eval_expr(condition.item, condition.span)?
                    .item
                    .as_bool()
                {
                    self.eval_stmt(then_.item, then_.span)?;
                } else if let Some(else_) = else_ {
                    self.eval_stmt(else_.item, else_.span)?;
                }
            }
            Stmt::Print { expr } => {
                let val = self.eval_expr(expr.item, expr.span)?.item;
                writeln!(self.data, "{val}").unwrap();
            }
            Stmt::Return { expr } => {
                return Err(InterpreterError::Return(
                    expr.as_ref()
                        .map(|e| self.eval_expr(e.item, e.span))
                        .transpose()?
                        .map_or(Value::Nil, |v| v.item),
                ))
            }
            Stmt::Var { name, initializer } => {
                let value = initializer
                    .as_ref()
                    .map(|e| self.eval_expr(e.item, e.span))
                    .transpose()?
                    .map(|v| v.item);
                self.env.define(name.item, value);
            }
            Stmt::While { condition, body } => {
                while self
                    .eval_expr(condition.item, condition.span)?
                    .item
                    .as_bool()
                {
                    self.eval_stmt(body.item, body.span)?;
                }
            }
            Stmt::Block { stmts } => {
                self.run_with_new_scope(|ctx| ctx.eval_stmts_in_scope(stmts))?;
            }
        }

        Ok(Value::Nil.at(span))
    }

    pub fn eval_expr(&mut self, expr: &Expr<'env>, span: Span) -> crate::Result<Valued<'env>> {
        let value = match expr {
            Expr::Literal(literal) => Value::from(literal),
            Expr::Var(Var { name, scope }) => self
                .env
                .get(name, scope.get())
                .map_err(|e| CroxErrorKind::from(e).at(span))?,
            Expr::Fun(func) => {
                let func = Function::new("<anon>", *func, self.env.clone());
                Value::from(func)
            }
            Expr::Assignment { name, scope, value } => {
                let value = self.eval_expr(value.item, value.span)?.item;
                self.env
                    .assign(name, value, scope.get())
                    .map_err(|e| CroxErrorKind::from(e).at(span))?
            }
            Expr::Unary { op, expr } => {
                let value = self.eval_expr(expr.item, expr.span)?.item;
                match op {
                    UnaryOp::Neg => value.neg(expr.span)?,
                    UnaryOp::Not => value.not(),
                }
            }
            Expr::Logical { lhs, op, rhs } => {
                let lhs = self.eval_expr(lhs.item, lhs.span)?.item;
                match op {
                    LogicalOp::And if !lhs.as_bool() => lhs,
                    LogicalOp::Or if lhs.as_bool() => lhs,
                    LogicalOp::And | LogicalOp::Or => self.eval_expr(rhs.item, rhs.span)?.item,
                }
            }
            Expr::Binary { lhs, op, rhs } => {
                let lhs = self.eval_expr(lhs.item, lhs.span)?;
                let rhs = self.eval_expr(rhs.item, rhs.span)?;
                match op {
                    BinaryOp::Equals => lhs.item.eq(&rhs.item),
                    BinaryOp::NotEquals => lhs.item.not_eq(&rhs.item),
                    BinaryOp::LessThan => lhs.item.lt(&rhs)?,
                    BinaryOp::LessThanOrEqual => lhs.item.lte(&rhs)?,
                    BinaryOp::GreaterThan => lhs.item.gt(&rhs)?,
                    BinaryOp::GreaterThanOrEqual => lhs.item.gte(&rhs)?,
                    BinaryOp::Add => lhs.item.add(&rhs, lhs.span, Some(self.arena))?,
                    BinaryOp::Sub => lhs.item.sub(&rhs, lhs.span)?,
                    BinaryOp::Mul => lhs.item.mul(&rhs, lhs.span)?,
                    BinaryOp::Div => lhs.item.div(&rhs, lhs.span)?,
                }
            }
            Expr::Call { callee, arguments } => {
                let callee = self.eval_expr(callee.item, callee.span)?;
                let span = callee.span;

                let callee = callee.item.as_callable(callee.span)?;

                let arguments = arguments
                    .iter()
                    .map(|arg| self.eval_expr(&arg.item, arg.span).map(|v| v.item))
                    .collect::<crate::Result<Vec<_>>>()?;

                if callee.arity() != arguments.len() {
                    return Err(CroxErrorKind::ArityMismatch {
                        expected: callee.arity(),
                        actual: arguments.len(),
                    }
                    .at(span));
                }

                callee.call(self, &arguments, span)?
            }
            Expr::Get { object, name, slot } => {
                let object = self.eval_expr(object.item, object.span)?;
                object.item.get(self, name, slot, span)?
            }
            Expr::Set {
                object,
                name,
                value,
            } => {
                let object = self.eval_expr(object.item, object.span)?;
                let value = self.eval_expr(value.item, value.span)?.item;
                object.item.set(name.item, value.clone(), span)?;
                value
            }
            Expr::This { scope } => self
                .env
                .get("this", scope.get())
                .map_err(|e| CroxErrorKind::from(e).at(span))?,
            Expr::Super {
                method,
                scope,
                slot,
            } => {
                return self.eval_super(scope, span, method, slot);
            }
            Expr::Group { expr } => self.eval_expr(expr.item, expr.span)?.item,
        };

        Ok(value.at(span))
    }

    fn class_new(
        &mut self,
        name: &'env str,
        class: &ClassDecl<'env>,
        superclass: Option<Node<&'env Class<'env>>>,
    ) -> Value<'env> {
        let class_members = class.members().map(self.arena, |m| {
            let name = m.item.name.item;
            let fun = m.item.fun;
            let method = Function::method(name, fun, self.env.clone());
            self.alloc(method)
        });

        let class = Class::new(name, superclass, class_members, self.arena);
        let class = self.alloc(class);
        Value::from(class)
    }

    fn eval_super(
        &mut self,
        scope: &Scoped,
        span: Span,
        method: &Ident<'env>,
        slot: &'env Slotted,
    ) -> crate::Result<Node<Value<'env>>> {
        let superclass = self
            .env
            .get("super", scope.get())
            .map_err(|e| CroxErrorKind::from(e).at(span))?;
        let this_scope = scope.get_at_offset(-1).unwrap_or_else(|| {
            panic!("[ICE] scope for `super` needs to be properly resolved, but it was {scope:?}")
        });
        let this = self
            .env
            .get("this", this_scope)
            .map_err(|e| CroxErrorKind::from(e).at(span))?;
        let method = match &superclass {
            Value::Class(superclass) => {
                let method_fn = superclass
                    .lookup(method.item, slot)
                    .into_method(method.item, method.span)?;
                method_fn.at(method.span)
            }
            _ => {
                return Err(CroxErrorKind::InvalidType {
                    expected: TypeSet::from(Type::Class),
                    actual: superclass.typ(),
                }
                .at(span))
            }
        };
        let this = match this {
            Value::Instance(instance) => instance,
            _ => {
                return Err(CroxErrorKind::InvalidType {
                    expected: TypeSet::from(Type::Instance),
                    actual: this.typ(),
                }
                .at(span))
            }
        };

        let span = method.span;
        let method = method.item.bind(this);
        let value = Value::from(method);
        Ok(value.at(span))
    }

    pub fn alloc<T>(&self, value: T) -> &'env T {
        self.arena.alloc(value)
    }
}

#[derive(Debug, Clone)]
pub enum InterpreterError<'env> {
    Return(Value<'env>),
    Err(CroxError),
}

impl<'env> From<CroxError> for InterpreterError<'env> {
    fn from(e: CroxError) -> Self {
        Self::Err(e)
    }
}

impl<'env> From<Value<'env>> for InterpreterError<'env> {
    fn from(e: Value<'env>) -> Self {
        Self::Return(e)
    }
}

pub type Result<'env, T, E = InterpreterError<'env>> = std::result::Result<T, E>;

pub struct StreamInterpreter<'env, 'out, R, I> {
    context: InterpreterContext<'env, 'out>,
    input: I,
    _rule: PhantomData<R>,
}

impl<'env, 'out, R, I> StreamInterpreter<'env, 'out, R, I> {
    pub fn new(context: InterpreterContext<'env, 'out>, tokens: I) -> Self {
        Self {
            context,
            input: tokens,
            _rule: PhantomData,
        }
    }
}

pub fn stmt_interpreter<'env: 'out, 'out, I>(
    context: InterpreterContext<'env, 'out>,
    tokens: I,
) -> impl Iterator<Item = crate::Result<Valued<'env>>> + 'out
where
    I: IntoIterator<Item = StmtNode<'env>> + 'out,
{
    StreamInterpreter::<StatementRule, _>::new(context, tokens.into_iter())
}

pub fn expr_interpreter<'env: 'out, 'out, I>(
    context: InterpreterContext<'env, 'out>,
    tokens: I,
) -> impl Iterator<Item = crate::Result<Valued<'env>>> + 'out
where
    I: IntoIterator<Item = ExprNode<'env>> + 'out,
{
    StreamInterpreter::<ExpressionRule, _>::new(context, tokens.into_iter())
}

impl<'env, 'out, R, I> Iterator for StreamInterpreter<'env, 'out, R, I>
where
    R: InterpreterRule,
    I: Iterator<Item = R::Input<'env>>,
{
    type Item = crate::Result<R::Interpreted<'env>>;

    fn next(&mut self) -> Option<Self::Item> {
        let input = self.input.next()?;
        Some(R::interpret(&mut self.context, input))
    }
}

pub trait InterpreterRule: Sized {
    type Input<'env>;
    type Interpreted<'env>;

    fn interpret<'env>(
        context: &mut InterpreterContext<'env, '_>,
        input: Self::Input<'env>,
    ) -> crate::Result<Self::Interpreted<'env>>;
}

impl InterpreterRule for ExpressionRule {
    type Input<'env> = ExprNode<'env>;
    type Interpreted<'env> = Valued<'env>;

    fn interpret<'env>(
        context: &mut InterpreterContext<'env, '_>,
        input: Self::Input<'env>,
    ) -> crate::Result<Self::Interpreted<'env>> {
        context.eval_expr(&input.item, input.span)
    }
}

impl InterpreterRule for StatementRule {
    type Input<'env> = StmtNode<'env>;
    type Interpreted<'env> = Valued<'env>;

    fn interpret<'env>(
        context: &mut InterpreterContext<'env, '_>,
        input: Self::Input<'env>,
    ) -> crate::Result<Self::Interpreted<'env>> {
        match context.eval_stmt(&input.item, input.span) {
            Ok(value) => Ok(value),
            Err(InterpreterError::Return(value)) => Ok(value.at(input.span)),
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
        let rhs = Value::Number(24.0).at(3..7);
        let result = lhs.add(&rhs, 1..3, None);
        assert_eq!(result, Ok(Value::Number(66.0)));
    }

    #[test]
    fn test_add_num_to_bool() {
        let lhs = Value::Number(42.0);
        let rhs = Value::Bool(true).at(3..7);
        let result = lhs.add(&rhs, 1..3, None);
        assert_eq!(
            result,
            Err(CroxErrorKind::InvalidType {
                expected: TypeSet::from(Type::Number),
                actual: Type::Bool,
            }
            .at(3..7))
        );
    }

    #[test]
    fn test_add_bool_to_num() {
        let lhs = Value::Bool(true);
        let rhs = Value::Number(42.0).at(3..7);
        let result = lhs.add(&rhs, 1..3, None);
        assert_eq!(
            result,
            Err(CroxErrorKind::InvalidType {
                expected: TypeSet::from(Type::Number),
                actual: Type::Bool,
            }
            .at(1..3))
        );
    }

    #[test]
    fn test_add_bool_to_bool() {
        let lhs = Value::Bool(true);
        let rhs = Value::Bool(false).at(3..7);
        let result = lhs.add(&rhs, 1..3, None);
        assert_eq!(
            result,
            Err(CroxErrorKind::InvalidType {
                expected: TypeSet::from_iter([Type::Number, Type::String]),
                actual: Type::Bool,
            }
            .at(1..3))
        );
    }

    #[test]
    fn test_add_str_to_str() {
        let lhs = Value::from("foo");
        let rhs = Value::from("bar").at(3..7);
        let result = lhs.add(&rhs, 1..3, None);
        assert_eq!(result, Ok(Value::from("foobar")));
    }

    #[test]
    fn test_add_str_to_num() {
        let lhs = Value::from("foo");
        let rhs = Value::Number(42.0).at(3..7);
        let result = lhs.add(&rhs, 1..3, None);
        assert_eq!(result, Ok(Value::from("foo42")));
    }

    #[test]
    fn test_add_num_to_str() {
        let lhs = Value::Number(42.0);
        let rhs = Value::from("foo").at(3..7);
        let result = lhs.add(&rhs, 1..3, None);
        assert_eq!(result, Ok(Value::from("42foo")));
    }

    #[test]
    fn test_add_str_to_bool() {
        let lhs = Value::from("foo");
        let rhs = Value::Bool(true).at(3..7);
        let result = lhs.add(&rhs, 1..3, None);
        assert_eq!(result, Ok(Value::from("footrue")));
    }

    #[test]
    fn test_add_bool_to_str() {
        let lhs = Value::Bool(true);
        let rhs = Value::from("foo").at(3..7);
        let result = lhs.add(&rhs, 1..3, None);
        assert_eq!(result, Ok(Value::from("truefoo")));
    }

    #[test]
    fn test_add_str_to_nil() {
        let lhs = Value::from("foo");
        let rhs = Value::Nil.at(3..7);
        let result = lhs.add(&rhs, 1..3, None);
        assert_eq!(result, Ok(Value::from("foonil")));
    }

    #[test]
    fn test_add_nil_to_str() {
        let lhs = Value::Nil;
        let rhs = Value::from("foo").at(3..7);
        let result = lhs.add(&rhs, 1..3, None);
        assert_eq!(result, Ok(Value::from("nilfoo")));
    }
}
