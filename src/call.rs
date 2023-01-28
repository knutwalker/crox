use std::rc::Rc;

use crate::{
    CroxErrorKind, Environment, FunctionDef, Instance, Interpreter, InterpreterContext,
    InterpreterError, Result, Scope, Span, Value,
};

pub trait Callable<'env>: std::fmt::Debug + 'env {
    fn arity(&self) -> usize;
    fn call(
        &self,
        ctx: &mut InterpreterContext<'env, '_>,
        args: &[Value<'env>],
        span: Span,
    ) -> Result<Value<'env>>;

    fn to_value(self) -> Value<'env>
    where
        Self: Sized,
    {
        Value::Callable(Rc::new(self))
    }
}

#[derive(Clone)]
pub struct Function<'env> {
    pub name: &'env str,
    is_init: bool,
    fun: FunctionDef<'env>,
    closure: Environment<'env>,
}

impl<'env> Function<'env> {
    pub fn new(name: &'env str, fun: FunctionDef<'env>, closure: Environment<'env>) -> Self {
        Self {
            name,
            fun,
            closure,
            is_init: false,
        }
    }

    pub fn method(name: &'env str, fun: FunctionDef<'env>, closure: Environment<'env>) -> Self {
        Self {
            name,
            fun,
            closure,
            is_init: name == "init",
        }
    }

    pub fn bind(&self, instance: &'env Instance<'env>) -> Self {
        let closure = self.closure.new_scope();
        closure.define("this", Value::Instance(instance));
        Self {
            name: self.name,
            is_init: self.is_init,
            fun: self.fun,
            closure,
        }
    }
}

impl<'env> Callable<'env> for Function<'env> {
    fn arity(&self) -> usize {
        self.fun.params.len()
    }

    fn call(
        &self,
        ctx: &mut InterpreterContext<'env, '_>,
        args: &[Value<'env>],
        span: Span,
    ) -> Result<Value<'env>> {
        ctx.run_with_scope(self.closure.new_scope(), |ctx| {
            for (param, arg) in self.fun.params.iter().zip(args) {
                ctx.env.define(param.item, arg.clone());
            }

            let res = Interpreter::eval_stmts_in_scope(ctx, self.fun.body);
            let res = match res {
                Ok(()) => Value::Nil,
                Err(InterpreterError::Return(val)) => val,
                Err(InterpreterError::Err(err)) => return Err(err),
            };

            if self.is_init {
                self.closure
                    .get("this", Scope::Local)
                    .map_err(|e| CroxErrorKind::from(e).at(span))
            } else {
                Ok(res)
            }
        })
    }
}

impl<'env> std::fmt::Debug for Function<'env> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<fn {}>", self.name)
    }
}
