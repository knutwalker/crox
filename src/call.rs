use std::rc::Rc;

use crate::{Context, Environment, FunctionDef, Interpreter, InterpreterError, Result, Value};
pub use builtin::Clock;

pub trait Callable<'a>: std::fmt::Debug + 'a {
    fn arity(&self) -> usize;
    fn call(&self, ctx: &mut Context<'a, '_>, args: &[Value<'a>]) -> Result<Value<'a>>;

    fn to_value(self) -> Value<'a>
    where
        Self: Sized,
    {
        Value::Fn(Rc::new(self))
    }
}

#[derive(Clone)]
pub struct Function<'a> {
    name: &'a str,
    fun: FunctionDef<'a>,
    closure: Environment<'a>,
}

impl<'a> Function<'a> {
    pub fn new(name: &'a str, fun: FunctionDef<'a>, closure: Environment<'a>) -> Self {
        Self { name, fun, closure }
    }
}

impl<'a> Callable<'a> for Function<'a> {
    fn arity(&self) -> usize {
        self.fun.params.len()
    }

    fn call(&self, ctx: &mut Context<'a, '_>, args: &[Value<'a>]) -> Result<Value<'a>> {
        ctx.run_with_scope(self.closure.new_scope(), |ctx| {
            for (param, arg) in self.fun.params.iter().zip(args) {
                ctx.env.define(param.item, arg.clone());
            }

            let res = Interpreter::eval_stmts_in_scope(ctx, &self.fun.body);
            match res {
                Ok(()) => Ok(Value::Nil),
                Err(InterpreterError::Return(value)) => Ok(value),
                Err(InterpreterError::Err(err)) => Err(err),
            }
        })
    }
}

impl<'a> std::fmt::Debug for Function<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<fn {}>", self.name)
    }
}

mod builtin {
    use std::time::{SystemTime, UNIX_EPOCH};

    use super::Callable;
    use crate::{Context, Result, Value};

    #[derive(Copy, Clone)]
    pub struct Clock;

    impl<'a> Callable<'a> for Clock {
        fn arity(&self) -> usize {
            0
        }

        fn call(&self, _ctx: &mut Context<'a, '_>, _args: &[Value<'a>]) -> Result<Value<'a>> {
            Ok(SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map_or(0.0, |d| d.as_secs_f64())
                .into())
        }
    }

    impl std::fmt::Debug for Clock {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "<builtin clock>")
        }
    }
}
