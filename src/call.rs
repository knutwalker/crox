use std::rc::Rc;

use crate::{
    CroxErrorKind, Environment, FunctionDef, Instance, Interpreter, InterpreterContext,
    InterpreterError, Result, Scope, Span, Value,
};

pub trait Callable<'a>: std::fmt::Debug + 'a {
    fn arity(&self) -> usize;
    fn call(
        &self,
        ctx: &mut InterpreterContext<'a, '_>,
        args: &[Value<'a>],
        span: Span,
    ) -> Result<Value<'a>>;

    fn to_value(self) -> Value<'a>
    where
        Self: Sized,
    {
        Value::Callable(Rc::new(self))
    }
}

#[derive(Clone)]
pub struct Function<'a> {
    name: &'a str,
    is_init: bool,
    fun: FunctionDef<'a>,
    closure: Environment<'a>,
}

impl<'a> Function<'a> {
    pub fn new(name: &'a str, fun: FunctionDef<'a>, closure: Environment<'a>) -> Self {
        Self {
            name,
            fun,
            closure,
            is_init: false,
        }
    }

    pub fn method(name: &'a str, fun: FunctionDef<'a>, closure: Environment<'a>) -> Self {
        Self {
            name,
            fun,
            closure,
            is_init: name == "init",
        }
    }

    pub fn bind(&self, instance: Rc<Instance<'a>>) -> Self {
        let env = self.closure.new_scope();
        env.define("this", Value::Instance(instance));
        Self {
            name: self.name,
            is_init: self.is_init,
            fun: self.fun.clone(),
            closure: env,
        }
    }
}

impl<'a> Callable<'a> for Function<'a> {
    fn arity(&self) -> usize {
        self.fun.params.len()
    }

    fn call(
        &self,
        ctx: &mut InterpreterContext<'a, '_>,
        args: &[Value<'a>],
        span: Span,
    ) -> Result<Value<'a>> {
        ctx.run_with_scope(self.closure.new_scope(), |ctx| {
            for (param, arg) in self.fun.params.iter().zip(args) {
                ctx.env.define(param.item, arg.clone());
            }

            let res = Interpreter::eval_stmts_in_scope(ctx, &self.fun.body);
            match res {
                Ok(()) => {
                    if self.is_init {
                        self.closure
                            .get("this", Scope::Local)
                            .map_err(|e| CroxErrorKind::from(e).at(span))
                    } else {
                        Ok(Value::Nil)
                    }
                }
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
