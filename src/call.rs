use crate::{
    Builtins, Class, CroxErrorKind, Environment, FunctionDef, Instance, Interpreter,
    InterpreterContext, InterpreterError, Result, Scope, Span, Value,
};

#[derive(Copy, Clone, Debug)]
pub enum Callable<'env> {
    Fn(&'env Function<'env>),
    Class(&'env Class<'env>),
    Builtin(Builtins),
}

impl<'env> Callable<'env> {
    pub fn arity(&self) -> usize {
        match self {
            Callable::Fn(function) => function.arity(),
            Callable::Class(class) => class.arity(),
            Callable::Builtin(builtins) => builtins.arity(),
        }
    }

    pub fn call(
        &self,
        ctx: &mut InterpreterContext<'env, '_>,
        args: &[Value<'env>],
        span: Span,
    ) -> Result<Value<'env>> {
        match self {
            Callable::Fn(function) => function.call(ctx, args, span),
            Callable::Class(class) => class.call(ctx, args, span),
            Callable::Builtin(builtins) => builtins.call(),
        }
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

    pub fn arity(&self) -> usize {
        self.fun.params.len()
    }

    pub fn call(
        &self,
        ctx: &mut InterpreterContext<'env, '_>,
        args: &[Value<'env>],
        span: Span,
    ) -> Result<Value<'env>> {
        ctx.run_with_scope(self.closure.new_scope(), |ctx| {
            for (param, arg) in self.fun.params.iter().zip(args) {
                ctx.env.define(param.item, *arg);
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
