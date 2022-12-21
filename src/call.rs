use crate::{FunctionDecl, Interpreter, Result, Value};
pub use builtin::Clock;

pub trait Callable<'a>: std::fmt::Debug + 'a {
    fn arity(&self) -> usize;
    fn call(&self, interpreter: &mut Interpreter<'a>, args: &[Value<'a>]) -> Result<Value<'a>>;

    fn to_value(self) -> Value<'a>
    where
        Self: Sized,
    {
        Value::Fn(std::rc::Rc::new(self))
    }
}

#[derive(Clone)]
pub struct Function<'a> {
    decl: FunctionDecl<'a>,
}

impl<'a> Function<'a> {
    pub fn new(decl: FunctionDecl<'a>) -> Self {
        Self { decl }
    }
}

impl<'a> Callable<'a> for Function<'a> {
    fn arity(&self) -> usize {
        self.decl.params.len()
    }

    fn call(&self, interpreter: &mut Interpreter<'a>, args: &[Value<'a>]) -> Result<Value<'a>> {
        match interpreter.run_with_new_scope(|interpreter| {
            for (param, arg) in self.decl.params.iter().zip(args) {
                interpreter.env.define(param.item, arg.clone());
            }
            interpreter.eval_stmts_in_scope(&self.decl.body)
        }) {
            Ok(()) => Ok(Value::Nil),
            Err(crate::interp::InterpreterError::Return(value)) => Ok(value),
            Err(crate::interp::InterpreterError::Err(err)) => Err(err),
        }
    }
}

impl<'a> std::fmt::Debug for Function<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<fn {}>", self.decl.name.item)
    }
}

mod builtin {
    use std::time::{SystemTime, UNIX_EPOCH};

    use super::Callable;
    use crate::{Result, Value};

    #[derive(Copy, Clone)]
    pub struct Clock;

    impl<'a> Callable<'a> for Clock {
        fn arity(&self) -> usize {
            0
        }

        fn call(
            &self,
            _interpreter: &mut crate::Interpreter<'a>,
            _args: &[Value<'a>],
        ) -> Result<Value<'a>> {
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
