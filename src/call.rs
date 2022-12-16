use crate::{Interpreter, Result, Value};
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
