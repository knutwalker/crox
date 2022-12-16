use crate::{Result, Value};
pub use builtin::Clock;

pub trait Callable: std::fmt::Debug + std::any::Any + Send + Sync {
    fn arity(&self) -> usize;
    fn call(&self, args: &[Value]) -> Result<Value>;

    fn to_value(self) -> Value
    where
        Self: Sized + 'static,
    {
        Value::Fn(std::rc::Rc::new(self))
    }
}

mod builtin {
    use std::time::{SystemTime, UNIX_EPOCH};

    use super::Callable;
    use crate::{Result, Value};

    #[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
    pub struct Clock;

    impl Callable for Clock {
        fn arity(&self) -> usize {
            0
        }

        fn call(&self, _args: &[Value]) -> Result<Value> {
            Ok(SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map_or(0.0, |d| d.as_secs_f64())
                .into())
        }
    }
}
