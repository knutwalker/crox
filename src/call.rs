use crate::{Result, Value};

pub trait Callable: std::fmt::Debug + std::any::Any + Send + Sync {
    fn arity(&self) -> usize;
    fn call(&self, args: &[Value]) -> Result<Value>;
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct Clock;

impl Callable for Clock {
    fn arity(&self) -> usize {
        0
    }

    fn call(&self, _args: &[Value]) -> Result<Value> {
        Ok(std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0.0, |d| d.as_secs_f64())
            .into())
    }
}

impl Clock {
    pub(crate) fn to_value(self) -> Value {
        Value::Fn(std::rc::Rc::new(self))
    }
}
