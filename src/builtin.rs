use std::time::{SystemTime, UNIX_EPOCH};

use super::Callable;
use crate::{InterpreterContext, Result, Span, Value};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Builtins {
    Clock,
}

impl Builtins {
    pub fn name(self) -> &'static str {
        match self {
            Self::Clock => "clock",
        }
    }

    pub fn to_value<'env>(self) -> Value<'env> {
        match self {
            Self::Clock => Clock.to_value(),
        }
    }
}

#[derive(Copy, Clone)]
pub struct Clock;

impl<'env> Callable<'env> for Clock {
    fn arity(&self) -> usize {
        0
    }

    fn call(
        &self,
        _ctx: &mut InterpreterContext<'env, '_>,
        _args: &[Value<'env>],
        _span: Span,
    ) -> Result<Value<'env>> {
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
