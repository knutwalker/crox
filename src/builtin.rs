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

    pub fn to_value<'a>(self) -> Value<'a> {
        match self {
            Self::Clock => Clock.to_value(),
        }
    }
}

#[derive(Copy, Clone)]
pub struct Clock;

impl<'a> Callable<'a> for Clock {
    fn arity(&self) -> usize {
        0
    }

    fn call(
        &self,
        _ctx: &mut InterpreterContext<'a, '_>,
        _args: &[Value<'a>],
        _span: Span,
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
