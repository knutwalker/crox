use std::time::{SystemTime, UNIX_EPOCH};

use crate::{Result, Value};

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Builtins {
    Clock,
}

impl Builtins {
    pub fn name(self) -> &'static str {
        match self {
            Self::Clock => "clock",
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            Builtins::Clock => 0,
        }
    }

    pub fn call<'env>(&self) -> Result<Value<'env>> {
        match self {
            Builtins::Clock => Ok(SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map_or(0.0, |d| d.as_secs_f64())
                .into()),
        }
    }

    pub fn to_value<'env>(self) -> Value<'env> {
        Value::Builtin(self)
    }
}

impl std::fmt::Debug for Builtins {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Clock => {
                write!(f, "<builtin clock>")
            }
        }
    }
}
