use std::io::Write;

use crate::Environment;

pub struct Context<'source, 'out> {
    pub env: Environment<'source>,
    pub out: &'out mut dyn Write,
}

impl<'source, 'out> Context<'source, 'out> {
    pub fn new(env: Environment<'source>, out: &'out mut dyn Write) -> Self {
        Self { env, out }
    }
}

impl<'source, 'out> std::fmt::Debug for Context<'source, 'out> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Context")
            .field("env", &self.env)
            .finish_non_exhaustive()
    }
}
