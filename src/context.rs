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

    pub fn swap_env(&mut self, new_env: Environment<'source>) -> Environment<'source> {
        std::mem::replace(&mut self.env, new_env)
    }

    pub fn run_with_new_scope<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.run_with_scope(self.env.new_scope(), f)
    }

    pub fn run_with_scope<T>(
        &mut self,
        scope: Environment<'source>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let ctx_env = self.swap_env(scope);
        let guard = ScopeGuard(self, Some(ctx_env));
        f(guard.0)
    }
}

impl<'source, 'out> std::fmt::Debug for Context<'source, 'out> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Context")
            .field("env", &self.env)
            .finish_non_exhaustive()
    }
}

struct ScopeGuard<'x, 'a, 'o>(&'x mut Context<'a, 'o>, Option<Environment<'a>>);

impl Drop for ScopeGuard<'_, '_, '_> {
    fn drop(&mut self) {
        let _ = self.0.swap_env(self.1.take().expect("double drop"));
    }
}
