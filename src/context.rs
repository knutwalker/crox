use std::{
    fmt::Debug,
    io::Write,
    ops::{Deref, DerefMut},
};

use crate::{Bump, Environment, Value};

pub type InterpreterContext<'a, 'out> = Context<'a, &'out mut dyn Write>;

pub struct Context<'source, Data, V = Value<'source>> {
    pub env: Environment<'source, V>,
    pub arena: &'source Bump,
    pub data: Data,
}

impl<'source, Data, V> Context<'source, Data, V> {
    pub fn new(env: Environment<'source, V>, arena: &'source Bump, data: Data) -> Self {
        Self { env, arena, data }
    }

    pub fn run_with_new_scope<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.run_with_scope(self.env.new_scope(), f)
    }

    pub fn run_with_scope<T>(
        &mut self,
        scope: Environment<'source, V>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let guard = self.swap_env(scope);
        f(guard.0)
    }

    pub fn swap_data(&mut self, new_data: Data) -> SwapGuard<'_, 'source, Data, V> {
        let old_data = std::mem::replace(&mut self.data, new_data);
        SwapGuard(self, Some(Field::Data(old_data)))
    }

    pub fn swap_env(
        &mut self,
        new_env: Environment<'source, V>,
    ) -> SwapGuard<'_, 'source, Data, V> {
        let old_env = std::mem::replace(&mut self.env, new_env);
        SwapGuard(self, Some(Field::Env(old_env)))
    }
}

impl<'source, 'out> InterpreterContext<'source, 'out> {
    pub fn alloc<T>(&self, value: T) -> &'source T {
        self.arena.alloc(value)
    }
    pub fn alloc_mut<T>(&self, value: T) -> &'source mut T {
        self.arena.alloc(value)
    }
}

impl<'source, Data, V: Debug> Debug for Context<'source, Data, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Context")
            .field("env", &self.env)
            .finish_non_exhaustive()
    }
}

pub struct SwapGuard<'this, 'source, Data, V>(
    &'this mut Context<'source, Data, V>,
    Option<Field<'source, Data, V>>,
);

impl<Data, V> Drop for SwapGuard<'_, '_, Data, V> {
    fn drop(&mut self) {
        match self.1.take().expect("double drop") {
            Field::Env(env) => self.0.env = env,
            Field::Data(data) => self.0.data = data,
        }
    }
}

impl<'this, 'source, Data, V> Deref for SwapGuard<'this, 'source, Data, V> {
    type Target = Context<'source, Data, V>;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<'this, 'source, Data, V> DerefMut for SwapGuard<'this, 'source, Data, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0
    }
}

enum Field<'source, Data, V> {
    Env(Environment<'source, V>),
    Data(Data),
}
