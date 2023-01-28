use std::{
    fmt::Debug,
    io::Write,
    ops::{Deref, DerefMut},
};

use crate::{Bump, Environment, Value};

pub type InterpreterContext<'env, 'out> = Context<'env, &'out mut dyn Write>;

pub struct Context<'env, Data, V = Value<'env>> {
    pub env: Environment<'env, V>,
    pub arena: &'env Bump,
    pub data: Data,
}

impl<'env, Data, V> Context<'env, Data, V> {
    pub fn new(env: Environment<'env, V>, arena: &'env Bump, data: Data) -> Self {
        Self { env, arena, data }
    }

    pub fn run_with_new_scope<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.run_with_scope(self.env.new_scope(), f)
    }

    pub fn run_with_scope<T>(
        &mut self,
        scope: Environment<'env, V>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let guard = self.swap_env(scope);
        f(guard.0)
    }

    pub fn swap_data(&mut self, new_data: Data) -> SwapGuard<'_, 'env, Data, V> {
        let old_data = std::mem::replace(&mut self.data, new_data);
        SwapGuard(self, Some(Field::Data(old_data)))
    }

    pub fn swap_env(&mut self, new_env: Environment<'env, V>) -> SwapGuard<'_, 'env, Data, V> {
        let old_env = std::mem::replace(&mut self.env, new_env);
        SwapGuard(self, Some(Field::Env(old_env)))
    }
}

impl<'env, 'out> InterpreterContext<'env, 'out> {
    pub fn alloc<T>(&self, value: T) -> &'env T {
        self.arena.alloc(value)
    }

    pub fn alloc_mut<T>(&self, value: T) -> &'env mut T {
        self.arena.alloc(value)
    }
}

impl<'env, Data, V: Debug> Debug for Context<'env, Data, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Context")
            .field("env", &self.env)
            .finish_non_exhaustive()
    }
}

pub struct SwapGuard<'this, 'env, Data, V>(
    &'this mut Context<'env, Data, V>,
    Option<Field<'env, Data, V>>,
);

impl<Data, V> Drop for SwapGuard<'_, '_, Data, V> {
    fn drop(&mut self) {
        match self.1.take().expect("double drop") {
            Field::Env(env) => self.0.env = env,
            Field::Data(data) => self.0.data = data,
        }
    }
}

impl<'this, 'env, Data, V> Deref for SwapGuard<'this, 'env, Data, V> {
    type Target = Context<'env, Data, V>;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<'this, 'env, Data, V> DerefMut for SwapGuard<'this, 'env, Data, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0
    }
}

enum Field<'env, Data, V> {
    Env(Environment<'env, V>),
    Data(Data),
}
