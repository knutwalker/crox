use std::cell::RefCell;

use crate::{Callable, Clock, CroxErrorKind, Value};

#[derive(Clone, Debug)]
pub struct Environment<'a, V = Value<'a>> {
    inner: RefCell<InnerEnvironment<'a, V>>,
}

impl<'a, V: Clone> Environment<'a, V> {
    pub fn get<'x>(&self, name: &'x str) -> Result<V, Error<'x>> {
        self.inner.borrow().get(name).cloned()
    }

    pub fn get_from_scope_ref<'x>(
        &self,
        name: &'x str,
        scope_ref: ScopeRef,
    ) -> Result<V, Error<'x>> {
        self.inner
            .borrow()
            .get_from_scope_ref(name, scope_ref)
            .cloned()
    }

    pub fn assign<'x>(&self, name: &'x str, value: V) -> Result<V, Error<'x>> {
        self.inner.borrow_mut().assign(name, value).cloned()
    }

    pub fn assign_at_scope_ref<'x>(
        &self,
        name: &'x str,
        scope_ref: ScopeRef,
        value: V,
    ) -> Result<V, Error<'x>> {
        self.inner
            .borrow_mut()
            .assign_at_scope_ref(name, scope_ref, value)
            .cloned()
    }
}

impl<'a, V> Environment<'a, V> {
    pub fn empty() -> Self {
        Self {
            inner: RefCell::new(InnerEnvironment::empty()),
        }
    }

    pub fn define(&self, name: &'a str, value: impl Into<Option<V>>) {
        self.inner.borrow_mut().define(name, value);
    }

    pub fn scope_of<'x>(&self, name: &'x str) -> Result<ScopeRef, Error<'x>> {
        self.inner.borrow().scope_of(name)
    }

    pub fn new_scope(&self) -> Scope<'a, V> {
        Scope::new(self.inner.borrow_mut().new_scope(), self)
    }

    pub fn run_with_new_scope<T>(&self, f: impl FnOnce(&Self) -> T) -> T {
        let scope = self.new_scope();
        let res = f(self);
        drop(scope);
        res
    }
}

impl Default for Environment<'_> {
    fn default() -> Self {
        Self {
            inner: RefCell::new(InnerEnvironment::new(|name| match name {
                "clock" => Clock.to_value(),
                _ => unimplemented!("builtin function {}", name),
            })),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Error<'a> {
    Undefined(&'a str),
    Uninitialized(&'a str),
}

impl<'a> From<Error<'a>> for CroxErrorKind {
    fn from(e: Error<'a>) -> Self {
        match e {
            Error::Undefined(name) => CroxErrorKind::UndefinedVariable {
                name: name.to_owned(),
            },
            Error::Uninitialized(name) => CroxErrorKind::UninitializedVariable {
                name: name.to_owned(),
            },
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct ScopeRef {
    scope: u32,
}

impl ScopeRef {
    fn new(scope: Option<usize>) -> Self {
        Self {
            scope: scope.map_or(0, |x| u32::try_from(x + 1).expect("Too many nested scopes")),
        }
    }

    fn scope(self) -> Option<usize> {
        match self.scope {
            0 => None,
            x => Some(usize::try_from(x - 1).unwrap()),
        }
    }
}

#[derive(Debug)]
pub struct Scope<'source, V> {
    scope: usize,
    env: *const Environment<'source, V>,
}

impl<'source, V> Scope<'source, V> {
    pub fn new(scope: usize, env: &Environment<'source, V>) -> Self {
        Self { env, scope }
    }
}

impl<V> Drop for Scope<'_, V> {
    fn drop(&mut self) {
        unsafe { &*self.env }
            .inner
            .borrow_mut()
            .drop_scope(self.scope);
    }
}

#[derive(Clone, Debug)]
struct InnerEnvironment<'a, V> {
    scopes: Vec<usize>,
    names: Vec<&'a str>,
    values: Vec<Option<V>>,
}

impl<'a, V> InnerEnvironment<'a, V> {
    fn empty() -> Self {
        Self {
            names: Vec::new(),
            values: Vec::new(),
            scopes: Vec::new(),
        }
    }

    fn new(globals: impl Fn(&'static str) -> V) -> Self {
        Self {
            scopes: Vec::new(),
            names: vec!["clock"],
            values: vec![Some(globals("clock"))],
        }
    }

    fn define(&mut self, name: &'a str, value: impl Into<Option<V>>) {
        self.names.push(name);
        self.values.push(value.into());
    }

    fn get<'x>(&self, name: &'x str) -> Result<&V, Error<'x>> {
        self.find(name, ..)
            .and_then(|idx| self.values[idx].as_ref().ok_or(Error::Uninitialized(name)))
    }

    fn assign<'x>(&mut self, name: &'x str, value: V) -> Result<&V, Error<'x>> {
        self.find(name, ..)
            .map(|idx| &*self.values[idx].insert(value))
    }

    fn get_from_scope_ref<'x>(&self, name: &'x str, scope_ref: ScopeRef) -> Result<&V, Error<'x>> {
        let range = self.resolve_scope(scope_ref);
        self.find(name, range)
            .and_then(|idx| self.values[idx].as_ref().ok_or(Error::Uninitialized(name)))
    }

    fn assign_at_scope_ref<'x>(
        &mut self,
        name: &'x str,
        scope_ref: ScopeRef,
        value: V,
    ) -> Result<&V, Error<'x>> {
        let range = self.resolve_scope(scope_ref);
        self.find(name, range)
            .map(|idx| &*self.values[idx].insert(value))
    }

    fn resolve_scope(&self, scope_ref: ScopeRef) -> std::ops::Range<usize> {
        let end = self.names.len();
        let range = match scope_ref.scope() {
            Some(idx) => self.scopes[idx]..self.scopes.get(idx + 1).copied().unwrap_or(end),
            None => 0..self.scopes.first().copied().unwrap_or(end),
        };
        range
    }

    fn scope_of<'x>(&self, name: &'x str) -> Result<ScopeRef, Error<'x>> {
        let pos = self.find(name, ..)?;
        Ok(ScopeRef::new(
            self.scopes.iter().rposition(|scp| *scp <= pos),
        ))
    }

    fn find<'x, R>(&self, name: &'x str, range: R) -> Result<usize, Error<'x>>
    where
        R: std::ops::RangeBounds<usize> + std::slice::SliceIndex<[&'a str], Output = [&'a str]>,
    {
        let offset = match range.start_bound() {
            std::ops::Bound::Included(x) => *x,
            std::ops::Bound::Excluded(x) => *x + 1,
            std::ops::Bound::Unbounded => 0,
        };

        self.names[range]
            .iter()
            .rposition(|&n| n == name)
            .map(|pos| pos + offset)
            .ok_or(Error::Undefined(name))
    }

    fn new_scope(&mut self) -> usize {
        let value = self.names.len();
        let scope = self.scopes.len();
        self.scopes.push(value);
        scope
    }

    fn drop_scope(&mut self, scope: usize) {
        for scope in self.scopes.drain(scope..).rev() {
            self.names.truncate(scope);
            self.values.truncate(scope);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_get_on_empty() {
        let env = Environment::default();
        assert_eq!(env.get("foo"), Err(Error::Undefined("foo")));
    }

    #[test]
    fn test_get_after_define() {
        let env = Environment::default();
        env.define("foo", Value::Number(42.0));
        assert_eq!(env.get("foo"), Ok(Value::Number(42.0)));
    }

    #[test]
    fn test_get_on_uninitialized() {
        let env = Environment::default();
        env.define("foo", None);
        assert_eq!(env.get("foo"), Err(Error::Uninitialized("foo")));
    }

    #[test]
    fn test_assign_on_empty() {
        let env = Environment::default();
        assert_eq!(
            env.assign("foo", Value::Number(42.0)),
            Err(Error::Undefined("foo"))
        );
        assert_eq!(env.get("foo"), Err(Error::Undefined("foo")));
    }

    #[test]
    fn test_assign_after_define() {
        let env = Environment::default();
        env.define("foo", Value::Number(42.0));
        assert_eq!(
            env.assign("foo", Value::Number(24.0)),
            Ok(Value::Number(24.0))
        );
        assert_eq!(env.get("foo"), Ok(Value::Number(24.0)));
    }

    #[test]
    fn test_assign_after_uninit() {
        let env = Environment::default();
        env.define("foo", None);
        assert_eq!(
            env.assign("foo", Value::Number(24.0)),
            Ok(Value::Number(24.0))
        );
        assert_eq!(env.get("foo"), Ok(Value::Number(24.0)));
    }

    #[rustfmt::skip]
    #[test]
    fn test_scope() {
        let env = Environment::default();
        env.define("foo", Value::Number(42.0));                   // var foo = 42;
                                                                  //
        let scope = env.new_scope();                              // {
                                                                  //
        assert_eq!(env.get("foo"), Ok(Value::Number(42.0)));      //     foo; // 42
                                                                  //
        env.define("foo", Value::Number(24.0));                   //     var foo = 24;
        assert_eq!(env.get("foo"), Ok(Value::Number(24.0)));      //     foo; // 24
                                                                  //
        let _ = env.assign("foo", Value::Number(12.0));           //     foo = 12;
        assert_eq!(env.get("foo"), Ok(Value::Number(12.0)));      //     foo; // 12
                                                                  //
        env.define("bar", Value::Number(42.0));                   //     var bar = 42;
        assert_eq!(env.get("bar"), Ok(Value::Number(42.0)));      //     bar; // 42
                                                                  //
        drop(scope);                                              // }
                                                                  //
        assert_eq!(env.get("foo"), Ok(Value::Number(42.0)));      // foo; // 42
        assert_eq!(env.get("bar"), Err(Error::Undefined("bar"))); // bar; // undefined
    }
}
