use std::{cell::RefCell, rc::Rc};

use crate::{Callable, Clock, CroxErrorKind, Value};

#[derive(Clone, Debug)]
pub struct Environment<'a, V = Value<'a>> {
    inner: Rc<InnerEnv<'a, V>>,
}

impl<'a, V: Clone> Environment<'a, V> {
    pub fn get<'x>(&self, name: &'x str) -> Result<V, Error<'x>> {
        self.inner.get(name)
    }

    pub fn get_from_scope_ref<'x>(
        &self,
        name: &'x str,
        scope_ref: ScopeRef,
    ) -> Result<V, Error<'x>> {
        self.inner.get_from_scope_ref(name, scope_ref)
    }

    pub fn assign<'x>(&self, name: &'x str, value: V) -> Result<V, Error<'x>> {
        self.inner.assign(name, value)
    }

    pub fn assign_at_scope_ref<'x>(
        &self,
        name: &'x str,
        scope_ref: ScopeRef,
        value: V,
    ) -> Result<V, Error<'x>> {
        self.inner.assign_at_scope_ref(name, scope_ref, value)
    }
}

impl<'a, V> Environment<'a, V> {
    pub fn empty() -> Self {
        Self {
            inner: Rc::new(InnerEnv::empty()),
        }
    }

    pub fn define(&self, name: &'a str, value: impl Into<Option<V>>) {
        self.inner.define(name, value);
    }

    pub fn scope_of<'x>(&self, name: &'x str) -> Result<ScopeRef, Error<'x>> {
        self.inner.scope_of(name)
    }

    #[must_use]
    pub fn new_scope(&self) -> Self {
        let scope = InnerEnv::new_scope(Rc::clone(&self.inner));
        Self {
            inner: Rc::new(scope),
        }
    }

    pub fn run_with_new_scope<T>(&self, f: impl FnOnce(&Self) -> T) -> T {
        let scope = self.new_scope();
        f(&scope)
    }
}

impl<'a> Environment<'a> {
    pub fn global() -> Self {
        Self {
            inner: Rc::new(InnerEnv::global()),
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
    fn new(scope: usize) -> Self {
        Self {
            scope: u32::try_from(scope).expect("Too many nested scopes"),
        }
    }

    fn scope(self) -> usize {
        usize::try_from(self.scope).unwrap()
    }
}

type Enclosing<'a, V> = Option<Rc<InnerEnv<'a, V>>>;

#[derive(Debug)]
struct InnerEnv<'a, V> {
    enclosing: Enclosing<'a, V>,
    values: RefCell<EnvValues<'a, V>>,
}

impl<'a> InnerEnv<'a, Value<'a>> {
    fn global() -> Self {
        Self {
            enclosing: None,
            values: RefCell::new(EnvValues::new(|name| match name {
                "clock" => Clock.to_value(),
                _ => unimplemented!("builtin function {}", name),
            })),
        }
    }
}

impl<'a, V> InnerEnv<'a, V> {
    fn empty() -> Self {
        Self {
            enclosing: None,
            values: RefCell::new(EnvValues::empty()),
        }
    }

    fn define(&self, name: &'a str, value: impl Into<Option<V>>) {
        self.values.borrow_mut().define(name, value);
    }

    fn scope_of<'x>(&self, name: &'x str) -> Result<ScopeRef, Error<'x>> {
        self.ancestors()
            .enumerate()
            .find_map(|(scope, this)| this.values.borrow().find(name).is_ok().then_some(scope))
            .map(ScopeRef::new)
            .ok_or(Error::Undefined(name))
    }

    fn new_scope(self: Rc<Self>) -> Self {
        Self {
            enclosing: Some(self),
            values: RefCell::new(EnvValues::empty()),
        }
    }

    fn resolve(&self, scope: ScopeRef) -> Option<&Self> {
        self.ancestors().nth(scope.scope())
    }

    fn ancestors(&self) -> impl Iterator<Item = &InnerEnv<'a, V>> + '_ {
        std::iter::successors(Some(self), |this| this.enclosing.as_deref())
    }
}

impl<'a, V: Clone> InnerEnv<'a, V> {
    fn get<'x>(&self, name: &'x str) -> Result<V, Error<'x>> {
        let mut this = self;
        loop {
            let values = this.values.borrow();
            match values.get(name) {
                Ok(val) => return Ok(val.clone()),
                Err(e @ Error::Undefined(_)) => match &this.enclosing {
                    Some(parent) => this = parent,
                    None => return Err(e),
                },
                Err(e) => return Err(e),
            }
        }
    }

    fn get_from_scope_ref<'x>(&self, name: &'x str, scope_ref: ScopeRef) -> Result<V, Error<'x>> {
        match self.resolve(scope_ref) {
            Some(this) => this.get(name),
            None => Err(Error::Undefined(name)),
        }
    }

    fn assign<'x>(&self, name: &'x str, mut value: V) -> Result<V, Error<'x>> {
        let mut this = self;
        loop {
            let mut values = this.values.borrow_mut();
            match values.assign(name, value) {
                Ok(assigned) => return Ok(assigned.clone()),
                Err(v) => {
                    value = v;
                    match &this.enclosing {
                        Some(parent) => this = parent,
                        None => return Err(Error::Undefined(name)),
                    }
                }
            }
        }
    }

    fn assign_at_scope_ref<'x>(
        &self,
        name: &'x str,
        scope_ref: ScopeRef,
        value: V,
    ) -> Result<V, Error<'x>> {
        match self.resolve(scope_ref) {
            Some(this) => this.assign(name, value),
            None => Err(Error::Undefined(name)),
        }
    }
}

#[derive(Clone, Debug)]
struct EnvValues<'a, V> {
    names: Vec<&'a str>,
    values: Vec<Option<V>>,
}

impl<'a, V> EnvValues<'a, V> {
    fn empty() -> Self {
        Self {
            names: Vec::new(),
            values: Vec::new(),
        }
    }

    fn new(globals: impl Fn(&'static str) -> V) -> Self {
        Self {
            names: vec!["clock"],
            values: vec![Some(globals("clock"))],
        }
    }

    fn define(&mut self, name: &'a str, value: impl Into<Option<V>>) {
        self.names.push(name);
        self.values.push(value.into());
    }

    fn get<'x>(&self, name: &'x str) -> Result<&V, Error<'x>> {
        self.find(name)
            .and_then(|idx| self.values[idx].as_ref().ok_or(Error::Uninitialized(name)))
    }

    fn assign<'x>(&mut self, name: &'x str, value: V) -> Result<&V, V> {
        match self.find(name) {
            Ok(idx) => Ok(&*self.values[idx].insert(value)),
            Err(_) => Err(value),
        }
    }

    fn find<'x>(&self, name: &'x str) -> Result<usize, Error<'x>> {
        self.names
            .iter()
            .rposition(|&n| n == name)
            .ok_or(Error::Undefined(name))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_get_on_empty() {
        let env = Environment::<()>::empty();
        assert_eq!(env.get("foo"), Err(Error::Undefined("foo")));
    }

    #[test]
    fn test_get_after_define() {
        let env = Environment::empty();
        env.define("foo", Value::Number(42.0));
        assert_eq!(env.get("foo"), Ok(Value::Number(42.0)));
    }

    #[test]
    fn test_get_on_uninitialized() {
        let env = Environment::<()>::empty();
        env.define("foo", None);
        assert_eq!(env.get("foo"), Err(Error::Uninitialized("foo")));
    }

    #[test]
    fn test_assign_on_empty() {
        let env = Environment::empty();
        assert_eq!(
            env.assign("foo", Value::Number(42.0)),
            Err(Error::Undefined("foo"))
        );
        assert_eq!(env.get("foo"), Err(Error::Undefined("foo")));
    }

    #[test]
    fn test_assign_after_define() {
        let env = Environment::empty();
        env.define("foo", Value::Number(42.0));
        assert_eq!(
            env.assign("foo", Value::Number(24.0)),
            Ok(Value::Number(24.0))
        );
        assert_eq!(env.get("foo"), Ok(Value::Number(24.0)));
    }

    #[test]
    fn test_assign_after_uninit() {
        let env = Environment::empty();
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
        let env = Environment::empty();
        env.define("foo", Value::Number(42.0));                   // var foo = 42;
                                                                  //
        let scope = env.new_scope();                              // {
                                                                  //
        assert_eq!(scope.get("foo"), Ok(Value::Number(42.0)));    //     foo; // 42
                                                                  //
        scope.define("foo", Value::Number(24.0));                 //     var foo = 24;
        assert_eq!(scope.get("foo"), Ok(Value::Number(24.0)));    //     foo; // 24
                                                                  //
        let _ = scope.assign("foo", Value::Number(12.0));         //     foo = 12;
        assert_eq!(scope.get("foo"), Ok(Value::Number(12.0)));    //     foo; // 12
                                                                  //
        scope.define("bar", Value::Number(42.0));                 //     var bar = 42;
        assert_eq!(scope.get("bar"), Ok(Value::Number(42.0)));    //     bar; // 42
                                                                  //
        drop(scope);                                              // }
                                                                  //
        assert_eq!(env.get("foo"), Ok(Value::Number(42.0)));      // foo; // 42
        assert_eq!(env.get("bar"), Err(Error::Undefined("bar"))); // bar; // undefined
    }
}
