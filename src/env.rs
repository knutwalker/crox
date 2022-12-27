use std::cell::RefCell;

use crate::{Callable, Clock, CroxErrorKind, Value};

#[derive(Clone, Debug, Default)]
pub struct Environment<'a> {
    inner: RefCell<InnerEnvironment<'a>>,
}

impl<'a> Environment<'a> {
    pub fn define(&self, name: &'a str, value: impl Into<Option<Value<'a>>>) {
        self.inner.borrow_mut().define(name, value);
    }

    pub fn assign(&self, name: &'a str, value: Value<'a>) -> Result<Value<'a>, Error<'a>> {
        self.inner.borrow_mut().assign(name, value).cloned()
    }

    pub fn get(&self, name: &'a str) -> Result<Value<'a>, Error<'a>> {
        self.inner.borrow().get(name).cloned()
    }

    pub fn new_scope(&self) -> Scope {
        self.inner.borrow_mut().new_scope()
    }

    pub fn drop_scope(&self, scope: Scope) {
        self.inner.borrow_mut().drop_scope(scope);
    }

    pub fn run_with_new_scope<T>(&self, f: impl FnOnce(&Self) -> T) -> T {
        let scope = self.new_scope();
        let res = f(self);
        self.drop_scope(scope);
        res
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

#[derive(Debug)]
pub struct Scope {
    scope: usize,
    dropped: bool,
}

impl Scope {
    fn new(scope: usize) -> Self {
        Scope {
            scope,
            dropped: false,
        }
    }

    pub fn stop(self, env: &mut Environment<'_>) {
        env.drop_scope(self);
    }
}

impl Drop for Scope {
    fn drop(&mut self) {
        #[cfg(debug_assertions)]
        if !self.dropped {
            panic!("Scope was not stopped");
        }
    }
}

#[derive(Clone, Debug)]
struct InnerEnvironment<'a> {
    names: Vec<&'a str>,
    values: Vec<Option<Value<'a>>>,
}

impl<'a> Default for InnerEnvironment<'a> {
    fn default() -> Self {
        Self {
            names: vec!["clock"],
            values: vec![Some(Clock.to_value())],
        }
    }
}

impl<'a> InnerEnvironment<'a> {
    fn define(&mut self, name: &'a str, value: impl Into<Option<Value<'a>>>) {
        self.names.push(name);
        self.values.push(value.into());
    }

    fn assign(&mut self, name: &'a str, value: Value<'a>) -> Result<&Value<'a>, Error<'a>> {
        self.find(name).map(|idx| &*self.values[idx].insert(value))
    }

    fn get(&self, name: &'a str) -> Result<&Value<'a>, Error<'a>> {
        self.find(name)
            .and_then(|idx| self.values[idx].as_ref().ok_or(Error::Uninitialized(name)))
    }

    fn find(&self, name: &'a str) -> Result<usize, Error<'a>> {
        self.names
            .iter()
            .rposition(|&n| n == name)
            .ok_or(Error::Undefined(name))
    }

    fn new_scope(&self) -> Scope {
        let scope = self.names.len();
        Scope::new(scope)
    }

    fn drop_scope(&mut self, mut scope: Scope) {
        scope.dropped = true;
        let scope = scope.scope;
        self.names.truncate(scope);
        self.values.truncate(scope);
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
        assert_eq!(env.get("foo"), Ok(Value::Number(42.0)));     //     foo; // 42
                                                                  //
        env.define("foo", Value::Number(24.0));                   //     var foo = 24;
        assert_eq!(env.get("foo"), Ok(Value::Number(24.0)));     //     foo; // 24
                                                                  //
        let _ = env.assign("foo", Value::Number(12.0));           //     foo = 12;
        assert_eq!(env.get("foo"), Ok(Value::Number(12.0)));     //     foo; // 12
                                                                  //
        env.define("bar", Value::Number(42.0));                   //     var bar = 42;
        assert_eq!(env.get("bar"), Ok(Value::Number(42.0)));     //     bar; // 42
                                                                  //
        env.drop_scope(scope);                                    // }
                                                                  //
        assert_eq!(env.get("foo"), Ok(Value::Number(42.0)));     // foo; // 42
        assert_eq!(env.get("bar"), Err(Error::Undefined("bar"))); // bar; // undefined
    }
}
