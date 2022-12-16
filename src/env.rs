use crate::{Callable, Clock, CroxErrorKind, Value};

#[derive(Clone, Debug)]
pub struct Environment<'a> {
    names: Vec<&'a str>,
    values: Vec<Option<Value<'a>>>,
}

impl<'a> Default for Environment<'a> {
    fn default() -> Self {
        Self {
            names: vec!["clock"],
            values: vec![Some(Clock.to_value())],
        }
    }
}

impl<'a> Environment<'a> {
    pub fn define(&mut self, name: &'a str, value: impl Into<Option<Value<'a>>>) {
        self.names.push(name);
        self.values.push(value.into());
    }

    pub fn assign(&mut self, name: &'a str, value: Value<'a>) -> Result<&Value<'a>, Error<'a>> {
        self.find(name).map(|idx| &*self.values[idx].insert(value))
    }

    pub fn get(&self, name: &'a str) -> Result<&Value<'a>, Error<'a>> {
        self.find(name)
            .and_then(|idx| self.values[idx].as_ref().ok_or(Error::Uninitialized(name)))
    }

    pub fn get_mut(&mut self, name: &'a str) -> Result<&mut Value<'a>, Error<'a>> {
        self.find(name)
            .and_then(|idx| self.values[idx].as_mut().ok_or(Error::Uninitialized(name)))
    }

    pub fn new_scope(&self) -> Scope {
        let scope = self.names.len();
        Scope::new(scope)
    }

    pub fn drop_scope(&mut self, mut scope: Scope) {
        scope.dropped = true;
        let scope = scope.scope;
        self.names.truncate(scope);
        self.values.truncate(scope);
    }

    fn find(&self, name: &'a str) -> Result<usize, Error<'a>> {
        self.names
            .iter()
            .rposition(|&n| n == name)
            .ok_or(Error::Undefined(name))
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
        let mut env = Environment::default();
        env.define("foo", Value::Number(42.0));
        assert_eq!(env.get("foo"), Ok(&Value::Number(42.0)));
    }

    #[test]
    fn test_get_on_uninitialized() {
        let mut env = Environment::default();
        env.define("foo", None);
        assert_eq!(env.get("foo"), Err(Error::Uninitialized("foo")));
    }

    #[test]
    fn test_get_mut_on_empty() {
        let mut env = Environment::default();
        assert_eq!(env.get_mut("foo"), Err(Error::Undefined("foo")));
    }

    #[test]
    fn test_get_mut_after_define() {
        let mut env = Environment::default();
        env.define("foo", Value::Number(42.0));
        assert_eq!(env.get_mut("foo"), Ok(&mut Value::Number(42.0)));
    }

    #[test]
    fn test_get_mut_on_uninitialized() {
        let mut env = Environment::default();
        env.define("foo", None);
        assert_eq!(env.get_mut("foo"), Err(Error::Uninitialized("foo")));
    }

    #[test]
    fn test_assign_on_empty() {
        let mut env = Environment::default();
        assert_eq!(
            env.assign("foo", Value::Number(42.0)),
            Err(Error::Undefined("foo"))
        );
        assert_eq!(env.get("foo"), Err(Error::Undefined("foo")));
    }

    #[test]
    fn test_assign_after_define() {
        let mut env = Environment::default();
        env.define("foo", Value::Number(42.0));
        assert_eq!(
            env.assign("foo", Value::Number(24.0)),
            Ok(&Value::Number(24.0))
        );
        assert_eq!(env.get("foo"), Ok(&Value::Number(24.0)));
    }

    #[test]
    fn test_assign_after_uninit() {
        let mut env = Environment::default();
        env.define("foo", None);
        assert_eq!(
            env.assign("foo", Value::Number(24.0)),
            Ok(&Value::Number(24.0))
        );
        assert_eq!(env.get("foo"), Ok(&Value::Number(24.0)));
    }

    #[test]
    fn test_get_mut_after_assign() {
        let mut env = Environment::default();
        env.define("foo", Value::Number(42.0));
        assert_eq!(
            env.assign("foo", Value::Number(24.0)),
            Ok(&Value::Number(24.0))
        );
        assert_eq!(env.get_mut("foo"), Ok(&mut Value::Number(24.0)));
    }

    #[rustfmt::skip]
    #[test]
    fn test_scope() {
        let mut env = Environment::default();
        env.define("foo", Value::Number(42.0));                   // var foo = 42;
                                                                  //
        let scope = env.new_scope();                              // {
                                                                  //
        assert_eq!(env.get("foo"), Ok(&Value::Number(42.0)));     //     foo; // 42
                                                                  //
        env.define("foo", Value::Number(24.0));                   //     var foo = 24;
        assert_eq!(env.get("foo"), Ok(&Value::Number(24.0)));     //     foo; // 24
                                                                  //
        let _ = env.assign("foo", Value::Number(12.0));           //     foo = 12;
        assert_eq!(env.get("foo"), Ok(&Value::Number(12.0)));     //     foo; // 12
                                                                  //
        env.define("bar", Value::Number(42.0));                   //     var bar = 42;
        assert_eq!(env.get("bar"), Ok(&Value::Number(42.0)));     //     bar; // 42
                                                                  //
        env.drop_scope(scope);                                    // }
                                                                  //
        assert_eq!(env.get("foo"), Ok(&Value::Number(42.0)));     // foo; // 42
        assert_eq!(env.get("bar"), Err(Error::Undefined("bar"))); // bar; // undefined
    }
}
