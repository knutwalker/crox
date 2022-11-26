use std::cell::{Ref, RefCell, RefMut};

use crate::Value;

#[derive(Clone, Debug, Default)]
pub struct Environment<'a> {
    names: RefCell<Vec<&'a str>>,
    values: RefCell<Vec<Value>>,
}

impl<'a> Environment<'a> {
    pub fn define(&self, name: &'a str, value: Value) {
        self.names.borrow_mut().push(name);
        self.values.borrow_mut().push(value);
    }

    pub fn assign(&self, name: &'a str, value: Value) -> Option<Value> {
        self.get_mut(name)
            .map(|mut v| std::mem::replace(&mut *v, value))
    }

    pub fn get(&self, name: &'a str) -> Option<Ref<'_, Value>> {
        self.names
            .borrow()
            .iter()
            .rposition(|&n| n == name)
            .map(|idx| Ref::map(self.values.borrow(), |v| &v[idx]))
    }

    pub fn get_mut(&self, name: &'a str) -> Option<RefMut<'_, Value>> {
        self.names
            .borrow_mut()
            .iter()
            .rposition(|&n| n == name)
            .map(|idx| RefMut::map(self.values.borrow_mut(), |v| &mut v[idx]))
    }

    pub fn push_scope(&self) -> ScopeGuard<'a, '_> {
        ScopeGuard::new(self)
    }
}

pub struct ScopeGuard<'a, 'x> {
    env: &'x Environment<'a>,
    scope: usize,
}

impl<'a, 'x> ScopeGuard<'a, 'x> {
    pub fn new(env: &'x Environment<'a>) -> Self {
        let scope = env.names.borrow().len();
        Self { env, scope }
    }
}

impl Drop for ScopeGuard<'_, '_> {
    fn drop(&mut self) {
        self.env.values.borrow_mut().truncate(self.scope);
        self.env.names.borrow_mut().truncate(self.scope);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_get_on_empty() {
        let env = Environment::default();
        assert_eq!(env.get("foo").as_deref(), None);
    }

    #[test]
    fn test_get_after_define() {
        let env = Environment::default();
        env.define("foo", Value::Number(42.0));
        assert_eq!(env.get("foo").as_deref(), Some(&Value::Number(42.0)));
    }

    #[test]
    fn test_get_mut_on_empty() {
        let env = Environment::default();
        assert_eq!(env.get_mut("foo").as_deref(), None);
    }

    #[test]
    fn test_get_mut_after_define() {
        let env = Environment::default();
        env.define("foo", Value::Number(42.0));
        assert_eq!(
            env.get_mut("foo").as_deref_mut(),
            Some(&mut Value::Number(42.0))
        );
    }

    #[test]
    fn test_assign_on_empty() {
        let env = Environment::default();
        assert_eq!(env.assign("foo", Value::Number(42.0)), None);
        assert_eq!(env.get("foo").as_deref(), None);
    }

    #[test]
    fn test_assign_after_define() {
        let env = Environment::default();
        env.define("foo", Value::Number(42.0));
        assert_eq!(
            env.assign("foo", Value::Number(24.0)),
            Some(Value::Number(42.0))
        );
        assert_eq!(env.get("foo").as_deref(), Some(&Value::Number(24.0)));
    }

    #[test]
    fn test_get_mut_after_assign() {
        let env = Environment::default();
        env.define("foo", Value::Number(42.0));
        assert_eq!(
            env.assign("foo", Value::Number(24.0)),
            Some(Value::Number(42.0))
        );
        assert_eq!(
            env.get_mut("foo").as_deref_mut(),
            Some(&mut Value::Number(24.0))
        );
    }

    #[rustfmt::skip]
    #[test]
    fn test_scope() {
        let env = Environment::default();
        env.define("foo", Value::Number(42.0));                            // var foo = 42;
                                                                           //
        let scope = env.push_scope();                                      // {
        assert_eq!(env.get("foo").as_deref(), Some(&Value::Number(42.0))); //     foo; // 42
                                                                           //
        env.define("foo", Value::Number(24.0));                            //     var foo = 24;
        assert_eq!(env.get("foo").as_deref(), Some(&Value::Number(24.0))); //     foo; // 24
                                                                           //
        env.assign("foo", Value::Number(12.0));                            //     foo = 12;
        assert_eq!(env.get("foo").as_deref(), Some(&Value::Number(12.0))); //     foo; // 12
                                                                           //
        env.define("bar", Value::Number(42.0));                            //     var bar = 42;
        assert_eq!(env.get("bar").as_deref(), Some(&Value::Number(42.0))); //     bar; // 42
                                                                           //
        drop(scope);                                                       // }
                                                                           //
        assert_eq!(env.get("foo").as_deref(), Some(&Value::Number(42.0))); // foo; // 42
        assert_eq!(env.get("bar").as_deref(), None);                       // bar; // undefined
    }
}
