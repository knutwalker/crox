use std::{
    cell::{Cell, RefCell},
    fmt::Display,
    io::Write,
    rc::Rc,
};

use crate::{Builtins, CroxErrorKind, Value};

#[derive(Clone, Debug)]
pub struct Environment<'a, V = Value<'a>> {
    inner: Rc<InnerEnv<'a, V>>,
}

impl<'a, V: Clone> Environment<'a, V> {
    pub fn get<'x>(&self, name: &'x str, scope: Scope) -> Result<V, Error<'x>> {
        self.inner.get(name, scope)
    }

    pub fn assign<'x>(&self, name: &'x str, value: V, scope: Scope) -> Result<V, Error<'x>> {
        self.inner.assign(name, value, scope)
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

    pub fn define_local(&self, name: &'a str, value: impl Into<Option<V>>) -> bool {
        self.inner.define_local(name, value)
    }

    pub fn define_local_unique(
        &self,
        name: &'a str,
        value: impl Into<Option<V>>,
    ) -> Result<bool, Error<'a>> {
        self.inner.define_local_unique(name, value)
    }

    pub fn scope_of<'x>(&self, name: &'x str) -> Result<Scope, Error<'x>> {
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

impl Environment<'_> {
    pub fn print_vars(&self, out: impl Write) {
        self.inner.print_vars(out)
    }
}

impl<'a> Default for Environment<'a> {
    fn default() -> Self {
        Self {
            inner: Rc::new(InnerEnv::global(|b| b.to_value())),
        }
    }
}

impl<'a, V> Environment<'a, V> {
    pub fn global(globals: impl Fn(Builtins) -> V) -> Self {
        Self {
            inner: Rc::new(InnerEnv::global(globals)),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Error<'a> {
    Undefined(&'a str),
    Uninitialized(&'a str),
    Duplicate(&'a str),
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
            Error::Duplicate(name) => CroxErrorKind::DuplicateBinding {
                name: name.to_owned(),
            },
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Scope {
    Global,
    Local,
    Enclosing { distance: u32 },
}

impl Scope {
    fn new(scope: usize) -> Self {
        Self::Enclosing {
            distance: u32::try_from(scope).expect("Too many nested scopes"),
        }
    }

    fn scope(self) -> Option<usize> {
        match self {
            Scope::Global => None,
            Scope::Local => Some(0),
            Scope::Enclosing { distance } => Some(usize::try_from(distance).unwrap()),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Scoped {
    pub resolved: Cell<Scope>,
}

impl Scoped {
    pub fn new() -> Self {
        Self {
            resolved: Cell::new(Scope::Global),
        }
    }

    pub fn get(&self) -> Scope {
        self.resolved.get()
    }

    pub fn resolve(&self, scope: Scope) {
        self.resolved.set(scope);
    }
}

impl Default for Scoped {
    fn default() -> Self {
        Self::new()
    }
}

type Enclosing<'a, V> = Option<Rc<InnerEnv<'a, V>>>;

#[derive(Debug)]
struct InnerEnv<'a, V> {
    enclosing: Enclosing<'a, V>,
    values: RefCell<EnvValues<'a, V>>,
}

impl<'a, V> InnerEnv<'a, V> {
    fn empty() -> Self {
        Self {
            enclosing: None,
            values: RefCell::new(EnvValues::empty()),
        }
    }

    fn global(globals: impl Fn(Builtins) -> V) -> Self {
        Self {
            enclosing: None,
            values: RefCell::new(EnvValues::new(globals)),
        }
    }

    fn define(&self, name: &'a str, value: impl Into<Option<V>>) {
        self.values.borrow_mut().define(name, value);
    }

    fn define_local(&self, name: &'a str, value: impl Into<Option<V>>) -> bool {
        if self.enclosing.is_none() {
            return false;
        }
        self.define(name, value);
        true
    }

    fn define_local_unique(
        &self,
        name: &'a str,
        value: impl Into<Option<V>>,
    ) -> Result<bool, Error<'a>> {
        if self.enclosing.is_none() {
            return Ok(false);
        }
        self.values.borrow_mut().define_unique(name, value)?;
        Ok(true)
    }

    fn scope_of<'x>(&self, name: &'x str) -> Result<Scope, Error<'x>> {
        self.ancestors()
            .enumerate()
            .find_map(|(scope, this)| this.values.borrow().find(name).is_ok().then_some(scope))
            .map(Scope::new)
            .ok_or(Error::Undefined(name))
    }

    fn new_scope(self: Rc<Self>) -> Self {
        Self {
            enclosing: Some(self),
            values: RefCell::new(EnvValues::empty()),
        }
    }

    fn resolve(&self, scope: usize) -> Option<&Self> {
        self.ancestors().nth(scope)
    }

    fn ancestors(&self) -> impl Iterator<Item = &InnerEnv<'a, V>> + '_ {
        std::iter::successors(Some(self), |this| this.enclosing.as_deref())
    }
}

impl<'a, V: Clone> InnerEnv<'a, V> {
    fn get<'x>(&self, name: &'x str, scope: Scope) -> Result<V, Error<'x>> {
        match scope.scope() {
            Some(scope) => match self.resolve(scope) {
                Some(this) => this.get_local(name),
                None => Err(Error::Undefined(name)),
            },
            None => self.ancestors().last().unwrap().get_local(name),
        }
    }

    fn get_local<'x>(&self, name: &'x str) -> Result<V, Error<'x>> {
        let values = self.values.borrow();
        values.get(name).cloned()
    }

    fn assign<'x>(&self, name: &'x str, value: V, scope: Scope) -> Result<V, Error<'x>> {
        match scope.scope() {
            Some(scope) => match self.resolve(scope) {
                Some(this) => this.assign_local(name, value),
                None => Err(Error::Undefined(name)),
            },
            None => self.ancestors().last().unwrap().assign_local(name, value),
        }
    }

    fn assign_local<'x>(&self, name: &'x str, value: V) -> Result<V, Error<'x>> {
        let mut values = self.values.borrow_mut();
        values.assign(name, value).cloned()
    }
}

impl<'a, V: Display> InnerEnv<'a, V> {
    fn print_vars(&self, mut out: impl Write) {
        for this in self.ancestors() {
            this.values.borrow().print_vars(&mut out);
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

    fn new(globals: impl Fn(Builtins) -> V) -> Self {
        Self {
            names: vec![Builtins::Clock.name()],
            values: vec![Some(globals(Builtins::Clock))],
        }
    }

    fn define(&mut self, name: &'a str, value: impl Into<Option<V>>) {
        self.names.push(name);
        self.values.push(value.into());
    }

    fn define_unique(
        &mut self,
        name: &'a str,
        value: impl Into<Option<V>>,
    ) -> Result<(), Error<'a>> {
        if self.find(name).is_ok() {
            return Err(Error::Duplicate(name));
        }
        self.define(name, value);
        Ok(())
    }

    fn get<'x>(&self, name: &'x str) -> Result<&V, Error<'x>> {
        self.find(name)
            .and_then(|idx| self.values[idx].as_ref().ok_or(Error::Uninitialized(name)))
    }

    fn assign<'x>(&mut self, name: &'x str, value: V) -> Result<&V, Error<'x>> {
        self.find(name).map(|idx| &*self.values[idx].insert(value))
    }

    fn find<'x>(&self, name: &'x str) -> Result<usize, Error<'x>> {
        self.names
            .iter()
            .rposition(|&n| n == name)
            .ok_or(Error::Undefined(name))
    }
}

impl<'a, V: Display> EnvValues<'a, V> {
    fn print_vars(&self, mut out: impl Write) {
        for (name, value) in self.names.iter().zip(self.values.iter()) {
            if let Some(value) = value {
                writeln!(out, "{name} = {value}").unwrap();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;
    use Scope::*;

    #[test]
    fn test_get_on_empty() {
        let env = Environment::<()>::empty();
        assert_eq!(env.get("foo", Local), Err(Error::Undefined("foo")));
    }

    #[test]
    fn test_get_after_define() {
        let env = Environment::empty();
        env.define("foo", Value::Number(42.0));
        assert_eq!(env.get("foo", Local), Ok(Value::Number(42.0)));
    }

    #[test]
    fn test_get_on_uninitialized() {
        let env = Environment::<()>::empty();
        env.define("foo", None);
        assert_eq!(env.get("foo", Local), Err(Error::Uninitialized("foo")));
    }

    #[test]
    fn test_assign_on_empty() {
        let env = Environment::empty();
        assert_eq!(
            env.assign("foo", Value::Number(42.0), Local),
            Err(Error::Undefined("foo"))
        );
        assert_eq!(env.get("foo", Local), Err(Error::Undefined("foo")));
    }

    #[test]
    fn test_assign_after_define() {
        let env = Environment::empty();
        env.define("foo", Value::Number(42.0));
        assert_eq!(
            env.assign("foo", Value::Number(24.0), Local),
            Ok(Value::Number(24.0))
        );
        assert_eq!(env.get("foo", Local), Ok(Value::Number(24.0)));
    }

    #[test]
    fn test_assign_after_uninit() {
        let env = Environment::empty();
        env.define("foo", None);
        assert_eq!(
            env.assign("foo", Value::Number(24.0), Local),
            Ok(Value::Number(24.0))
        );
        assert_eq!(env.get("foo", Local), Ok(Value::Number(24.0)));
    }

    #[rustfmt::skip]
    #[test]
    fn test_scope() {
        let env = Environment::empty();
        env.define("foo", Value::Number(42.0));                             // var foo = 42;
                                                                            //
        let scope = env.new_scope();                                        // {
                                                                            //
        assert_eq!(scope.get("foo", Local), Err(Error::Undefined("foo")));  //     foo; // 42
        assert_eq!(scope.get("foo", Global), Ok(Value::Number(42.0)));      //     foo; // 42
                                                                            //
        scope.define("foo", Value::Number(24.0));                           //     var foo = 24;
        assert_eq!(scope.get("foo", Local), Ok(Value::Number(24.0)));       //     foo; // 24
                                                                            //
        let _ = scope.assign("foo", Value::Number(12.0), Local);            //     foo = 12;
        assert_eq!(scope.get("foo", Local), Ok(Value::Number(12.0)));       //     foo; // 12
                                                                            //
        scope.define("bar", Value::Number(42.0));                           //     var bar = 42;
        assert_eq!(scope.get("bar", Local), Ok(Value::Number(42.0)));       //     bar; // 42
                                                                            //
        drop(scope);                                                        // }
                                                                            //
        assert_eq!(env.get("foo", Local), Ok(Value::Number(42.0)));         // foo; // 42
        assert_eq!(env.get("bar", Local), Err(Error::Undefined("bar")));    // bar; // undefined
    }
}
