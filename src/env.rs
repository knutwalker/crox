use crate::Value;

#[derive(Clone, Debug, Default)]
pub struct Environment<'a> {
    names: Vec<&'a str>,
    values: Vec<Value>,
}

impl<'a> Environment<'a> {
    pub fn define(&mut self, name: &'a str, value: Value) {
        self.names.push(name);
        self.values.push(value);
    }

    pub fn assign(&mut self, name: &'a str, value: Value) -> Option<Value> {
        self.get_mut(name).map(|v| std::mem::replace(v, value))
    }

    pub fn get(&self, name: &'a str) -> Option<&Value> {
        self.names
            .iter()
            .rposition(|&n| n == name)
            .map(|idx| &self.values[idx])
    }

    pub fn get_mut(&mut self, name: &'a str) -> Option<&mut Value> {
        self.names
            .iter()
            .rposition(|&n| n == name)
            .map(|idx| &mut self.values[idx])
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

    pub fn stop(self, env: &mut Environment) {
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
        assert_eq!(env.get("foo"), None);
    }

    #[test]
    fn test_get_after_define() {
        let mut env = Environment::default();
        env.define("foo", Value::Number(42.0));
        assert_eq!(env.get("foo"), Some(&Value::Number(42.0)));
    }

    #[test]
    fn test_get_mut_on_empty() {
        let mut env = Environment::default();
        assert_eq!(env.get_mut("foo"), None);
    }

    #[test]
    fn test_get_mut_after_define() {
        let mut env = Environment::default();
        env.define("foo", Value::Number(42.0));
        assert_eq!(env.get_mut("foo"), Some(&mut Value::Number(42.0)));
    }

    #[test]
    fn test_assign_on_empty() {
        let mut env = Environment::default();
        assert_eq!(env.assign("foo", Value::Number(42.0)), None);
        assert_eq!(env.get("foo"), None);
    }

    #[test]
    fn test_assign_after_define() {
        let mut env = Environment::default();
        env.define("foo", Value::Number(42.0));
        assert_eq!(
            env.assign("foo", Value::Number(24.0)),
            Some(Value::Number(42.0))
        );
        assert_eq!(env.get("foo"), Some(&Value::Number(24.0)));
    }

    #[test]
    fn test_get_mut_after_assign() {
        let mut env = Environment::default();
        env.define("foo", Value::Number(42.0));
        assert_eq!(
            env.assign("foo", Value::Number(24.0)),
            Some(Value::Number(42.0))
        );
        assert_eq!(env.get_mut("foo"), Some(&mut Value::Number(24.0)));
    }

    #[rustfmt::skip]
    #[test]
    fn test_scope() {
        let mut env = Environment::default();
        env.define("foo", Value::Number(42.0));                   // var foo = 42;
                                                                  //
        let scope = env.new_scope();                              // {
                                                                  //
        assert_eq!(env.get("foo"), Some(&Value::Number(42.0)));   //     foo; // 42
                                                                  //
        env.define("foo", Value::Number(24.0));                   //     var foo = 24;
        assert_eq!(env.get("foo"), Some(&Value::Number(24.0)));   //     foo; // 24
                                                                  //
        let _ = env.assign("foo", Value::Number(12.0));           //     foo = 12;
        assert_eq!(env.get("foo"), Some(&Value::Number(12.0)));   //     foo; // 12
                                                                  //
        env.define("bar", Value::Number(42.0));                   //     var bar = 42;
        assert_eq!(env.get("bar"), Some(&Value::Number(42.0)));   //     bar; // 42
                                                                  //
        env.drop_scope(scope);                                    // }
                                                                  //
        assert_eq!(env.get("foo"), Some(&Value::Number(42.0)));   // foo; // 42
        assert_eq!(env.get("bar"), None);                         // bar; // undefined
    }
}
