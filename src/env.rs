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
}
