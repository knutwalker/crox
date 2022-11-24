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
