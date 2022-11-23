use crate::Value;

#[derive(Clone, Debug, Default)]
pub struct Environment<'a> {
    // names: Vec<&'a str>,
    // values: Vec<Value>,
    bindings: Vec<(&'a str, Value)>,
}

impl<'a> Environment<'a> {
    pub fn define(&mut self, name: &'a str, value: Value) {
        // self.names.push(name);
        // self.values.push(value);
        self.bindings.push((name, value));
    }

    pub fn get(&self, name: &'a str) -> Option<&Value> {
        // self.names
        //     .iter()
        //     .rposition(|&n| n == name)
        //     .map(|idx| &self.values[idx])
        self.bindings
            .iter()
            .rev()
            .find_map(|(n, v)| (n == &name).then_some(v))
    }
}
