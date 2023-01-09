use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{Callable, InterpreterContext, Result, Value};

#[derive(Clone)]
pub struct Class<'a> {
    pub name: &'a str,
}

impl<'a> Class<'a> {
    pub fn new(name: &'a str) -> Self {
        Self { name }
    }
}

impl<'a> Callable<'a> for Class<'a> {
    fn arity(&self) -> usize {
        0
    }

    fn call(
        &self,
        _ctx: &mut InterpreterContext<'a, '_>,
        _args: &[Value<'a>],
    ) -> Result<Value<'a>> {
        let instance = Instance::new(self.name);
        Ok(Value::Instance(Rc::new(instance)))
    }
}

#[derive(Clone)]
pub struct Instance<'a> {
    pub name: &'a str,
    fields: RefCell<HashMap<&'a str, Value<'a>>>,
}

impl<'a> Instance<'a> {
    pub fn new(name: &'a str) -> Self {
        Self {
            name,
            fields: RefCell::new(HashMap::new()),
        }
    }

    pub fn get(&self, name: &'a str) -> Option<Value<'a>> {
        self.fields.borrow().get(name).cloned()
    }

    pub fn set(&self, name: &'a str, value: Value<'a>) {
        self.fields.borrow_mut().insert(name, value);
    }
}

impl<'a> std::fmt::Debug for Class<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<class {}>", self.name)
    }
}

impl<'a> std::fmt::Debug for Instance<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<{} instance>", self.name)
    }
}
