use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{Callable, Function, InterpreterContext, Result, Span, Value};

#[derive(Clone)]
pub struct Class<'a> {
    pub name: &'a str,
    methods: Rc<HashMap<&'a str, Function<'a>>>,
}

impl<'a> Class<'a> {
    pub fn new(name: &'a str, methods: HashMap<&'a str, Function<'a>>) -> Self {
        Self {
            name,
            methods: methods.into(),
        }
    }
}

impl<'a> Callable<'a> for Class<'a> {
    fn arity(&self) -> usize {
        self.methods.get("init").map(|fun| fun.arity()).unwrap_or(0)
    }

    fn call(
        &self,
        ctx: &mut InterpreterContext<'a, '_>,
        args: &[Value<'a>],
        span: Span,
    ) -> Result<Value<'a>> {
        let instance = Instance::new(self.clone());
        let instance = Rc::new(instance);
        if let Some(initializer) = self.methods.get("init") {
            initializer.bind(instance.clone()).call(ctx, args, span)?;
        }
        Ok(Value::Instance(instance))
    }
}

#[derive(Clone)]
pub struct Instance<'a> {
    class: Class<'a>,
    fields: RefCell<HashMap<&'a str, Value<'a>>>,
}

impl<'a> Instance<'a> {
    pub fn new(class: Class<'a>) -> Self {
        Self {
            class,
            fields: RefCell::new(HashMap::new()),
        }
    }

    pub fn name(&self) -> &'a str {
        self.class.name
    }

    pub fn get(self: &Rc<Self>, name: &'a str) -> Option<Value<'a>> {
        self.fields.borrow().get(name).cloned().or_else(|| {
            self.class
                .methods
                .get(name)
                .map(|method| Value::Fn(method.bind(Rc::clone(self))))
        })
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
        write!(f, "<{} instance>", self.name())
    }
}
