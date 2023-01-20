use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{Callable, Function, InterpreterContext, Result, Span, Value};

#[derive(Clone)]
pub struct Class<'a> {
    pub name: &'a str,
    methods: Rc<HashMap<&'a str, Function<'a>>>,
    class_methods: Rc<HashMap<&'a str, Rc<Function<'a>>>>,
}

impl<'a> Class<'a> {
    pub fn new(
        name: &'a str,
        methods: HashMap<&'a str, Function<'a>>,
        class_methods: HashMap<&'a str, Rc<Function<'a>>>,
    ) -> Self {
        Self {
            name,
            methods: methods.into(),
            class_methods: class_methods.into(),
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
}

pub trait AsInstance<'a> {
    fn get(&self, name: &'a str) -> Result<Value<'a>, LookupError>;
}

pub trait AsMutInstance<'a> {
    fn set(&self, name: &'a str, value: Value<'a>);
}

impl<'a> AsInstance<'a> for Rc<Instance<'a>> {
    fn get(&self, name: &'a str) -> Result<Value<'a>, LookupError> {
        // return error enum or error ish enum for the reason -- not found / invalid type
        let field = self.fields.borrow();
        let field = field.get(name);
        if let Some(field) = field {
            return Ok(field.clone());
        }
        let method = self.class.methods.get(name);
        if let Some(method) = method {
            let method = method.bind(Rc::clone(self));
            return Ok(Value::from(method));
        }
        if self.class.class_methods.contains_key(name) {
            return Err(LookupError::ClassPropertyOnInstance);
        }
        Err(LookupError::NoSuchProperty)
    }
}

impl<'a> AsMutInstance<'a> for Rc<Instance<'a>> {
    fn set(&self, name: &'a str, value: Value<'a>) {
        self.fields.borrow_mut().insert(name, value);
    }
}

impl<'a> AsInstance<'a> for Rc<Class<'a>> {
    fn get(&self, name: &'a str) -> Result<Value<'a>, LookupError> {
        let method = self.class_methods.get(name);
        if let Some(method) = method {
            return Ok(Value::Fn(Rc::clone(method)));
        }
        Err(LookupError::InvalidType)
    }
}

pub enum LookupError {
    NoSuchProperty,
    ClassPropertyOnInstance,
    InvalidType,
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
