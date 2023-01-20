use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{
    Callable, CroxErrorKind, Function, InterpreterContext, Members, Node, Result, Span, Type,
    TypeSet, Value,
};

#[derive(Clone)]
pub struct Class<'a> {
    pub name: &'a str,
    members: Members<Rc<Function<'a>>>,
}

impl<'a> Class<'a> {
    pub fn new(name: &'a str, members: Members<Rc<Function<'a>>>) -> Self {
        Self { name, members }
    }
}

impl<'a> Callable<'a> for Class<'a> {
    fn arity(&self) -> usize {
        self.members
            .methods()
            .find_map(|m| (m.name == "init").then_some(m.arity()))
            .unwrap_or(0)
    }

    fn call(
        &self,
        ctx: &mut InterpreterContext<'a, '_>,
        args: &[Value<'a>],
        span: Span,
    ) -> Result<Value<'a>> {
        let instance = Instance::new(self.clone());
        let instance = Rc::new(instance);
        if let Some(initializer) = self.members.methods().find(|m| m.name == "init") {
            initializer
                .bind(Rc::clone(&instance))
                .call(ctx, args, span)?;
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
    fn get(
        &self,
        name: &Node<&'a str>,
        ctx: &mut InterpreterContext<'a, '_>,
        caller: Span,
    ) -> Result<Value<'a>>;
}

pub trait AsMutInstance<'a> {
    fn set(&self, name: &'a str, value: Value<'a>);
}

impl<'a> AsInstance<'a> for Rc<Instance<'a>> {
    fn get(
        &self,
        name: &Node<&'a str>,
        ctx: &mut InterpreterContext<'a, '_>,
        caller: Span,
    ) -> Result<Value<'a>> {
        let name_span = name.span;
        let name = name.item;

        let field = self.fields.borrow();
        let field = field.get(name);
        if let Some(field) = field {
            return Ok(field.clone());
        }

        if let Some(property) = self.class.members.properties().find(|p| p.name == name) {
            let property = property.bind(Rc::clone(self));
            return property.call(ctx, &[], caller);
        }

        let method = self.class.members.methods().find(|m| m.name == name);
        if let Some(method) = method {
            let method = method.bind(Rc::clone(self));
            return Ok(Value::from(method));
        }
        if self.class.members.class_methods().any(|cm| cm.name == name) {
            return Err(CroxErrorKind::ClassPropertyOnInstance {
                name: name.to_owned(),
            }
            .at(name_span));
        }
        Err(CroxErrorKind::UndefinedProperty {
            name: name.to_owned(),
        }
        .at(name_span))
    }
}

impl<'a> AsMutInstance<'a> for Rc<Instance<'a>> {
    fn set(&self, name: &'a str, value: Value<'a>) {
        self.fields.borrow_mut().insert(name, value);
    }
}

impl<'a> AsInstance<'a> for Rc<Class<'a>> {
    fn get(
        &self,
        name: &Node<&'a str>,
        _ctx: &mut InterpreterContext<'a, '_>,
        caller: Span,
    ) -> Result<Value<'a>> {
        let name = name.item;

        let method = self.members.class_methods().find(|cm| cm.name == name);
        if let Some(method) = method {
            return Ok(Value::Fn(Rc::clone(method)));
        }
        Err(CroxErrorKind::InvalidType {
            expected: TypeSet::from(Type::Instance),
            actual: Type::Class,
        }
        .at(caller))
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
