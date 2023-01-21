use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
    rc::Rc,
};

use crate::{
    Callable, CroxErrorKind, Function, InterpreterContext, Members, Node, Result, Span, Type,
    TypeSet, Value,
};

#[derive(Clone)]
pub struct Class<'a> {
    pub name: &'a str,
    superclass: Option<Node<Rc<Class<'a>>>>,
    members: Members<Rc<Function<'a>>>,
}

impl<'a> Class<'a> {
    pub fn new(
        name: &'a str,
        superclass: Option<Node<Rc<Class<'a>>>>,
        members: Members<Rc<Function<'a>>>,
    ) -> Self {
        Self {
            name,
            superclass,
            members,
        }
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

impl<'a> Class<'a> {
    fn lookup(&self, name: &'a str) -> Lookup<'_, 'a> {
        if let Some(property) = self.members.properties().find(|p| p.name == name) {
            return Lookup::Property(property);
        }

        let method = self.members.methods().find(|m| m.name == name);
        if let Some(method) = method {
            return Lookup::Method(method);
        }

        if self.members.class_methods().any(|cm| cm.name == name) {
            return Lookup::ClassMethod;
        }

        Lookup::Undefined
    }
}

impl<'a> Instance<'a> {
    fn lookup(&self, name: &'a str) -> Lookup<'_, 'a> {
        let field = self.fields.borrow();
        let field = Ref::filter_map(field, |f| f.get(name));
        if let Ok(field) = field {
            return Lookup::Field(field);
        }

        self.class.lookup(name)
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
        match self.lookup(name.item) {
            Lookup::Field(field) => Ok(field.clone()),
            Lookup::Property(property) => {
                let property = property.bind(Rc::clone(self));
                property.call(ctx, &[], caller)
            }
            Lookup::Method(method) => {
                let method = method.bind(Rc::clone(self));
                Ok(Value::from(method))
            }
            Lookup::ClassMethod => Err(CroxErrorKind::ClassPropertyOnInstance {
                name: name.item.to_owned(),
            }
            .at(name.span)),
            Lookup::Undefined => Err(CroxErrorKind::UndefinedProperty {
                name: name.item.to_owned(),
            }
            .at(name.span)),
        }
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

enum Lookup<'a, 'env> {
    Field(Ref<'a, Value<'env>>),
    Property(&'a Rc<Function<'env>>),
    Method(&'a Rc<Function<'env>>),
    ClassMethod,
    Undefined,
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
