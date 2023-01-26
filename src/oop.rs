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
    pub fn lookup(&self, name: &'a str) -> Lookup<'_, 'a> {
        if let Some(property) = self.members.properties().find(|p| p.name == name) {
            return Lookup::Property(property);
        }

        let method = self.members.methods().find(|m| m.name == name);
        if let Some(method) = method {
            return Lookup::Method(method);
        }

        if let Some(superclass) = self.superclass.as_ref() {
            match superclass.item.lookup(name) {
                res @ (Lookup::Field(_)
                | Lookup::Property(_)
                | Lookup::Method(_)
                | Lookup::ClassMethod) => return res,
                Lookup::Undefined => {}
            }
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

pub trait InstanceLike<'a> {
    fn get(&self, name: &Node<&'a str>, caller: Span) -> Result<IntoValue<'a>>;
}

pub trait MutInstanceLike<'a> {
    fn set(&self, name: &'a str, value: Value<'a>);
}

impl<'a> InstanceLike<'a> for Rc<Instance<'a>> {
    fn get(&self, name: &Node<&'a str>, _caller: Span) -> Result<IntoValue<'a>> {
        self.lookup(name.item)
            .into_value(self, name.item, name.span)
    }
}

impl<'a> MutInstanceLike<'a> for Rc<Instance<'a>> {
    fn set(&self, name: &'a str, value: Value<'a>) {
        self.fields.borrow_mut().insert(name, value);
    }
}

impl<'a> InstanceLike<'a> for Rc<Class<'a>> {
    fn get(&self, name: &Node<&'a str>, caller: Span) -> Result<IntoValue<'a>> {
        let name = name.item;

        let method = self.members.class_methods().find(|cm| cm.name == name);
        if let Some(method) = method {
            return Ok(IntoValue::Value(Value::Fn(Rc::clone(method))));
        }
        Err(CroxErrorKind::InvalidType {
            expected: TypeSet::from(Type::Instance),
            actual: Type::Class,
        }
        .at(caller))
    }
}

#[derive(Clone, Debug)]
pub enum IntoValue<'a> {
    Value(Value<'a>),
    Property(Function<'a>),
}

impl<'a> IntoValue<'a> {
    pub fn into_value(
        self,
        ctx: &mut InterpreterContext<'a, '_>,
        caller: Span,
    ) -> Result<Value<'a>> {
        match self {
            IntoValue::Value(v) => Ok(v),
            IntoValue::Property(p) => p.call(ctx, &[], caller),
        }
    }
}

#[derive(Debug)]
pub enum Lookup<'a, 'env> {
    Field(Ref<'a, Value<'env>>),
    Property(&'a Rc<Function<'env>>),
    Method(&'a Rc<Function<'env>>),
    ClassMethod,
    Undefined,
}

impl<'a, 'env> Lookup<'a, 'env> {
    pub fn into_method(self, method: &str, span: Span) -> Result<&'a Rc<Function<'env>>> {
        match self {
            Lookup::Method(method) => Ok(method),
            Lookup::Field(_) | Lookup::Property(_) => Err(CroxErrorKind::MemberIsNotAMethod {
                name: method.to_owned(),
            }
            .at(span)),
            Lookup::ClassMethod => Err(CroxErrorKind::ClassMemberOnInstance {
                name: method.to_owned(),
            }
            .at(span)),
            Lookup::Undefined => Err(CroxErrorKind::UndefinedMember {
                name: method.to_owned(),
            }
            .at(span)),
        }
    }

    fn into_value(
        self,
        instance: &Rc<Instance<'env>>,
        name: &str,
        span: Span,
    ) -> Result<IntoValue<'env>> {
        match self {
            Lookup::Field(field) => Ok(IntoValue::Value(field.clone())),
            Lookup::Property(property) => {
                let property = property.bind(Rc::clone(instance));
                Ok(IntoValue::Property(property))
            }
            Lookup::Method(method) => {
                let method = method.bind(Rc::clone(instance));
                Ok(IntoValue::Value(Value::from(method)))
            }
            Lookup::ClassMethod => Err(CroxErrorKind::ClassMemberOnInstance {
                name: name.to_owned(),
            }
            .at(span)),
            Lookup::Undefined => Err(CroxErrorKind::UndefinedMember {
                name: name.to_owned(),
            }
            .at(span)),
        }
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
