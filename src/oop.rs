use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
};

use crate::{CroxErrorKind, Function, InterpreterContext, Members, Node, Result, Span, Value};

#[derive(Copy, Clone)]
pub struct Class<'env> {
    pub name: &'env str,
    superclass: Option<Node<&'env Class<'env>>>,
    members: Members<'env, &'env Function<'env>>,
}

impl<'env> Class<'env> {
    pub fn new(
        name: &'env str,
        superclass: Option<Node<&'env Class<'env>>>,
        members: Members<'env, &'env Function<'env>>,
    ) -> Self {
        Self {
            name,
            superclass,
            members,
        }
    }

    pub fn arity(&self) -> usize {
        self.method_lookup("init").map_or(0, Function::arity)
    }

    pub fn call(
        &self,
        ctx: &mut InterpreterContext<'env, '_>,
        args: &[Value<'env>],
        span: Span,
    ) -> Result<Value<'env>> {
        let instance = Instance::new(*self);
        let instance = ctx.alloc(instance);
        if let Some(initializer) = self.method_lookup("init") {
            initializer.bind(instance).call(ctx, args, span)?;
        }
        Ok(Value::Instance(instance))
    }
}

pub struct Instance<'env> {
    // TODO: replace with &'env Class<'env>
    class: Class<'env>,
    fields: RefCell<HashMap<&'env str, Value<'env>>>,
}

impl<'env> Instance<'env> {
    pub fn new(class: Class<'env>) -> Self {
        Self {
            class,
            fields: RefCell::new(HashMap::new()),
        }
    }

    pub fn name(&self) -> &'env str {
        self.class.name
    }
}

impl<'env> Class<'env> {
    pub fn lookup(&self, name: &'env str) -> Lookup<'_, 'env> {
        if let Some(&property) = self.members.properties().find(|p| p.name == name) {
            return Lookup::Property(property);
        }

        let method = self.members.methods().find(|m| m.name == name);
        if let Some(&method) = method {
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

    fn method_lookup(&self, name: &'env str) -> Option<&'env Function<'env>> {
        let method = self.members.methods().find(|m| m.name == name);
        if let Some(&method) = method {
            return Some(method);
        }

        self.superclass
            .as_ref()
            .and_then(|sc| sc.item.method_lookup(name))
    }

    pub fn class_method_lookup(&self, name: &'env str) -> Option<&'env Function<'env>> {
        let method = self.members.class_methods().find(|m| m.name == name);
        if let Some(&method) = method {
            return Some(method);
        }

        self.superclass
            .as_ref()
            .and_then(|sc| sc.item.class_method_lookup(name))
    }
}

impl<'env> Instance<'env> {
    pub fn lookup(&self, name: &'env str) -> Lookup<'_, 'env> {
        let field = self.fields.borrow();
        let field = Ref::filter_map(field, |f| f.get(name));
        if let Ok(field) = field {
            return Lookup::Field(field);
        }

        self.class.lookup(name)
    }

    pub fn insert(&self, name: &'env str, value: Value<'env>) {
        self.fields.borrow_mut().insert(name, value);
    }
}

#[derive(Debug)]
pub enum Lookup<'a, 'env> {
    Field(Ref<'a, Value<'env>>),
    Property(&'env Function<'env>),
    Method(&'env Function<'env>),
    ClassMethod,
    Undefined,
}

impl<'a, 'env> Lookup<'a, 'env> {
    pub fn into_method(self, method: &str, span: Span) -> Result<&'a Function<'env>> {
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

    pub fn into_value(
        self,
        ctx: &mut InterpreterContext<'env, '_>,
        instance: &'env Instance<'env>,
        name: &Node<&'env str>,
        caller: Span,
    ) -> Result<Value<'env>> {
        match self {
            Lookup::Field(field) => Ok(*field),
            Lookup::Property(property) => {
                let property = property.bind(instance);
                property.call(ctx, &[], caller)
            }
            Lookup::Method(method) => {
                let method = method.bind(instance);
                let method = ctx.alloc(method);
                Ok(Value::from(method))
            }
            Lookup::ClassMethod => Err(CroxErrorKind::ClassMemberOnInstance {
                name: name.item.to_owned(),
            }
            .at(name.span)),
            Lookup::Undefined => Err(CroxErrorKind::UndefinedMember {
                name: name.item.to_owned(),
            }
            .at(name.span)),
        }
    }
}

impl<'env> std::fmt::Debug for Class<'env> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<class {}>", self.name)
    }
}

impl<'env> std::fmt::Debug for Instance<'env> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<{} instance>", self.name())
    }
}
