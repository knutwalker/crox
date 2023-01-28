use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
    rc::Rc,
};

use crate::{
    Callable, CroxErrorKind, Function, InterpreterContext, Members, Node, Result, Span, Value,
};

#[derive(Clone)]
pub struct Class<'a> {
    pub name: &'a str,
    superclass: Option<Node<Rc<Class<'a>>>>,
    members: Members<'a, &'a Function<'a>>,
}

impl<'a> Class<'a> {
    pub fn new(
        name: &'a str,
        superclass: Option<Node<Rc<Class<'a>>>>,
        members: Members<'a, &'a Function<'a>>,
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
        self.method_lookup("init").map_or(0, Callable::arity)
    }

    fn call(
        &self,
        ctx: &mut InterpreterContext<'a, '_>,
        args: &[Value<'a>],
        span: Span,
    ) -> Result<Value<'a>> {
        let instance = Instance::new(self.clone());
        let instance = ctx.arena.alloc(instance);
        if let Some(initializer) = self.method_lookup("init") {
            initializer.bind(instance).call(ctx, args, span)?;
        }
        Ok(Value::Instance(instance))
    }
}

pub struct Instance<'a> {
    // TODO: replace with &'a Class<'a>
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

    fn method_lookup(&self, name: &'a str) -> Option<&'a Function<'a>> {
        let method = self.members.methods().find(|m| m.name == name);
        if let Some(&method) = method {
            return Some(method);
        }

        self.superclass
            .as_ref()
            .and_then(|sc| sc.item.method_lookup(name))
    }

    pub fn class_method_lookup(&self, name: &'a str) -> Option<&'a Function<'a>> {
        let method = self.members.class_methods().find(|m| m.name == name);
        if let Some(&method) = method {
            return Some(method);
        }

        self.superclass
            .as_ref()
            .and_then(|sc| sc.item.class_method_lookup(name))
    }
}

impl<'a> Instance<'a> {
    pub fn lookup(&self, name: &'a str) -> Lookup<'_, 'a> {
        let field = self.fields.borrow();
        let field = Ref::filter_map(field, |f| f.get(name));
        if let Ok(field) = field {
            return Lookup::Field(field);
        }

        self.class.lookup(name)
    }

    pub fn insert(&self, name: &'a str, value: Value<'a>) {
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
            Lookup::Field(field) => Ok(field.clone()),
            Lookup::Property(property) => {
                let property = property.bind(instance);
                property.call(ctx, &[], caller)
            }
            Lookup::Method(method) => {
                let method = method.bind(instance);
                let method = ctx.arena.alloc(method);
                Ok(Value::from(&*method))
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
