use std::{
    cell::{Ref, RefCell},
    rc::Rc,
};

use crate::{
    Bump, CroxErrorKind, Function, InterpreterContext, Members, Node, Result, Slot, Slotted, Span,
    Value,
};

use ahash::{HashMap, HashMapExt};

#[derive(Copy, Clone)]
pub struct Class<'env> {
    pub name: &'env str,
    superclass: Option<Node<&'env Class<'env>>>,
    members: Members<'env, &'env Function<'env>>,
    init_slot: &'env Slotted,
}

impl<'env> Class<'env> {
    pub fn new(
        name: &'env str,
        superclass: Option<Node<&'env Class<'env>>>,
        members: Members<'env, &'env Function<'env>>,
        arena: &'env Bump,
    ) -> Self {
        Self {
            name,
            superclass,
            members,
            init_slot: arena.alloc(Slotted::new()),
        }
    }

    pub fn arity(&self) -> usize {
        self.method_lookup("init", self.init_slot)
            .map_or(0, Function::arity)
    }

    pub fn call(
        &'env self,
        ctx: &mut InterpreterContext<'env, '_>,
        args: &[Value<'env>],
        span: Span,
    ) -> Result<Value<'env>> {
        let instance = Instance::new(self);
        let instance = Rc::new(instance);
        if let Some(initializer) = self.method_lookup("init", self.init_slot) {
            initializer
                .bind(Rc::clone(&instance))
                .call(ctx, args, span)?;
        }
        Ok(Value::Instance(instance))
    }
}

pub struct Instance<'env> {
    class: &'env Class<'env>,
    fields: RefCell<HashMap<&'env str, Value<'env>>>,
}

impl<'env> Instance<'env> {
    pub fn new(class: &'env Class<'env>) -> Self {
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
    pub fn lookup(&self, name: &'env str, slotted: &'env Slotted) -> Lookup<'_, 'env> {
        match self.lookup_slot(name, slotted.get()) {
            Ok(res) => res,
            Err(Some((res, slot))) => {
                slotted.set(slot);
                res
            }
            Err(None) => Lookup::Undefined,
        }
    }

    fn lookup_slot(
        &self,
        name: &'env str,
        slot: Slot,
    ) -> Result<Lookup<'_, 'env>, LookupSlow<'_, 'env>> {
        Ok(match slot {
            Slot::Unknown => return Err(self.lookup_slow(name)),
            Slot::ClassMethod { .. } => Lookup::ClassMethod,
            Slot::Method { slot, distance } => {
                Lookup::Method(self.ancestor(distance).unwrap().members.get_slot(slot))
            }
            Slot::Property { slot, distance } => {
                Lookup::Property(self.ancestor(distance).unwrap().members.get_slot(slot))
            }
        })
    }

    fn lookup_slow(&self, name: &'env str) -> LookupSlow<'_, 'env> {
        self.ancestors().enumerate().find_map(|(distance, this)| {
            match this.members.slot_of(name, distance) {
                Slot::Unknown => None,
                s @ Slot::ClassMethod { .. } => Some((Lookup::ClassMethod, s)),
                s @ Slot::Method { slot, distance: _ } => {
                    Some((Lookup::Method(this.members.get_slot(slot)), s))
                }
                s @ Slot::Property { slot, distance: _ } => {
                    Some((Lookup::Property(this.members.get_slot(slot)), s))
                }
            }
        })
    }

    fn method_lookup(
        &self,
        name: &'env str,
        slotted: &'env Slotted,
    ) -> Option<&'env Function<'env>> {
        match slotted.get() {
            Slot::Unknown => self.ancestors().enumerate().find_map(|(distance, this)| {
                match this.members.find_method(name, distance) {
                    s @ Slot::Method { slot, distance: _ } => {
                        slotted.set(s);
                        Some(*this.members.get_slot(slot))
                    }
                    _ => None,
                }
            }),
            Slot::Method { slot, distance } => {
                Some(self.ancestor(distance).unwrap().members.get_slot(slot))
            }
            Slot::ClassMethod { .. } | Slot::Property { .. } => None,
        }
    }

    pub fn class_method_lookup(
        &self,
        name: &'env str,
        slotted: &'env Slotted,
    ) -> Option<&'env Function<'env>> {
        match slotted.get() {
            Slot::Unknown => self.ancestors().enumerate().find_map(|(distance, this)| {
                match this.members.find_class_method(name, distance) {
                    s @ Slot::ClassMethod { slot, distance: _ } => {
                        slotted.set(s);
                        Some(*this.members.get_slot(slot))
                    }
                    _ => None,
                }
            }),
            Slot::ClassMethod { slot, distance } => {
                Some(self.ancestor(distance).unwrap().members.get_slot(slot))
            }
            Slot::Method { .. } | Slot::Property { .. } => None,
        }
    }

    fn ancestors(&self) -> impl Iterator<Item = &Class<'env>> {
        std::iter::successors(Some(self), |this| this.superclass.as_ref().map(|n| n.item))
    }

    fn ancestor(&self, distance: u16) -> Option<&Class<'env>> {
        self.ancestors().nth(distance as usize)
    }
}

impl<'env> Instance<'env> {
    pub fn lookup(&self, name: &'env str, slot: &'env Slotted) -> Lookup<'_, 'env> {
        let field = self.fields.borrow();
        let field = Ref::filter_map(field, |f| f.get(name));
        if let Ok(field) = field {
            return Lookup::Field(field);
        }

        self.class.lookup(name, slot)
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
    pub fn into_method(self, method: &str, span: Span) -> Result<&'env Function<'env>> {
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
        instance: &Rc<Instance<'env>>,
        name: &Node<&'env str>,
        caller: Span,
    ) -> Result<Value<'env>> {
        match self {
            Lookup::Field(field) => Ok(field.clone()),
            Lookup::Property(property) => {
                let property = property.bind(Rc::clone(instance));
                property.call(ctx, &[], caller)
            }
            Lookup::Method(method) => {
                let method = method.bind(Rc::clone(instance));
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

type LookupSlow<'a, 'env> = Option<(Lookup<'a, 'env>, Slot)>;
