use std::cell::Cell;

use crate::{Bump, Function, FunctionDecl, FunctionKind, Node};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Members<'env, T> {
    pub(crate) members: &'env [T],
    pub(crate) methods: usize,
    pub(crate) class_methods: usize,
}

impl<'env, T: MemberConstructor<'env>> Members<'env, T> {
    pub fn new(members: &'env mut [T]) -> Self {
        members.sort_by_key(|m| (m.kind(), m.name()));

        let (methods, class_methods) =
            members
                .iter()
                .fold((0, 0), |(methods, class_methods), member| {
                    match member.kind() {
                        FunctionKind::Method => (methods + 1, class_methods + 1),
                        FunctionKind::ClassMethod => (methods, class_methods + 1),
                        FunctionKind::Property => (methods, class_methods),
                        otherwise => panic!("unsupported class member of kind {otherwise}"),
                    }
                });

        Self {
            members,
            methods,
            class_methods,
        }
    }
}

impl<'env, T: MemberItem<'env>> Members<'env, T> {
    pub fn methods(&self) -> impl Iterator<Item = &T> {
        self.members[..self.methods].iter()
    }

    pub fn class_methods(&self) -> impl Iterator<Item = &T> {
        self.members[self.methods..self.class_methods].iter()
    }

    pub fn properties(&self) -> impl Iterator<Item = &T> {
        self.members[self.class_methods..].iter()
    }

    pub fn slot_of(&self, name: &str, distance: usize) -> Slot {
        match self.members.iter().position(|m| m.name() == name) {
            Some(slot) if slot < self.methods => Slot::method(slot, distance),
            Some(slot) if slot < self.class_methods => Slot::class_method(slot, distance),
            Some(slot) => Slot::property(slot, distance),
            None => Slot::Unknown,
        }
    }

    pub fn find_method(&self, name: &str, distance: usize) -> Slot {
        match self.members[..self.methods]
            .iter()
            .position(|m| m.name() == name)
        {
            Some(slot) => Slot::method(slot, distance),
            None => Slot::Unknown,
        }
    }

    pub fn find_class_method(&self, name: &str, distance: usize) -> Slot {
        match self.members[self.methods..self.class_methods]
            .iter()
            .position(|m| m.name() == name)
        {
            Some(slot) => Slot::class_method(slot + self.methods, distance),
            None => Slot::Unknown,
        }
    }
}

impl<'env, T> Members<'env, T> {
    pub fn get_slot(&self, slot: u32) -> &T {
        &self.members[slot as usize]
    }

    pub fn map<U>(&self, arena: &'env Bump, map: impl FnMut(&T) -> U) -> Members<'env, U> {
        let members = self.members.iter().map(map);
        let members = arena.alloc_slice_fill_iter(members);

        Members {
            members,
            methods: self.methods,
            class_methods: self.class_methods,
        }
    }
}

pub trait MemberItem<'env> {
    fn name(&self) -> &'env str;
}

pub trait MemberConstructor<'env>: MemberItem<'env> {
    fn kind(&self) -> FunctionKind;
}

impl<'env> MemberItem<'env> for Node<FunctionDecl<'env>> {
    fn name(&self) -> &'env str {
        self.item.name.item
    }
}

impl<'env> MemberConstructor<'env> for Node<FunctionDecl<'env>> {
    fn kind(&self) -> FunctionKind {
        self.item.kind
    }
}

impl<'env> MemberItem<'env> for &'env Function<'env> {
    fn name(&self) -> &'env str {
        self.name
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Slotted {
    pub(crate) slot: Cell<Slot>,
}

impl Slotted {
    pub fn new() -> Self {
        Self {
            slot: Cell::new(Slot::Unknown),
        }
    }

    pub fn get(&self) -> Slot {
        self.slot.get()
    }

    pub fn set(&self, slot: Slot) {
        self.slot.set(slot);
    }
}

impl Default for Slotted {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub enum Slot {
    #[default]
    Unknown,
    Method {
        slot: u32,
        distance: u16,
    },
    ClassMethod {
        slot: u32,
        distance: u16,
    },
    Property {
        slot: u32,
        distance: u16,
    },
}

impl Slot {
    pub fn method(slot: usize, distance: usize) -> Self {
        let slot = u32::try_from(slot).expect("Too many slots in use");
        let distance = u16::try_from(distance).expect("Too many superclasses");
        Self::Method { slot, distance }
    }

    pub fn class_method(slot: usize, distance: usize) -> Self {
        let slot = u32::try_from(slot).expect("Too many slots in use");
        let distance = u16::try_from(distance).expect("Too many superclasses");
        Self::ClassMethod { slot, distance }
    }

    pub fn property(slot: usize, distance: usize) -> Self {
        let slot = u32::try_from(slot).expect("Too many slots in use");
        let distance = u16::try_from(distance).expect("Too many superclasses");
        Self::Property { slot, distance }
    }
}
