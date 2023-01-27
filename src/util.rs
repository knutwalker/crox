use std::{fmt, iter::FusedIterator, marker::PhantomData, num::NonZeroU64};

#[derive(Clone, PartialEq, Eq)]
pub struct EnumSet<T> {
    bits: u64,
    _enum: PhantomData<T>,
}

impl<T> EnumSet<T> {
    /// Create a new empty set
    pub fn empty() -> Self {
        Self {
            bits: 0,
            _enum: PhantomData,
        }
    }

    /// Returns the number of elements in this set
    pub fn len(&self) -> usize {
        self.bits.count_ones() as usize
    }

    /// Returns `true` if this set is empty
    pub fn is_empty(&self) -> bool {
        self.bits == 0
    }

    /// Remove all the entries from this set
    pub fn clear(&mut self) {
        self.bits = 0;
    }
}

#[allow(clippy::needless_pass_by_value)]
impl<T: ValueEnum> EnumSet<T> {
    /// Returns `true` if the value was added to this set, `false` if it was already present.
    pub fn insert(&mut self, value: T) -> bool {
        let old = self.bits;
        let new = old | (1 << value.to_ord());
        self.bits = new;
        old != new
    }

    /// Returns `true` if the value was removed, `false` if it was not present.
    pub fn remove(&mut self, value: T) -> bool {
        let old = self.bits;
        let new = old & !(1 << value.to_ord());
        self.bits = new;
        old != new
    }

    // Returns a new set with the typ present.
    pub fn with(mut self, value: T) -> Self {
        self.insert(value);

        self
    }

    // Returns a new set with all types from the iter present.
    pub fn with_all<I: IntoIterator<Item = T>>(mut self, iterator: I) -> Self {
        self.extend(iterator);

        self
    }

    /// Returns `true` if the set contains the type.
    pub fn contains(&self, value: T) -> bool {
        self.bits & (1 << value.to_ord()) != 0
    }

    /// Returns an iterator over the set's elements.
    pub fn iter(&self) -> TokensIter<T> {
        TokensIter {
            bits: NonZeroU64::new(self.bits),
            _enum: PhantomData,
        }
    }
}

impl<T> Default for EnumSet<T> {
    fn default() -> Self {
        Self::empty()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TokensIter<T> {
    bits: Option<NonZeroU64>,
    _enum: PhantomData<T>,
}

impl<T: ValueEnum> Iterator for TokensIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let bits = self.bits?.get();
        self.bits = NonZeroU64::new(bits ^ (bits & (!bits + 1)));
        #[allow(clippy::cast_possible_truncation)]
        let ord = bits.trailing_zeros() as u8;
        // SAFETY: we only add valid values to the set
        Some(unsafe { T::from_ord(ord) })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let count = self.bits.map_or(0, NonZeroU64::get).count_ones() as usize;
        (count, Some(count))
    }
}

impl<T: ValueEnum> ExactSizeIterator for TokensIter<T> {
    fn len(&self) -> usize {
        self.bits.map_or(0, NonZeroU64::get).count_ones() as usize
    }
}

impl<T: ValueEnum> FusedIterator for TokensIter<T> {}

impl<'a, T: ValueEnum> IntoIterator for &'a EnumSet<T> {
    type Item = T;

    type IntoIter = TokensIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T: ValueEnum> Extend<T> for EnumSet<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for element in iter {
            self.insert(element);
        }
    }
}

impl<T: ValueEnum> From<T> for EnumSet<T> {
    fn from(value: T) -> Self {
        Self::empty().with(value)
    }
}

impl<T: ValueEnum> FromIterator<T> for EnumSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iterator: I) -> Self {
        let mut set = Self::empty();
        set.extend(iterator);
        set
    }
}

impl<T: fmt::Debug + ValueEnum> fmt::Debug for EnumSet<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

pub trait ValueEnum {
    fn to_ord(&self) -> u8;

    /// # Safety
    /// the value must be in the range of the enum
    unsafe fn from_ord(ord: u8) -> Self;
}

#[cfg(test)]
#[allow(clippy::bool_assert_comparison)]
mod tests {
    use super::{EnumSet, ValueEnum};
    use E::*;

    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    #[repr(u8)]
    enum E {
        A,
        B,
        C,
        D,
    }

    impl ValueEnum for E {
        fn to_ord(&self) -> u8 {
            *self as u8
        }

        unsafe fn from_ord(ord: u8) -> Self {
            std::mem::transmute(ord)
        }
    }

    #[test]
    fn test_empty() {
        let set = EnumSet::<E>::empty();
        assert!(set.is_empty());
    }

    #[test]
    fn test_len() {
        let mut set = EnumSet::<E>::empty();
        assert_eq!(set.len(), 0);

        set.insert(A);
        assert_eq!(set.len(), 1);

        set.insert(B);
        assert_eq!(set.len(), 2);

        set.insert(A);
        assert_eq!(set.len(), 2);

        set.remove(A);
        assert_eq!(set.len(), 1);

        set.clear();
        assert_eq!(set.len(), 0);
    }

    #[test]
    fn test_insert() {
        let mut set = EnumSet::<E>::empty();

        let res = set.insert(A);
        assert_eq!(res, true);
        assert_eq!(set.contains(A), true);

        let res = set.insert(A);
        assert_eq!(res, false);
        assert_eq!(set.contains(A), true);

        let res = set.insert(B);
        assert_eq!(res, true);
        assert_eq!(set.contains(B), true);

        let res = set.insert(B);
        assert_eq!(res, false);
        assert_eq!(set.contains(B), true);
    }

    #[test]
    fn test_with() {
        let set = EnumSet::<E>::empty().with(A).with(C);

        assert_eq!(set.contains(A), true);
        assert_eq!(set.contains(C), true);
        assert_eq!(set.contains(B), false);

        let set = set.with(B);

        assert_eq!(set.contains(A), true);
        assert_eq!(set.contains(C), true);
        assert_eq!(set.contains(B), true);
    }

    #[test]
    fn test_remove() {
        let mut set = EnumSet::<E>::empty();

        set.insert(A);
        set.insert(B);

        assert_eq!(set.contains(A), true);
        assert_eq!(set.contains(B), true);

        let res = set.remove(A);
        assert_eq!(res, true);
        assert_eq!(set.contains(A), false);

        let res = set.remove(A);
        assert_eq!(res, false);
        assert_eq!(set.contains(A), false);

        let res = set.remove(B);
        assert_eq!(res, true);
        assert_eq!(set.contains(B), false);

        let res = set.remove(B);
        assert_eq!(res, false);
        assert_eq!(set.contains(B), false);
    }

    #[test]
    fn test_contains() {
        let mut set = EnumSet::<E>::empty();
        set.insert(C);

        assert!(set.contains(C));
        assert!(!set.contains(D));
        assert!(!set.contains(A));

        set.insert(C);
        set.insert(D);
        assert!(set.contains(C));
        assert!(set.contains(D));
        assert!(!set.contains(A));
    }

    #[test]
    fn test_iterator() {
        let mut set = EnumSet::<E>::empty();

        assert_eq!(set.iter().collect::<Vec<_>>(), vec![]);

        set.insert(A);
        assert_eq!(set.iter().collect::<Vec<_>>(), vec![A]);

        set.insert(C);
        assert_eq!(set.iter().collect::<Vec<_>>(), vec![A, C]);

        set.insert(C);
        assert_eq!(set.iter().collect::<Vec<_>>(), vec![A, C]);

        set.insert(B);
        assert_eq!(set.iter().collect::<Vec<_>>(), vec![A, B, C]);
    }

    #[test]
    fn test_iterator_size() {
        let mut set = EnumSet::<E>::empty();

        assert_eq!(set.iter().len(), 0);

        set.insert(A);
        assert_eq!(set.iter().len(), 1);

        set.insert(C);
        assert_eq!(set.iter().len(), 2);

        set.insert(C);
        assert_eq!(set.iter().len(), 2);

        set.insert(B);
        let mut iter = set.iter();
        assert_eq!(iter.len(), 3);

        assert_eq!(iter.next(), Some(A));
        assert_eq!(iter.len(), 2);

        assert_eq!(iter.next(), Some(B));
        assert_eq!(iter.len(), 1);

        assert_eq!(iter.next(), Some(C));
        assert_eq!(iter.len(), 0);

        assert_eq!(iter.next(), None);
        assert_eq!(iter.len(), 0);
    }

    #[test]
    fn test_from_iter() {
        let set = [C, B, A].into_iter().collect::<EnumSet<E>>();

        assert_eq!(set.len(), 3);
        assert_eq!(set.contains(A), true);
        assert_eq!(set.contains(B), true);
        assert_eq!(set.contains(C), true);
        assert_eq!(set.contains(D), false);

        assert_eq!(set.iter().collect::<Vec<_>>(), vec![A, B, C]);
    }

    #[test]
    fn test_extend() {
        let mut set = EnumSet::<E>::empty();
        assert!(set.is_empty());

        set.extend([C, B, A]);

        assert_eq!(set.len(), 3);
        assert_eq!(set.contains(A), true);
        assert_eq!(set.contains(B), true);
        assert_eq!(set.contains(C), true);
        assert_eq!(set.contains(D), false);

        assert_eq!(set.iter().collect::<Vec<_>>(), vec![A, B, C]);

        set.extend([A, D]);

        assert_eq!(set.len(), 4);
        assert_eq!(set.contains(A), true);
        assert_eq!(set.contains(B), true);
        assert_eq!(set.contains(C), true);
        assert_eq!(set.contains(D), true);

        assert_eq!(set.iter().collect::<Vec<_>>(), vec![A, B, C, D]);
    }

    #[test]
    fn test_with_all() {
        let set = EnumSet::<E>::empty();

        let set = set.with_all([C, B, A]);

        assert_eq!(set.len(), 3);
        assert_eq!(set.contains(A), true);
        assert_eq!(set.contains(B), true);
        assert_eq!(set.contains(C), true);
        assert_eq!(set.contains(D), false);

        assert_eq!(set.iter().collect::<Vec<_>>(), vec![A, B, C]);

        let set = set.with_all([A, D]);

        assert_eq!(set.len(), 4);
        assert_eq!(set.contains(A), true);
        assert_eq!(set.contains(B), true);
        assert_eq!(set.contains(C), true);
        assert_eq!(set.contains(D), true);

        assert_eq!(set.iter().collect::<Vec<_>>(), vec![A, B, C, D]);
    }

    #[test]
    fn test_debug() {
        let mut set = EnumSet::<E>::empty();
        assert_eq!("[]", format!("{set:?}"));
        set.insert(A);
        assert_eq!("[A]", format!("{set:?}"));
        set.insert(B);
        assert_eq!("[A, B]", format!("{set:?}"));
    }
}
