use std::{
    fmt::{self, Debug},
    iter::FusedIterator,
    num::NonZeroU64,
};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum TokenType {
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Slash,
    Star,

    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    Identifier,
    String,
    Number,

    And,
    Class,
    Else,
    False,
    Fun,
    For,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    While,
}

impl From<&str> for TokenType {
    fn from(ident: &str) -> Self {
        match ident {
            "and" => TokenType::And,
            "class" => TokenType::Class,
            "else" => TokenType::Else,
            "false" => TokenType::False,
            "fun" => TokenType::Fun,
            "for" => TokenType::For,
            "if" => TokenType::If,
            "nil" => TokenType::Nil,
            "or" => TokenType::Or,
            "print" => TokenType::Print,
            "return" => TokenType::Return,
            "super" => TokenType::Super,
            "this" => TokenType::This,
            "true" => TokenType::True,
            "var" => TokenType::Var,
            "while" => TokenType::While,
            _ => TokenType::Identifier,
        }
    }
}

pub type Range = std::ops::Range<usize>;

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Span {
    pub offset: usize,
    pub len: usize,
}

impl Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&Range::from(*self), f)
    }
}

impl Span {
    pub fn new(offset: usize, len: usize) -> Self {
        Self { offset, len }
    }

    pub fn union(self, other: Self) -> Range {
        self.offset..(other.offset + other.len)
    }
}

impl From<Range> for Span {
    fn from(value: Range) -> Self {
        Self {
            offset: value.start,
            len: value.len(),
        }
    }
}

impl From<Span> for Range {
    fn from(value: Span) -> Self {
        value.offset..(value.offset + value.len)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Token {
    pub typ: TokenType,
    pub span: Span,
}

impl Token {
    pub fn new(typ: TokenType, offset: usize, len: usize) -> Self {
        Self {
            typ,
            span: Span::new(offset, len),
        }
    }

    pub fn span(&self) -> Span {
        self.span
    }
}

impl From<(TokenType, Range)> for Token {
    fn from((typ, range): (TokenType, Range)) -> Self {
        Self {
            typ,
            span: Span::from(range),
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct TokenSet {
    bits: u64,
}

impl TokenSet {
    /// Create a new empty set
    pub fn empty() -> Self {
        Self { bits: 0 }
    }

    /// Returns the number of elements in this set
    pub fn len(&self) -> usize {
        self.bits.count_ones() as usize
    }

    /// Returns `true` if this set is empty
    pub fn is_empty(&self) -> bool {
        self.bits == 0
    }

    /// Returns `true` if the value was added to this set, `false` if it was already present.
    pub fn insert(&mut self, typ: TokenType) -> bool {
        let old = self.bits;
        let new = old | (1 << (typ as u8));
        self.bits = new;
        old != new
    }

    /// Returns `true` if the value was removed, `false` if it was not present.
    pub fn remove(&mut self, typ: TokenType) -> bool {
        let old = self.bits;
        let new = old & !(1 << (typ as u8));
        self.bits = new;
        old != new
    }

    // Returns a new set with the typ present.
    pub fn with(mut self, typ: TokenType) -> Self {
        self.insert(typ);

        self
    }

    // Returns a new set with all types from the iter present.
    pub fn with_all<I: IntoIterator<Item = TokenType>>(mut self, iterator: I) -> Self {
        self.extend(iterator);

        self
    }

    /// Returns `true` if the set contains the type.
    pub fn contains(&self, typ: TokenType) -> bool {
        self.bits & (1 << (typ as u8)) != 0
    }

    /// Remove all the entries from this set
    pub fn clear(&mut self) {
        self.bits = 0;
    }

    /// Returns an iterator over the set's elements.
    pub fn iter(&self) -> TokensIter {
        TokensIter {
            bits: NonZeroU64::new(self.bits),
        }
    }
}

impl Default for TokenSet {
    fn default() -> Self {
        Self::empty()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TokensIter {
    bits: Option<NonZeroU64>,
}

impl Iterator for TokensIter {
    type Item = TokenType;

    fn next(&mut self) -> Option<Self::Item> {
        let bits = self.bits?.get();
        self.bits = NonZeroU64::new(bits ^ (bits & (!bits + 1)));
        let ord = bits.trailing_zeros() as u8;
        // SAFETY: we only add valid values to the set
        Some(unsafe { std::mem::transmute_copy(&ord) })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let count = self.bits.map_or(0, |b| b.get()).count_ones() as usize;
        (count, Some(count))
    }
}

impl ExactSizeIterator for TokensIter {
    fn len(&self) -> usize {
        self.bits.map_or(0, |b| b.get()).count_ones() as usize
    }
}

impl FusedIterator for TokensIter {}

impl<'a> IntoIterator for &'a TokenSet {
    type Item = TokenType;

    type IntoIter = TokensIter;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl FromIterator<TokenType> for TokenSet {
    fn from_iter<I: IntoIterator<Item = TokenType>>(iterator: I) -> Self {
        let mut set = Self::empty();
        set.extend(iterator);
        set
    }
}

impl Extend<TokenType> for TokenSet {
    fn extend<I: IntoIterator<Item = TokenType>>(&mut self, iter: I) {
        for element in iter {
            self.insert(element);
        }
    }
}

impl Debug for TokenSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

#[cfg(test)]
#[allow(clippy::bool_assert_comparison)]
mod tests {
    use super::{TokenSet, TokenType};
    use TokenType::*;

    #[test]
    fn test_empty() {
        let set = TokenSet::empty();
        assert!(set.is_empty());
    }

    #[test]
    fn test_len() {
        let mut set = TokenSet::empty();
        assert_eq!(set.len(), 0);

        set.insert(LeftParen);
        assert_eq!(set.len(), 1);

        set.insert(RightParen);
        assert_eq!(set.len(), 2);

        set.insert(LeftParen);
        assert_eq!(set.len(), 2);

        set.remove(LeftParen);
        assert_eq!(set.len(), 1);

        set.clear();
        assert_eq!(set.len(), 0);
    }

    #[test]
    fn test_insert() {
        let mut set = TokenSet::empty();

        let res = set.insert(LeftParen);
        assert_eq!(res, true);
        assert_eq!(set.contains(LeftParen), true);

        let res = set.insert(LeftParen);
        assert_eq!(res, false);
        assert_eq!(set.contains(LeftParen), true);

        let res = set.insert(RightParen);
        assert_eq!(res, true);
        assert_eq!(set.contains(RightParen), true);

        let res = set.insert(RightParen);
        assert_eq!(res, false);
        assert_eq!(set.contains(RightParen), true);
    }

    #[test]
    fn test_with() {
        let set = TokenSet::empty().with(LeftParen).with(LeftBrace);

        assert_eq!(set.contains(LeftParen), true);
        assert_eq!(set.contains(LeftBrace), true);
        assert_eq!(set.contains(RightParen), false);

        let set = set.with(RightParen);

        assert_eq!(set.contains(LeftParen), true);
        assert_eq!(set.contains(LeftBrace), true);
        assert_eq!(set.contains(RightParen), true);
    }

    #[test]
    fn test_remove() {
        let mut set = TokenSet::empty();

        set.insert(LeftParen);
        set.insert(RightParen);

        assert_eq!(set.contains(LeftParen), true);
        assert_eq!(set.contains(RightParen), true);

        let res = set.remove(LeftParen);
        assert_eq!(res, true);
        assert_eq!(set.contains(LeftParen), false);

        let res = set.remove(LeftParen);
        assert_eq!(res, false);
        assert_eq!(set.contains(LeftParen), false);

        let res = set.remove(RightParen);
        assert_eq!(res, true);
        assert_eq!(set.contains(RightParen), false);

        let res = set.remove(RightParen);
        assert_eq!(res, false);
        assert_eq!(set.contains(RightParen), false);
    }

    #[test]
    fn test_contains() {
        let mut set = TokenSet::empty();
        set.insert(LeftBrace);

        assert!(set.contains(LeftBrace));
        assert!(!set.contains(RightBrace));
        assert!(!set.contains(LeftParen));

        set.insert(LeftBrace);
        set.insert(RightBrace);
        assert!(set.contains(LeftBrace));
        assert!(set.contains(RightBrace));
        assert!(!set.contains(LeftParen));
    }

    #[test]
    fn test_iterator() {
        let mut set = TokenSet::empty();

        assert_eq!(set.iter().collect::<Vec<_>>(), vec![]);

        set.insert(LeftParen);
        assert_eq!(set.iter().collect::<Vec<_>>(), vec![LeftParen]);

        set.insert(LeftBrace);
        assert_eq!(set.iter().collect::<Vec<_>>(), vec![LeftParen, LeftBrace]);

        set.insert(LeftBrace);
        assert_eq!(set.iter().collect::<Vec<_>>(), vec![LeftParen, LeftBrace]);

        set.insert(RightParen);
        assert_eq!(
            set.iter().collect::<Vec<_>>(),
            vec![LeftParen, RightParen, LeftBrace]
        );
    }

    #[test]
    fn test_iterator_size() {
        let mut set = TokenSet::empty();

        assert_eq!(set.iter().len(), 0);

        set.insert(LeftParen);
        assert_eq!(set.iter().len(), 1);

        set.insert(LeftBrace);
        assert_eq!(set.iter().len(), 2);

        set.insert(LeftBrace);
        assert_eq!(set.iter().len(), 2);

        set.insert(RightParen);
        let mut iter = set.iter();
        assert_eq!(iter.len(), 3);

        assert_eq!(iter.next(), Some(LeftParen));
        assert_eq!(iter.len(), 2);

        assert_eq!(iter.next(), Some(RightParen));
        assert_eq!(iter.len(), 1);

        assert_eq!(iter.next(), Some(LeftBrace));
        assert_eq!(iter.len(), 0);

        assert_eq!(iter.next(), None);
        assert_eq!(iter.len(), 0);
    }

    #[test]
    fn test_from_iter() {
        let set = [LeftBrace, RightParen, LeftParen]
            .into_iter()
            .collect::<TokenSet>();

        assert_eq!(set.len(), 3);
        assert_eq!(set.contains(LeftParen), true);
        assert_eq!(set.contains(RightParen), true);
        assert_eq!(set.contains(LeftBrace), true);
        assert_eq!(set.contains(RightBrace), false);

        assert_eq!(
            set.iter().collect::<Vec<_>>(),
            vec![LeftParen, RightParen, LeftBrace]
        );
    }

    #[test]
    fn test_extend() {
        let mut set = TokenSet::empty();
        assert!(set.is_empty());

        set.extend([LeftBrace, RightParen, LeftParen]);

        assert_eq!(set.len(), 3);
        assert_eq!(set.contains(LeftParen), true);
        assert_eq!(set.contains(RightParen), true);
        assert_eq!(set.contains(LeftBrace), true);
        assert_eq!(set.contains(RightBrace), false);

        assert_eq!(
            set.iter().collect::<Vec<_>>(),
            vec![LeftParen, RightParen, LeftBrace]
        );

        set.extend([LeftParen, RightBrace]);

        assert_eq!(set.len(), 4);
        assert_eq!(set.contains(LeftParen), true);
        assert_eq!(set.contains(RightParen), true);
        assert_eq!(set.contains(LeftBrace), true);
        assert_eq!(set.contains(RightBrace), true);

        assert_eq!(
            set.iter().collect::<Vec<_>>(),
            vec![LeftParen, RightParen, LeftBrace, RightBrace]
        );
    }

    #[test]
    fn test_with_all() {
        let set = TokenSet::empty();

        let set = set.with_all([LeftBrace, RightParen, LeftParen]);

        assert_eq!(set.len(), 3);
        assert_eq!(set.contains(LeftParen), true);
        assert_eq!(set.contains(RightParen), true);
        assert_eq!(set.contains(LeftBrace), true);
        assert_eq!(set.contains(RightBrace), false);

        assert_eq!(
            set.iter().collect::<Vec<_>>(),
            vec![LeftParen, RightParen, LeftBrace]
        );

        let set = set.with_all([LeftParen, RightBrace]);

        assert_eq!(set.len(), 4);
        assert_eq!(set.contains(LeftParen), true);
        assert_eq!(set.contains(RightParen), true);
        assert_eq!(set.contains(LeftBrace), true);
        assert_eq!(set.contains(RightBrace), true);

        assert_eq!(
            set.iter().collect::<Vec<_>>(),
            vec![LeftParen, RightParen, LeftBrace, RightBrace]
        );
    }

    #[test]
    fn test_debug() {
        let mut set = TokenSet::empty();
        assert_eq!("[]", format!("{:?}", set));
        set.insert(LeftParen);
        assert_eq!("[LeftParen]", format!("{:?}", set));
        set.insert(RightParen);
        assert_eq!("[LeftParen, RightParen]", format!("{:?}", set));
    }
}
