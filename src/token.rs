use crate::{EnumSet, ValueEnum};
use std::fmt::{self, Debug};

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

impl ValueEnum for TokenType {
    fn to_ord(&self) -> u8 {
        *self as u8
    }

    unsafe fn from_ord(ord: u8) -> Self {
        std::mem::transmute_copy(&ord)
    }
}

pub type TokenSet = EnumSet<TokenType>;
