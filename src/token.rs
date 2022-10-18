#[derive(Copy, Clone, Debug, PartialEq, Eq)]
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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Token {
    pub typ: TokenType,
    pub offset: usize,
    pub len: usize,
}

impl Token {
    pub fn new(typ: TokenType, offset: usize, len: usize) -> Self {
        Self { typ, offset, len }
    }
}

pub type Span = std::ops::Range<usize>;

impl From<(TokenType, Span)> for Token {
    fn from((typ, span): (TokenType, Span)) -> Self {
        Self {
            typ,
            offset: span.start,
            len: span.len(),
        }
    }
}
