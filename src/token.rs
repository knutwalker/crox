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

pub type Span = std::ops::Range<usize>;

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

    pub fn span(&self) -> Span {
        self.offset..(self.offset + self.len)
    }
}

impl From<(TokenType, Span)> for Token {
    fn from((typ, span): (TokenType, Span)) -> Self {
        Self {
            typ,
            offset: span.start,
            len: span.len(),
        }
    }
}
