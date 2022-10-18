use super::{Result, RunError, Token, TokenType};

#[derive(Copy, Clone, Debug)]
pub struct Source<'a> {
    source: &'a str,
}

impl<'a> Source<'a> {
    pub fn new(source: &'a str) -> Self {
        Self { source }
    }
}

impl<'a> IntoIterator for Source<'a> {
    type Item = Result<Token>;
    type IntoIter = Scanner<'a>;

    fn into_iter(self) -> Self::IntoIter {
        Scanner::new(self)
    }
}

#[derive(Clone, Debug)]
pub struct Scanner<'a> {
    source: &'a str,
    origin: Source<'a>,
}

impl<'a> Scanner<'a> {
    fn new(origin: Source<'a>) -> Self {
        Self {
            origin,
            source: origin
                .source
                .trim_matches(|c: char| c.is_ascii_whitespace()),
        }
    }
}

impl Iterator for Scanner<'_> {
    type Item = Result<Token>;

    fn next(&mut self) -> Option<Self::Item> {
        while !self.is_at_end() {
            if let Some(res) = self.next_token().transpose() {
                return Some(res);
            }
        }
        None
    }
}

impl<'a> Scanner<'a> {
    fn is_at_end(&self) -> bool {
        self.source.is_empty()
    }

    fn next_token(&mut self) -> Result<Option<Token>> {
        let (token, rest) = self.next_lexeme();

        let typ = match token {
            "(" => TokenType::LeftParen,
            ")" => TokenType::RightParen,
            "{" => TokenType::LeftBrace,
            "}" => TokenType::RightBrace,
            "," => TokenType::Comma,
            "." => TokenType::Dot,
            "-" => TokenType::Minus,
            "+" => TokenType::Plus,
            ";" => TokenType::Semicolon,
            "*" => TokenType::Star,
            "!" | "=" | "<" | ">" => {
                if let Some(next) = self.next_bi_token() {
                    return Ok(Some(next));
                }
                match token {
                    "!" => TokenType::Bang,
                    "=" => TokenType::Equal,
                    "<" => TokenType::Less,
                    ">" => TokenType::Greater,
                    _ => unreachable!(),
                }
            }
            "/" => {
                if self.comment().is_some() {
                    return Ok(None);
                }
                TokenType::Slash
            }
            "\"" => {
                return Ok(Some(self.string()?));
            }
            _ => {
                if let Some(next) = self.number() {
                    return Ok(Some(next));
                }
                if let Some(next) = self.identifier() {
                    return Ok(Some(next));
                }

                return Err(self.error(token, rest, format!("Unexpected character: {}", token)));
            }
        };

        self.advance(rest);
        Ok(Some(self.token(typ, token)))
    }

    fn next_bi_token(&mut self) -> Option<Token> {
        let (token, rest) = self.next_lexeme_2();
        let typ = match token {
            "!=" => TokenType::BangEqual,
            "==" => TokenType::EqualEqual,
            "<=" => TokenType::LessEqual,
            ">=" => TokenType::GreaterEqual,
            _ => return None,
        };
        self.advance(rest);
        Some(self.token(typ, token))
    }

    fn comment(&mut self) -> Option<()> {
        if let Some(rest) = self.source.strip_prefix("//") {
            let nl = rest.find(|b| b == '\n').unwrap_or(rest.len());
            self.advance(&rest[nl..]);
            Some(())
        } else {
            None
        }
    }

    fn string(&mut self) -> Result<Token> {
        let source = &self.source[1..];
        source
            .find('"')
            .map(|end| {
                let (string, rest) = source.split_at(end + 1);
                let string = &string[..end];
                self.advance(rest);
                self.token(TokenType::String, string)
            })
            .ok_or_else(|| self.error(self.source, "", "Unterminated string"))
    }

    fn number(&mut self) -> Option<Token> {
        let mut has_dot = false;

        let end = self
            .source
            .find(move |c: char| match c {
                '0'..='9' => false,
                '.' if !has_dot => {
                    has_dot = true;
                    false
                }
                _ => true,
            })
            .unwrap_or(self.source.len());

        if end == 0 {
            return None;
        }

        let end = end - usize::from(self.source.as_bytes()[end - 1] == b'.');
        let (number, rest) = self.source.split_at(end);
        self.advance(rest);
        Some(self.token(TokenType::Number, number))
    }

    fn identifier(&mut self) -> Option<Token> {
        let end = self
            .source
            .find(|c: char| !c.is_ascii_alphanumeric())
            .unwrap_or(self.source.len());

        if end == 0 {
            return None;
        }

        let (identifier, rest) = self.source.split_at(end);

        let typ = match identifier {
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
        };

        self.advance(rest);
        Some(self.token(typ, identifier))
    }

    fn next_lexeme(&self) -> (&'a str, &'a str) {
        let idx = (1..=self.source.len())
            .find(|&i| self.source.is_char_boundary(i))
            .unwrap();
        self.source.split_at(idx)
    }

    fn next_lexeme_2(&self) -> (&'a str, &'a str) {
        let idx = (1..=self.source.len())
            .filter(|&i| self.source.is_char_boundary(i))
            .take(2)
            .last()
            .unwrap();
        self.source.split_at(idx)
    }

    fn advance(&mut self, to: &'a str) {
        self.source = to.trim_start_matches(|c: char| c.is_ascii_whitespace());
    }

    fn token(&self, typ: TokenType, lexeme: &'a str) -> Token {
        let offset = Self::offset_from(lexeme, self.origin.source);
        let len = lexeme.len();
        Token::new(typ, offset, len)
    }

    fn error(&mut self, lexeme: &'a str, rest: &'a str, message: impl Into<String>) -> RunError {
        self.advance(rest);

        let offset = Self::offset_from(lexeme, self.origin.source);
        let origin = &self.origin.source[..=offset];
        let line_offset = origin.bytes().rposition(|b| b == b'\n').unwrap_or(0);
        let line = origin.lines().count();
        let offset = offset - line_offset;
        RunError::new(line, offset, message)
    }

    fn offset_from(source: &'a str, origin: &'a str) -> usize {
        (source.as_ptr() as usize).saturating_sub(origin.as_ptr() as usize)
    }
}
