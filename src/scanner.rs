use crate::Range;

use super::{CroxError, CroxErrorKind, CroxErrors, Result, Token, TokenType};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Source<'env> {
    pub source: &'env str,
}

impl<'env> Source<'env> {
    pub fn new(source: &'env str) -> Self {
        Self { source }
    }

    pub fn slice(&self, range: impl Into<Range>) -> &'env str {
        &self.source[range.into()]
    }
}

impl<'env> Source<'env> {
    pub fn scan_all(self) -> Result<Vec<Token>, CroxErrors> {
        let source = self.source;
        let mut oks = Vec::new();
        let mut errs = Vec::new();
        for x in self {
            match x {
                Ok(t) => oks.push(t),
                Err(e) => errs.push(e),
            }
        }
        if errs.is_empty() {
            Ok(oks)
        } else {
            Err(CroxErrors::from((source, errs)))
        }
    }
}

impl<'env> IntoIterator for Source<'env> {
    type Item = Result<Token>;
    type IntoIter = Scanner<'env>;

    fn into_iter(self) -> Self::IntoIter {
        Scanner::from(self)
    }
}

#[derive(Clone, Debug)]
pub struct Scanner<'env> {
    input: &'env str,
    source: Source<'env>,
}

impl<'env> From<Source<'env>> for Scanner<'env> {
    fn from(source: Source<'env>) -> Self {
        Self {
            source,
            input: source
                .source
                .trim_matches(|c: char| c.is_ascii_whitespace()),
        }
    }
}

impl<'env> Iterator for Scanner<'env> {
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

impl<'env> Scanner<'env> {
    fn is_at_end(&self) -> bool {
        self.input.is_empty()
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

                let input = token.chars().next();
                let kind = CroxErrorKind::of(input);
                return Err(self.error(token, rest, kind));
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
        if let Some(rest) = self.input.strip_prefix("//") {
            let nl = rest.find(|b| b == '\n').unwrap_or(rest.len());
            self.advance(&rest[nl..]);
            Some(())
        } else {
            None
        }
    }

    fn string(&mut self) -> Result<Token> {
        let source = &self.input[1..];
        source
            .find('"')
            .map(|end| {
                let (string, rest) = source.split_at(end + 1);
                let string = &string[..end];
                self.advance(rest);
                self.token(TokenType::String, string)
            })
            .ok_or_else(|| self.error(self.input, "", CroxErrorKind::UnclosedStringLiteral))
    }

    fn number(&mut self) -> Option<Token> {
        let mut has_dot = false;

        let end = self
            .input
            .find(move |c: char| match c {
                '0'..='9' => false,
                '.' if !has_dot => {
                    has_dot = true;
                    false
                }
                _ => true,
            })
            .unwrap_or(self.input.len());

        if end == 0 {
            return None;
        }

        let end = end - usize::from(self.input.as_bytes()[end - 1] == b'.');
        let (number, rest) = self.input.split_at(end);
        self.advance(rest);
        Some(self.token(TokenType::Number, number))
    }

    fn identifier(&mut self) -> Option<Token> {
        let end = self
            .input
            .find(|c: char| !matches!(c, '0'..='9' | 'A'..='Z' | 'a'..='z' | '_'))
            .unwrap_or(self.input.len());

        if end == 0 {
            return None;
        }

        let (identifier, rest) = self.input.split_at(end);
        let typ = TokenType::from(identifier);

        self.advance(rest);
        Some(self.token(typ, identifier))
    }

    fn next_lexeme(&self) -> (&'env str, &'env str) {
        let idx = (1..=self.input.len())
            .find(|&i| self.input.is_char_boundary(i))
            .unwrap();
        self.input.split_at(idx)
    }

    fn next_lexeme_2(&self) -> (&'env str, &'env str) {
        let idx = (1..=self.input.len())
            .filter(|&i| self.input.is_char_boundary(i))
            .take(2)
            .last()
            .unwrap();
        self.input.split_at(idx)
    }

    fn advance(&mut self, to: &'env str) {
        self.input = to.trim_start_matches(|c: char| c.is_ascii_whitespace());
    }

    fn token(&self, typ: TokenType, lexeme: &'env str) -> Token {
        token(typ, lexeme, self.source.source)
    }

    fn error(&mut self, lexeme: &'env str, rest: &'env str, kind: CroxErrorKind) -> CroxError {
        self.advance(rest);
        error(lexeme, self.source.source, kind)
    }
}

fn token<'env>(typ: TokenType, token: &'env str, source: &'env str) -> Token {
    let offset = offset_from(token, source);
    let len = token.len();
    Token::new(typ, offset, len)
}

fn error<'env>(input: &'env str, source: &'env str, kind: CroxErrorKind) -> CroxError {
    let offset = offset_from(input, source);
    let len = input.len().min(1);
    let span = offset..(offset + len);
    CroxError::new(kind, span)
}

fn offset_from<'env>(input: &'env str, source: &'env str) -> usize {
    (input.as_ptr() as usize).saturating_sub(source.as_ptr() as usize)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unexpected_bracket() {
        let input = Source::new("foo [ bar");
        let err = input
            .into_iter()
            .collect::<Result<Vec<_>, _>>()
            .unwrap_err();
        assert_eq!(err.kind, CroxErrorKind::UnexpectedInput { input: '[' });
        assert_eq!(err.span, 4..5);
    }

    #[test]
    fn test_unclosed_string() {
        let input = Source::new("foo \"bar");
        let err = input
            .into_iter()
            .collect::<Result<Vec<_>, _>>()
            .unwrap_err();
        assert_eq!(err.kind, CroxErrorKind::UnclosedStringLiteral);
        assert_eq!(err.span, 4..5);
    }
}
