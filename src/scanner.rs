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
    input: &'a str,
    source: Source<'a>,
}

impl<'a> Scanner<'a> {
    fn new(source: Source<'a>) -> Self {
        Self {
            source,
            input: source
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
            .ok_or_else(|| self.error(self.input, "", "Unterminated string"))
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
            .find(|c: char| !c.is_ascii_alphanumeric())
            .unwrap_or(self.input.len());

        if end == 0 {
            return None;
        }

        let (identifier, rest) = self.input.split_at(end);
        let typ = TokenType::from(identifier);

        self.advance(rest);
        Some(self.token(typ, identifier))
    }

    fn next_lexeme(&self) -> (&'a str, &'a str) {
        let idx = (1..=self.input.len())
            .find(|&i| self.input.is_char_boundary(i))
            .unwrap();
        self.input.split_at(idx)
    }

    fn next_lexeme_2(&self) -> (&'a str, &'a str) {
        let idx = (1..=self.input.len())
            .filter(|&i| self.input.is_char_boundary(i))
            .take(2)
            .last()
            .unwrap();
        self.input.split_at(idx)
    }

    fn advance(&mut self, to: &'a str) {
        self.input = to.trim_start_matches(|c: char| c.is_ascii_whitespace());
    }

    fn token(&self, typ: TokenType, lexeme: &'a str) -> Token {
        token(typ, lexeme, self.source.source)
    }

    fn error(&mut self, lexeme: &'a str, rest: &'a str, message: impl Into<String>) -> RunError {
        self.advance(rest);
        error(lexeme, self.source.source, message)
    }
}

fn token<'a>(typ: TokenType, token: &'a str, source: &'a str) -> Token {
    let offset = offset_from(token, source);
    let len = token.len();
    Token::new(typ, offset, len)
}

fn error<'a>(input: &'a str, source: &'a str, message: impl Into<String>) -> RunError {
    let offset = offset_from(input, source);
    let offset = offset.min(source.len() - 1);
    let source = &source[..=offset];
    let line_offset = source.bytes().rposition(|b| b == b'\n').unwrap_or(0);
    let line = source.lines().count();
    let offset = offset - line_offset;
    RunError::new(line, offset, message)
}

fn offset_from<'a>(input: &'a str, source: &'a str) -> usize {
    (input.as_ptr() as usize).saturating_sub(source.as_ptr() as usize)
}

#[cfg(feature = "chumsky")]
mod chum {
    use super::*;
    use ariadne::{Color, Fmt, Label, Report, ReportKind, Source as AriadneSource};
    use chumsky::{
        prelude::{filter, just, take_until, text, Parser, Simple},
        primitive::end,
        text::TextParser,
    };

    impl<'a> Source<'a> {
        pub fn into_chumsky(self) -> Result<Vec<Token>> {
            match lexer().parse(self.source) {
                Ok(tokens) => Ok(tokens),
                Err(errs) => {
                    let msg = errs
                        .into_iter()
                        .map(|err| {
                            let err = err.map(|c| c.to_string());

                            let report = Report::build(ReportKind::Error, (), err.span().start);

                            let report = match err.reason() {
                                chumsky::error::SimpleReason::Unclosed { span, delimiter } => {
                                    report
                                        .with_message(format!(
                                            "Unclosed delimiter {}",
                                            delimiter.fg(Color::Yellow)
                                        ))
                                        .with_label(
                                            Label::new(span.clone())
                                                .with_message(format!(
                                                    "Unclosed delimiter {}",
                                                    delimiter.fg(Color::Yellow)
                                                ))
                                                .with_color(Color::Yellow),
                                        )
                                        .with_label(
                                            Label::new(err.span())
                                                .with_message(format!(
                                                    "Must be closed before this {}",
                                                    err.found()
                                                        .unwrap_or(&"end of file".to_string())
                                                        .fg(Color::Red)
                                                ))
                                                .with_color(Color::Red),
                                        )
                                }
                                chumsky::error::SimpleReason::Unexpected => report
                                    .with_message(format!(
                                        "{}, expected {}",
                                        if err.found().is_some() {
                                            "Unexpected token in input"
                                        } else {
                                            "Unexpected end of input"
                                        },
                                        if err.expected().len() == 0 {
                                            "something else".to_string()
                                        } else {
                                            err.expected()
                                                .map(|expected| match expected {
                                                    Some(expected) => expected.to_string(),
                                                    None => "end of input".to_string(),
                                                })
                                                .collect::<Vec<_>>()
                                                .join(", ")
                                        }
                                    ))
                                    .with_label(
                                        Label::new(err.span())
                                            .with_message(format!(
                                                "Unexpected {}",
                                                err.found()
                                                    .map(|found| format!("token {}", found))
                                                    .unwrap_or_else(|| String::from("end of file"))
                                                    .fg(Color::Red)
                                            ))
                                            .with_color(Color::Red),
                                    ),
                                chumsky::error::SimpleReason::Custom(msg) => {
                                    report.with_message(msg).with_label(
                                        Label::new(err.span())
                                            .with_message(format!("{}", msg.fg(Color::Red)))
                                            .with_color(Color::Red),
                                    )
                                }
                            };

                            report.finish()
                        })
                        .fold(Vec::new(), |mut msg, report| {
                            report
                                .write(AriadneSource::from(self.source), &mut msg)
                                .unwrap();
                            msg.extend_from_slice(b"\n\n");
                            msg
                        });

                    let msg = String::from_utf8(msg).expect("ariadne writes utf8, hopefully");

                    Err(RunError::new(1, 0, msg))
                }
            }
        }
    }

    fn lexer() -> impl Parser<char, Vec<Token>, Error = Simple<char>> {
        let op = just('(')
            .to(TokenType::LeftParen)
            .or(just(')').to(TokenType::RightParen))
            .or(just('{').to(TokenType::LeftBrace))
            .or(just('}').to(TokenType::RightBrace))
            .or(just(',').to(TokenType::Comma))
            .or(just('.').to(TokenType::Dot))
            .or(just('-').to(TokenType::Minus))
            .or(just('+').to(TokenType::Plus))
            .or(just(';').to(TokenType::Semicolon))
            .or(just('*').to(TokenType::Star))
            .or(just('/').to(TokenType::Slash))
            .or(just("!=").to(TokenType::BangEqual))
            .or(just("==").to(TokenType::EqualEqual))
            .or(just("<=").to(TokenType::LessEqual))
            .or(just(">=").to(TokenType::GreaterEqual))
            .or(just('!').to(TokenType::Bang))
            .or(just('=').to(TokenType::Equal))
            .or(just('<').to(TokenType::Less))
            .or(just('>').to(TokenType::Greater))
            .map_with_span(|typ, span| Token::from((typ, span)));

        let num = text::int(10)
            .then(just('.').ignore_then(text::digits(10)).or_not())
            .map_with_span(|_num, span| Token::from((TokenType::Number, span)));

        let string = just('"')
            .ignore_then(
                filter(|c| *c != '"')
                    .repeated()
                    .map_with_span(|_string, span| Token::from((TokenType::String, span))),
            )
            .then_ignore(just('"'));

        let ident = text::ident().map_with_span(|ident: String, span| {
            let typ = TokenType::from(ident.as_str());
            Token::from((typ, span))
        });

        let token = num.or(string).or(op).or(ident);

        let comment = just("//").then(take_until(just('\n'))).padded();

        token
            .padded_by(comment.repeated())
            .padded()
            .repeated()
            .then_ignore(end())
    }
}

#[cfg(feature = "nom")]
mod no {
    use super::*;
    use nom::{
        branch::alt,
        bytes::complete::{tag, take_until},
        character::complete::{alpha1, alphanumeric0, char, digit1, multispace0},
        combinator::{all_consuming, consumed, cut, map, opt, recognize, value},
        error::ErrorKind,
        multi::many0,
        sequence::{pair, preceded, terminated, tuple},
        Finish, Parser,
    };

    type NErr<I> = nom::error::Error<I>;
    type NRes<I, O, E = NErr<I>> = Result<(I, O), nom::Err<E>>;

    impl<'a> Source<'a> {
        pub fn into_nom(self) -> Result<Vec<Token>> {
            let mut lexer = self.lexer();
            let res = lexer(self.source).finish();
            match res {
                Ok((_, tokens)) => Ok(tokens),
                Err(e) => Err(self.convert_err(e)),
            }
        }
    }

    impl<'a> Source<'a> {
        fn convert_err(&self, err: NErr<&'a str>) -> RunError {
            match err.code {
                ErrorKind::Eof => error(
                    err.input,
                    self.source,
                    format!(
                        "Unexpected character: {}",
                        err.input.chars().next().unwrap_or_default()
                    ),
                ),
                ErrorKind::Char | ErrorKind::TakeUntil => {
                    error(err.input, self.source, "Unterminated string")
                }
                _ => error(err.input, self.source, err.to_string()),
            }
        }

        fn as_token<F>(&self, parser: F) -> impl FnMut(&'a str) -> NRes<&'a str, Token>
        where
            F: Parser<&'a str, TokenType, NErr<&'a str>>,
        {
            let mut parser = consumed(parser);
            let source = self.source;
            move |input| {
                let (input, (consumed, typ)) = parser(input)?;
                let token = token(typ, consumed, source);
                Ok((input, token))
            }
        }

        fn op(&self) -> impl FnMut(&'a str) -> NRes<&'a str, Token> {
            let op = alt((
                value(TokenType::LeftParen, char('(')),
                value(TokenType::RightParen, char(')')),
                value(TokenType::LeftBrace, char('{')),
                value(TokenType::RightBrace, char('}')),
                value(TokenType::Comma, char(',')),
                value(TokenType::Dot, char('.')),
                value(TokenType::Minus, char('-')),
                value(TokenType::Plus, char('+')),
                value(TokenType::Semicolon, char(';')),
                value(TokenType::Star, char('*')),
                value(TokenType::Slash, char('/')),
                value(TokenType::Bang, char('!')),
                value(TokenType::Equal, char('=')),
                value(TokenType::Less, char('<')),
                value(TokenType::Greater, char('>')),
            ));
            self.as_token(op)
        }

        fn two_op(&self) -> impl FnMut(&'a str) -> NRes<&'a str, Token> {
            let op = alt((
                value(TokenType::BangEqual, tag("!=")),
                value(TokenType::EqualEqual, tag("==")),
                value(TokenType::LessEqual, tag("<=")),
                value(TokenType::GreaterEqual, tag(">=")),
            ));
            self.as_token(op)
        }

        fn num(&self) -> impl FnMut(&'a str) -> NRes<&'a str, Token> {
            let num = tuple((digit1, opt(pair(char('.'), digit1))));
            let num = value(TokenType::Number, num);
            self.as_token(num)
        }

        fn string(&self) -> impl FnMut(&'a str) -> NRes<&'a str, Token> {
            let string = value(TokenType::String, take_until("\""));
            let string = self.as_token(string);
            let string = terminated(string, char('\"'));
            preceded(char('\"'), cut(string))
        }

        fn ident(&self) -> impl FnMut(&'a str) -> NRes<&'a str, Token> {
            let ident = recognize(pair(alpha1, alphanumeric0));
            let ident = map(ident, TokenType::from);
            self.as_token(ident)
        }

        fn token(&self) -> impl FnMut(&'a str) -> NRes<&'a str, Token> {
            alt((
                self.ident(),
                self.string(),
                self.num(),
                self.two_op(),
                self.op(),
            ))
        }

        fn comment(&self) -> impl FnMut(&'a str) -> NRes<&'a str, ()> {
            value((), preceded(tag("//"), take_until("\n")))
        }

        fn lexer(&self) -> impl FnMut(&'a str) -> NRes<&'a str, Vec<Token>> {
            let comment = preceded(multispace0, self.comment());
            let comment = many0(comment);
            let token = preceded(multispace0, self.token());
            let token = preceded(comment, token);
            let token = many0(token);

            let comment = preceded(multispace0, self.comment());
            let comment = many0(comment);
            let token = terminated(token, comment);
            let token = terminated(token, multispace0);

            all_consuming(token)
        }
    }
}
