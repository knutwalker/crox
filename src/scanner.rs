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
        let offset = offset_from(lexeme, self.source.source);
        let len = lexeme.len();
        Token::new(typ, offset, len)
    }

    fn error(&mut self, lexeme: &'a str, rest: &'a str, message: impl Into<String>) -> RunError {
        self.advance(rest);

        let offset = offset_from(lexeme, self.source.source);
        let source = &self.source.source[..=offset];
        let line_offset = source.bytes().rposition(|b| b == b'\n').unwrap_or(0);
        let line = source.lines().count();
        let offset = offset - line_offset;
        RunError::new(line, offset, message)
    }
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
            let typ = match ident.as_str() {
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
    use crate::token::Span;
    use nom::{
        branch::alt,
        bytes::complete::{tag, take_until, take_while1},
        character::complete::{alphanumeric1, char, digit1, multispace0},
        combinator::{all_consuming, cut, into, map_parser, opt, value},
        multi::many0,
        sequence::{pair, preceded, terminated, tuple},
        IResult, Parser,
    };

    impl<'a> Source<'a> {
        pub fn into_nom(self) -> Result<Vec<Token>> {
            let mut lexer = self.lexer();
            let res = lexer(self.source);
            match res {
                Ok((_, tokens)) => Ok(tokens),
                Err(e) => Err(RunError::new(1, 0, e.to_string())),
            }
        }
    }

    impl<'a> Source<'a> {
        fn spanned<O, F>(&self, mut parser: F) -> impl FnMut(&'a str) -> IResult<&'a str, (O, Span)>
        where
            F: Parser<&'a str, O, nom::error::Error<&'a str>>,
        {
            let source = self.source;
            move |input| {
                let start = offset_from(input, source);
                let (input, output) = parser.parse(input)?;
                let end = offset_from(input, source);
                Ok((input, (output, start..end)))
            }
        }

        fn as_token<F, O>(
            &self,
            typ: TokenType,
            parser: F,
        ) -> impl FnMut(&'a str) -> IResult<&'a str, Token>
        where
            F: Parser<&'a str, O, nom::error::Error<&'a str>>,
        {
            into(self.spanned(value(typ, parser)))
        }

        fn op(&self) -> impl FnMut(&'a str) -> IResult<&'a str, Token> {
            let op = alt((
                value(TokenType::LeftParen, tag("(")),
                value(TokenType::RightParen, tag(")")),
                value(TokenType::LeftBrace, tag("{")),
                value(TokenType::RightBrace, tag("}")),
                value(TokenType::Comma, tag(",")),
                value(TokenType::Dot, tag(".")),
                value(TokenType::Minus, tag("-")),
                value(TokenType::Plus, tag("+")),
                value(TokenType::Semicolon, tag(";")),
                value(TokenType::Star, tag("*")),
                value(TokenType::Slash, tag("/")),
                value(TokenType::BangEqual, tag("!=")),
                value(TokenType::EqualEqual, tag("==")),
                value(TokenType::LessEqual, tag("<=")),
                value(TokenType::GreaterEqual, tag(">=")),
                value(TokenType::Bang, tag("!")),
                value(TokenType::Equal, tag("=")),
                value(TokenType::Less, tag("<")),
                value(TokenType::Greater, tag(">")),
            ));
            into(self.spanned(op))
        }

        fn num(&self) -> impl FnMut(&'a str) -> IResult<&'a str, Token> {
            let num = tuple((digit1, opt(pair(char('.'), digit1))));
            self.as_token(TokenType::Number, num)
        }

        fn string(&self) -> impl FnMut(&'a str) -> IResult<&'a str, Token> {
            let string = take_until("\"");
            let string = self.as_token(TokenType::String, string);
            let string = terminated(string, char('\"'));
            preceded(char('\"'), cut(string))
        }

        fn ident(&self) -> impl FnMut(&'a str) -> IResult<&'a str, Token> {
            let ident_token = alt((
                value(TokenType::And, all_consuming(tag("and"))),
                value(TokenType::Class, all_consuming(tag("class"))),
                value(TokenType::Else, all_consuming(tag("else"))),
                value(TokenType::False, all_consuming(tag("false"))),
                value(TokenType::Fun, all_consuming(tag("fun"))),
                value(TokenType::For, all_consuming(tag("for"))),
                value(TokenType::If, all_consuming(tag("if"))),
                value(TokenType::Nil, all_consuming(tag("nil"))),
                value(TokenType::Or, all_consuming(tag("or"))),
                value(TokenType::Print, all_consuming(tag("print"))),
                value(TokenType::Return, all_consuming(tag("return"))),
                value(TokenType::Super, all_consuming(tag("super"))),
                value(TokenType::This, all_consuming(tag("this"))),
                value(TokenType::True, all_consuming(tag("true"))),
                value(TokenType::Var, all_consuming(tag("var"))),
                value(TokenType::While, all_consuming(tag("while"))),
                value(TokenType::Identifier, all_consuming(alphanumeric1)),
            ));

            let ident = take_while1(|c: char| c.is_ascii_alphabetic());
            let ident = map_parser(ident, ident_token);

            into(self.spanned(ident))
        }

        fn token(&self) -> impl FnMut(&'a str) -> IResult<&'a str, Token> {
            alt((self.op(), self.num(), self.string(), self.ident()))
        }

        fn comment(&self) -> impl FnMut(&'a str) -> IResult<&'a str, ()> {
            value((), preceded(tag("//"), take_until("\n")))
        }

        fn lexer(&self) -> impl FnMut(&'a str) -> IResult<&'a str, Vec<Token>> {
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

#[cfg(test)]
mod tests {
    use super::*;
    use TokenType::*;

    fn run_test(content: &str, expected: Vec<Token>) -> Result {
        use pretty_assertions::assert_eq;

        let source = Source::new(content);
        let actual = source.into_iter().collect::<Result<Vec<_>>>()?;
        assert_eq!(actual, expected);

        #[cfg(feature = "chumsky")]
        {
            let actual = source.into_chumsky()?;
            assert_eq!(actual, expected);
        }

        #[cfg(feature = "nom")]
        {
            let actual = source.into_nom()?;
            assert_eq!(actual, expected);
        }

        Ok(())
    }

    #[test]
    fn test_classes() -> Result {
        run_test(
            include_str!("../tests/classes.crox"),
            vec![
                Token {
                    typ: Class,
                    offset: 0,
                    len: 5,
                },
                Token {
                    typ: Identifier,
                    offset: 6,
                    len: 9,
                },
                Token {
                    typ: LeftBrace,
                    offset: 16,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 22,
                    len: 4,
                },
                Token {
                    typ: LeftParen,
                    offset: 26,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 27,
                    len: 4,
                },
                Token {
                    typ: Comma,
                    offset: 31,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 33,
                    len: 5,
                },
                Token {
                    typ: RightParen,
                    offset: 38,
                    len: 1,
                },
                Token {
                    typ: LeftBrace,
                    offset: 40,
                    len: 1,
                },
                Token {
                    typ: This,
                    offset: 50,
                    len: 4,
                },
                Token {
                    typ: Dot,
                    offset: 54,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 55,
                    len: 4,
                },
                Token {
                    typ: Equal,
                    offset: 60,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 62,
                    len: 4,
                },
                Token {
                    typ: Semicolon,
                    offset: 66,
                    len: 1,
                },
                Token {
                    typ: This,
                    offset: 76,
                    len: 4,
                },
                Token {
                    typ: Dot,
                    offset: 80,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 81,
                    len: 5,
                },
                Token {
                    typ: Equal,
                    offset: 87,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 89,
                    len: 5,
                },
                Token {
                    typ: Semicolon,
                    offset: 94,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 100,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 107,
                    len: 4,
                },
                Token {
                    typ: LeftParen,
                    offset: 111,
                    len: 1,
                },
                Token {
                    typ: RightParen,
                    offset: 112,
                    len: 1,
                },
                Token {
                    typ: LeftBrace,
                    offset: 114,
                    len: 1,
                },
                Token {
                    typ: Print,
                    offset: 124,
                    len: 5,
                },
                Token {
                    typ: String,
                    offset: 131,
                    len: 14,
                },
                Token {
                    typ: Semicolon,
                    offset: 146,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 152,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 159,
                    len: 5,
                },
                Token {
                    typ: LeftParen,
                    offset: 164,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 165,
                    len: 3,
                },
                Token {
                    typ: RightParen,
                    offset: 168,
                    len: 1,
                },
                Token {
                    typ: LeftBrace,
                    offset: 170,
                    len: 1,
                },
                Token {
                    typ: Print,
                    offset: 180,
                    len: 5,
                },
                Token {
                    typ: String,
                    offset: 187,
                    len: 11,
                },
                Token {
                    typ: Plus,
                    offset: 200,
                    len: 1,
                },
                Token {
                    typ: This,
                    offset: 202,
                    len: 4,
                },
                Token {
                    typ: Dot,
                    offset: 206,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 207,
                    len: 4,
                },
                Token {
                    typ: Plus,
                    offset: 212,
                    len: 1,
                },
                Token {
                    typ: String,
                    offset: 215,
                    len: 5,
                },
                Token {
                    typ: Plus,
                    offset: 222,
                    len: 1,
                },
                Token {
                    typ: This,
                    offset: 224,
                    len: 4,
                },
                Token {
                    typ: Dot,
                    offset: 228,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 229,
                    len: 5,
                },
                Token {
                    typ: Plus,
                    offset: 235,
                    len: 1,
                },
                Token {
                    typ: String,
                    offset: 238,
                    len: 2,
                },
                Token {
                    typ: Plus,
                    offset: 242,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 244,
                    len: 3,
                },
                Token {
                    typ: Plus,
                    offset: 248,
                    len: 1,
                },
                Token {
                    typ: String,
                    offset: 251,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 253,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 259,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 261,
                    len: 1,
                },
                Token {
                    typ: Var,
                    offset: 289,
                    len: 3,
                },
                Token {
                    typ: Identifier,
                    offset: 293,
                    len: 12,
                },
                Token {
                    typ: Equal,
                    offset: 306,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 308,
                    len: 9,
                },
                Token {
                    typ: Semicolon,
                    offset: 317,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 345,
                    len: 12,
                },
                Token {
                    typ: LeftParen,
                    offset: 357,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 358,
                    len: 9,
                },
                Token {
                    typ: RightParen,
                    offset: 367,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 368,
                    len: 1,
                },
                Token {
                    typ: Var,
                    offset: 371,
                    len: 3,
                },
                Token {
                    typ: Identifier,
                    offset: 375,
                    len: 9,
                },
                Token {
                    typ: Equal,
                    offset: 385,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 387,
                    len: 9,
                },
                Token {
                    typ: LeftParen,
                    offset: 396,
                    len: 1,
                },
                Token {
                    typ: String,
                    offset: 398,
                    len: 5,
                },
                Token {
                    typ: Comma,
                    offset: 404,
                    len: 1,
                },
                Token {
                    typ: String,
                    offset: 407,
                    len: 5,
                },
                Token {
                    typ: RightParen,
                    offset: 413,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 414,
                    len: 1,
                },
                Token {
                    typ: Print,
                    offset: 416,
                    len: 5,
                },
                Token {
                    typ: Identifier,
                    offset: 422,
                    len: 9,
                },
                Token {
                    typ: Semicolon,
                    offset: 431,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 457,
                    len: 9,
                },
                Token {
                    typ: Dot,
                    offset: 466,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 467,
                    len: 5,
                },
                Token {
                    typ: LeftParen,
                    offset: 472,
                    len: 1,
                },
                Token {
                    typ: String,
                    offset: 474,
                    len: 11,
                },
                Token {
                    typ: RightParen,
                    offset: 486,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 487,
                    len: 1,
                },
                Token {
                    typ: Class,
                    offset: 537,
                    len: 5,
                },
                Token {
                    typ: Identifier,
                    offset: 543,
                    len: 6,
                },
                Token {
                    typ: Less,
                    offset: 550,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 552,
                    len: 9,
                },
                Token {
                    typ: LeftBrace,
                    offset: 562,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 568,
                    len: 4,
                },
                Token {
                    typ: LeftParen,
                    offset: 572,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 573,
                    len: 4,
                },
                Token {
                    typ: Comma,
                    offset: 577,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 579,
                    len: 5,
                },
                Token {
                    typ: Comma,
                    offset: 584,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 586,
                    len: 5,
                },
                Token {
                    typ: RightParen,
                    offset: 591,
                    len: 1,
                },
                Token {
                    typ: LeftBrace,
                    offset: 593,
                    len: 1,
                },
                Token {
                    typ: Super,
                    offset: 603,
                    len: 5,
                },
                Token {
                    typ: LeftParen,
                    offset: 608,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 609,
                    len: 4,
                },
                Token {
                    typ: Comma,
                    offset: 613,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 615,
                    len: 5,
                },
                Token {
                    typ: RightParen,
                    offset: 620,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 621,
                    len: 1,
                },
                Token {
                    typ: This,
                    offset: 631,
                    len: 4,
                },
                Token {
                    typ: Dot,
                    offset: 635,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 636,
                    len: 5,
                },
                Token {
                    typ: Equal,
                    offset: 642,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 644,
                    len: 5,
                },
                Token {
                    typ: Semicolon,
                    offset: 649,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 655,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 662,
                    len: 5,
                },
                Token {
                    typ: LeftParen,
                    offset: 667,
                    len: 1,
                },
                Token {
                    typ: RightParen,
                    offset: 668,
                    len: 1,
                },
                Token {
                    typ: LeftBrace,
                    offset: 670,
                    len: 1,
                },
                Token {
                    typ: Print,
                    offset: 680,
                    len: 5,
                },
                Token {
                    typ: String,
                    offset: 687,
                    len: 12,
                },
                Token {
                    typ: Plus,
                    offset: 701,
                    len: 1,
                },
                Token {
                    typ: This,
                    offset: 703,
                    len: 4,
                },
                Token {
                    typ: Dot,
                    offset: 707,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 708,
                    len: 5,
                },
                Token {
                    typ: Plus,
                    offset: 714,
                    len: 1,
                },
                Token {
                    typ: String,
                    offset: 717,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 719,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 725,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 727,
                    len: 1,
                },
                Token {
                    typ: Var,
                    offset: 731,
                    len: 3,
                },
                Token {
                    typ: Identifier,
                    offset: 735,
                    len: 8,
                },
                Token {
                    typ: Equal,
                    offset: 744,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 746,
                    len: 6,
                },
                Token {
                    typ: LeftParen,
                    offset: 752,
                    len: 1,
                },
                Token {
                    typ: String,
                    offset: 754,
                    len: 3,
                },
                Token {
                    typ: Comma,
                    offset: 758,
                    len: 1,
                },
                Token {
                    typ: String,
                    offset: 761,
                    len: 14,
                },
                Token {
                    typ: RightParen,
                    offset: 776,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 777,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 779,
                    len: 8,
                },
                Token {
                    typ: Dot,
                    offset: 787,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 788,
                    len: 5,
                },
                Token {
                    typ: LeftParen,
                    offset: 793,
                    len: 1,
                },
                Token {
                    typ: String,
                    offset: 795,
                    len: 12,
                },
                Token {
                    typ: RightParen,
                    offset: 808,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 809,
                    len: 1,
                },
            ],
        )
    }

    #[test]
    fn test_control_flow() -> Result {
        run_test(
            include_str!("../tests/control_flow.crox"),
            vec![
                Token {
                    typ: If,
                    offset: 0,
                    len: 2,
                },
                Token {
                    typ: LeftParen,
                    offset: 3,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 4,
                    len: 9,
                },
                Token {
                    typ: RightParen,
                    offset: 13,
                    len: 1,
                },
                Token {
                    typ: LeftBrace,
                    offset: 15,
                    len: 1,
                },
                Token {
                    typ: Print,
                    offset: 21,
                    len: 5,
                },
                Token {
                    typ: String,
                    offset: 28,
                    len: 3,
                },
                Token {
                    typ: Semicolon,
                    offset: 32,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 34,
                    len: 1,
                },
                Token {
                    typ: Else,
                    offset: 36,
                    len: 4,
                },
                Token {
                    typ: LeftBrace,
                    offset: 41,
                    len: 1,
                },
                Token {
                    typ: Print,
                    offset: 47,
                    len: 5,
                },
                Token {
                    typ: String,
                    offset: 54,
                    len: 2,
                },
                Token {
                    typ: Semicolon,
                    offset: 57,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 59,
                    len: 1,
                },
                Token {
                    typ: Var,
                    offset: 63,
                    len: 3,
                },
                Token {
                    typ: Identifier,
                    offset: 67,
                    len: 1,
                },
                Token {
                    typ: Equal,
                    offset: 69,
                    len: 1,
                },
                Token {
                    typ: Number,
                    offset: 71,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 72,
                    len: 1,
                },
                Token {
                    typ: While,
                    offset: 74,
                    len: 5,
                },
                Token {
                    typ: LeftParen,
                    offset: 80,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 81,
                    len: 1,
                },
                Token {
                    typ: Less,
                    offset: 83,
                    len: 1,
                },
                Token {
                    typ: Number,
                    offset: 85,
                    len: 2,
                },
                Token {
                    typ: RightParen,
                    offset: 87,
                    len: 1,
                },
                Token {
                    typ: LeftBrace,
                    offset: 89,
                    len: 1,
                },
                Token {
                    typ: Print,
                    offset: 95,
                    len: 5,
                },
                Token {
                    typ: Identifier,
                    offset: 101,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 102,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 108,
                    len: 1,
                },
                Token {
                    typ: Equal,
                    offset: 110,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 112,
                    len: 1,
                },
                Token {
                    typ: Plus,
                    offset: 114,
                    len: 1,
                },
                Token {
                    typ: Number,
                    offset: 116,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 117,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 119,
                    len: 1,
                },
                Token {
                    typ: For,
                    offset: 122,
                    len: 3,
                },
                Token {
                    typ: LeftParen,
                    offset: 126,
                    len: 1,
                },
                Token {
                    typ: Var,
                    offset: 127,
                    len: 3,
                },
                Token {
                    typ: Identifier,
                    offset: 131,
                    len: 1,
                },
                Token {
                    typ: Equal,
                    offset: 133,
                    len: 1,
                },
                Token {
                    typ: Number,
                    offset: 135,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 136,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 138,
                    len: 1,
                },
                Token {
                    typ: Less,
                    offset: 140,
                    len: 1,
                },
                Token {
                    typ: Number,
                    offset: 142,
                    len: 2,
                },
                Token {
                    typ: Semicolon,
                    offset: 144,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 146,
                    len: 1,
                },
                Token {
                    typ: Equal,
                    offset: 148,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 150,
                    len: 1,
                },
                Token {
                    typ: Plus,
                    offset: 152,
                    len: 1,
                },
                Token {
                    typ: Number,
                    offset: 154,
                    len: 1,
                },
                Token {
                    typ: RightParen,
                    offset: 155,
                    len: 1,
                },
                Token {
                    typ: LeftBrace,
                    offset: 157,
                    len: 1,
                },
                Token {
                    typ: Print,
                    offset: 163,
                    len: 5,
                },
                Token {
                    typ: Identifier,
                    offset: 169,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 170,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 172,
                    len: 1,
                },
            ],
        )
    }

    #[test]
    fn test_expressions() -> Result {
        run_test(
            include_str!("../tests/expressions.crox"),
            vec![
                Token {
                    typ: Identifier,
                    offset: 0,
                    len: 3,
                },
                Token {
                    typ: Plus,
                    offset: 4,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 6,
                    len: 2,
                },
                Token {
                    typ: Semicolon,
                    offset: 8,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 10,
                    len: 8,
                },
                Token {
                    typ: Minus,
                    offset: 19,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 21,
                    len: 2,
                },
                Token {
                    typ: Semicolon,
                    offset: 23,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 25,
                    len: 8,
                },
                Token {
                    typ: Star,
                    offset: 34,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 36,
                    len: 2,
                },
                Token {
                    typ: Semicolon,
                    offset: 38,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 40,
                    len: 6,
                },
                Token {
                    typ: Slash,
                    offset: 47,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 49,
                    len: 2,
                },
                Token {
                    typ: Semicolon,
                    offset: 51,
                    len: 1,
                },
                Token {
                    typ: Minus,
                    offset: 54,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 55,
                    len: 8,
                },
                Token {
                    typ: Semicolon,
                    offset: 63,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 66,
                    len: 4,
                },
                Token {
                    typ: Less,
                    offset: 71,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 73,
                    len: 4,
                },
                Token {
                    typ: Semicolon,
                    offset: 77,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 79,
                    len: 8,
                },
                Token {
                    typ: LessEqual,
                    offset: 88,
                    len: 2,
                },
                Token {
                    typ: Identifier,
                    offset: 91,
                    len: 7,
                },
                Token {
                    typ: Semicolon,
                    offset: 98,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 100,
                    len: 7,
                },
                Token {
                    typ: Greater,
                    offset: 108,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 110,
                    len: 4,
                },
                Token {
                    typ: Semicolon,
                    offset: 114,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 116,
                    len: 11,
                },
                Token {
                    typ: GreaterEqual,
                    offset: 128,
                    len: 2,
                },
                Token {
                    typ: Identifier,
                    offset: 131,
                    len: 7,
                },
                Token {
                    typ: Semicolon,
                    offset: 138,
                    len: 1,
                },
                Token {
                    typ: Number,
                    offset: 141,
                    len: 1,
                },
                Token {
                    typ: EqualEqual,
                    offset: 143,
                    len: 2,
                },
                Token {
                    typ: Number,
                    offset: 146,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 147,
                    len: 1,
                },
                Token {
                    typ: String,
                    offset: 159,
                    len: 3,
                },
                Token {
                    typ: BangEqual,
                    offset: 164,
                    len: 2,
                },
                Token {
                    typ: String,
                    offset: 168,
                    len: 3,
                },
                Token {
                    typ: Semicolon,
                    offset: 172,
                    len: 1,
                },
                Token {
                    typ: Number,
                    offset: 183,
                    len: 3,
                },
                Token {
                    typ: EqualEqual,
                    offset: 187,
                    len: 2,
                },
                Token {
                    typ: String,
                    offset: 191,
                    len: 2,
                },
                Token {
                    typ: Semicolon,
                    offset: 194,
                    len: 1,
                },
                Token {
                    typ: Number,
                    offset: 205,
                    len: 3,
                },
                Token {
                    typ: EqualEqual,
                    offset: 209,
                    len: 2,
                },
                Token {
                    typ: String,
                    offset: 213,
                    len: 3,
                },
                Token {
                    typ: Semicolon,
                    offset: 217,
                    len: 1,
                },
                Token {
                    typ: Bang,
                    offset: 229,
                    len: 1,
                },
                Token {
                    typ: True,
                    offset: 230,
                    len: 4,
                },
                Token {
                    typ: Semicolon,
                    offset: 234,
                    len: 1,
                },
                Token {
                    typ: Bang,
                    offset: 245,
                    len: 1,
                },
                Token {
                    typ: False,
                    offset: 246,
                    len: 5,
                },
                Token {
                    typ: Semicolon,
                    offset: 251,
                    len: 1,
                },
                Token {
                    typ: True,
                    offset: 262,
                    len: 4,
                },
                Token {
                    typ: And,
                    offset: 267,
                    len: 3,
                },
                Token {
                    typ: False,
                    offset: 271,
                    len: 5,
                },
                Token {
                    typ: Semicolon,
                    offset: 276,
                    len: 1,
                },
                Token {
                    typ: True,
                    offset: 287,
                    len: 4,
                },
                Token {
                    typ: And,
                    offset: 292,
                    len: 3,
                },
                Token {
                    typ: True,
                    offset: 296,
                    len: 4,
                },
                Token {
                    typ: Semicolon,
                    offset: 300,
                    len: 1,
                },
                Token {
                    typ: False,
                    offset: 311,
                    len: 5,
                },
                Token {
                    typ: Or,
                    offset: 317,
                    len: 2,
                },
                Token {
                    typ: False,
                    offset: 320,
                    len: 5,
                },
                Token {
                    typ: Semicolon,
                    offset: 325,
                    len: 1,
                },
                Token {
                    typ: False,
                    offset: 336,
                    len: 5,
                },
                Token {
                    typ: Or,
                    offset: 342,
                    len: 2,
                },
                Token {
                    typ: True,
                    offset: 345,
                    len: 4,
                },
                Token {
                    typ: Semicolon,
                    offset: 349,
                    len: 1,
                },
                Token {
                    typ: Var,
                    offset: 360,
                    len: 3,
                },
                Token {
                    typ: Identifier,
                    offset: 364,
                    len: 7,
                },
                Token {
                    typ: Equal,
                    offset: 372,
                    len: 1,
                },
                Token {
                    typ: LeftParen,
                    offset: 374,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 375,
                    len: 3,
                },
                Token {
                    typ: Plus,
                    offset: 379,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 381,
                    len: 3,
                },
                Token {
                    typ: RightParen,
                    offset: 384,
                    len: 1,
                },
                Token {
                    typ: Slash,
                    offset: 386,
                    len: 1,
                },
                Token {
                    typ: Number,
                    offset: 388,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 389,
                    len: 1,
                },
            ],
        )
    }

    #[test]
    fn test_functions() -> Result {
        run_test(
            include_str!("../tests/functions.crox"),
            vec![
                Token {
                    typ: Identifier,
                    offset: 0,
                    len: 13,
                },
                Token {
                    typ: LeftParen,
                    offset: 13,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 14,
                    len: 5,
                },
                Token {
                    typ: Comma,
                    offset: 19,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 21,
                    len: 4,
                },
                Token {
                    typ: Comma,
                    offset: 25,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 27,
                    len: 5,
                },
                Token {
                    typ: RightParen,
                    offset: 32,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 33,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 36,
                    len: 13,
                },
                Token {
                    typ: LeftParen,
                    offset: 49,
                    len: 1,
                },
                Token {
                    typ: RightParen,
                    offset: 50,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 51,
                    len: 1,
                },
                Token {
                    typ: Fun,
                    offset: 54,
                    len: 3,
                },
                Token {
                    typ: Identifier,
                    offset: 58,
                    len: 8,
                },
                Token {
                    typ: LeftParen,
                    offset: 66,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 67,
                    len: 1,
                },
                Token {
                    typ: Comma,
                    offset: 68,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 70,
                    len: 1,
                },
                Token {
                    typ: RightParen,
                    offset: 71,
                    len: 1,
                },
                Token {
                    typ: LeftBrace,
                    offset: 73,
                    len: 1,
                },
                Token {
                    typ: Print,
                    offset: 79,
                    len: 5,
                },
                Token {
                    typ: Identifier,
                    offset: 85,
                    len: 1,
                },
                Token {
                    typ: Plus,
                    offset: 87,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 89,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 90,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 92,
                    len: 1,
                },
                Token {
                    typ: Fun,
                    offset: 95,
                    len: 3,
                },
                Token {
                    typ: Identifier,
                    offset: 99,
                    len: 9,
                },
                Token {
                    typ: LeftParen,
                    offset: 108,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 109,
                    len: 1,
                },
                Token {
                    typ: Comma,
                    offset: 110,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 112,
                    len: 1,
                },
                Token {
                    typ: RightParen,
                    offset: 113,
                    len: 1,
                },
                Token {
                    typ: LeftBrace,
                    offset: 115,
                    len: 1,
                },
                Token {
                    typ: Return,
                    offset: 121,
                    len: 6,
                },
                Token {
                    typ: Identifier,
                    offset: 128,
                    len: 1,
                },
                Token {
                    typ: Plus,
                    offset: 130,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 132,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 133,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 135,
                    len: 1,
                },
                Token {
                    typ: Fun,
                    offset: 138,
                    len: 3,
                },
                Token {
                    typ: Identifier,
                    offset: 142,
                    len: 7,
                },
                Token {
                    typ: LeftParen,
                    offset: 149,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 150,
                    len: 1,
                },
                Token {
                    typ: Comma,
                    offset: 151,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 153,
                    len: 1,
                },
                Token {
                    typ: RightParen,
                    offset: 154,
                    len: 1,
                },
                Token {
                    typ: LeftBrace,
                    offset: 156,
                    len: 1,
                },
                Token {
                    typ: Return,
                    offset: 162,
                    len: 6,
                },
                Token {
                    typ: Identifier,
                    offset: 169,
                    len: 1,
                },
                Token {
                    typ: Plus,
                    offset: 171,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 173,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 174,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 176,
                    len: 1,
                },
                Token {
                    typ: Fun,
                    offset: 179,
                    len: 3,
                },
                Token {
                    typ: Identifier,
                    offset: 183,
                    len: 8,
                },
                Token {
                    typ: LeftParen,
                    offset: 191,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 192,
                    len: 1,
                },
                Token {
                    typ: RightParen,
                    offset: 193,
                    len: 1,
                },
                Token {
                    typ: LeftBrace,
                    offset: 195,
                    len: 1,
                },
                Token {
                    typ: Return,
                    offset: 201,
                    len: 6,
                },
                Token {
                    typ: Identifier,
                    offset: 208,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 209,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 211,
                    len: 1,
                },
                Token {
                    typ: Print,
                    offset: 214,
                    len: 5,
                },
                Token {
                    typ: Identifier,
                    offset: 220,
                    len: 8,
                },
                Token {
                    typ: LeftParen,
                    offset: 228,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 229,
                    len: 7,
                },
                Token {
                    typ: RightParen,
                    offset: 236,
                    len: 1,
                },
                Token {
                    typ: LeftParen,
                    offset: 237,
                    len: 1,
                },
                Token {
                    typ: Number,
                    offset: 238,
                    len: 1,
                },
                Token {
                    typ: Comma,
                    offset: 239,
                    len: 1,
                },
                Token {
                    typ: Number,
                    offset: 241,
                    len: 1,
                },
                Token {
                    typ: RightParen,
                    offset: 242,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 243,
                    len: 1,
                },
                Token {
                    typ: Fun,
                    offset: 253,
                    len: 3,
                },
                Token {
                    typ: Identifier,
                    offset: 257,
                    len: 13,
                },
                Token {
                    typ: LeftParen,
                    offset: 270,
                    len: 1,
                },
                Token {
                    typ: RightParen,
                    offset: 271,
                    len: 1,
                },
                Token {
                    typ: LeftBrace,
                    offset: 273,
                    len: 1,
                },
                Token {
                    typ: Fun,
                    offset: 279,
                    len: 3,
                },
                Token {
                    typ: Identifier,
                    offset: 283,
                    len: 13,
                },
                Token {
                    typ: LeftParen,
                    offset: 296,
                    len: 1,
                },
                Token {
                    typ: RightParen,
                    offset: 297,
                    len: 1,
                },
                Token {
                    typ: LeftBrace,
                    offset: 299,
                    len: 1,
                },
                Token {
                    typ: Print,
                    offset: 309,
                    len: 5,
                },
                Token {
                    typ: String,
                    offset: 316,
                    len: 10,
                },
                Token {
                    typ: Semicolon,
                    offset: 327,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 333,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 340,
                    len: 13,
                },
                Token {
                    typ: LeftParen,
                    offset: 353,
                    len: 1,
                },
                Token {
                    typ: RightParen,
                    offset: 354,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 355,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 357,
                    len: 1,
                },
                Token {
                    typ: Fun,
                    offset: 360,
                    len: 3,
                },
                Token {
                    typ: Identifier,
                    offset: 364,
                    len: 14,
                },
                Token {
                    typ: LeftParen,
                    offset: 378,
                    len: 1,
                },
                Token {
                    typ: RightParen,
                    offset: 379,
                    len: 1,
                },
                Token {
                    typ: LeftBrace,
                    offset: 381,
                    len: 1,
                },
                Token {
                    typ: Var,
                    offset: 387,
                    len: 3,
                },
                Token {
                    typ: Identifier,
                    offset: 391,
                    len: 7,
                },
                Token {
                    typ: Equal,
                    offset: 399,
                    len: 1,
                },
                Token {
                    typ: String,
                    offset: 402,
                    len: 7,
                },
                Token {
                    typ: Semicolon,
                    offset: 410,
                    len: 1,
                },
                Token {
                    typ: Fun,
                    offset: 417,
                    len: 3,
                },
                Token {
                    typ: Identifier,
                    offset: 421,
                    len: 5,
                },
                Token {
                    typ: LeftParen,
                    offset: 426,
                    len: 1,
                },
                Token {
                    typ: RightParen,
                    offset: 427,
                    len: 1,
                },
                Token {
                    typ: LeftBrace,
                    offset: 429,
                    len: 1,
                },
                Token {
                    typ: Print,
                    offset: 439,
                    len: 5,
                },
                Token {
                    typ: Identifier,
                    offset: 445,
                    len: 7,
                },
                Token {
                    typ: Semicolon,
                    offset: 452,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 458,
                    len: 1,
                },
                Token {
                    typ: Return,
                    offset: 465,
                    len: 6,
                },
                Token {
                    typ: Identifier,
                    offset: 472,
                    len: 5,
                },
                Token {
                    typ: Semicolon,
                    offset: 477,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 479,
                    len: 1,
                },
                Token {
                    typ: Var,
                    offset: 482,
                    len: 3,
                },
                Token {
                    typ: Identifier,
                    offset: 486,
                    len: 2,
                },
                Token {
                    typ: Equal,
                    offset: 489,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 491,
                    len: 14,
                },
                Token {
                    typ: LeftParen,
                    offset: 505,
                    len: 1,
                },
                Token {
                    typ: RightParen,
                    offset: 506,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 507,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 509,
                    len: 2,
                },
                Token {
                    typ: LeftParen,
                    offset: 511,
                    len: 1,
                },
                Token {
                    typ: RightParen,
                    offset: 512,
                    len: 1,
                },
                Token {
                    typ: Semicolon,
                    offset: 513,
                    len: 1,
                },
            ],
        )
    }

    #[test]
    fn test_hello_world() -> Result {
        run_test(
            include_str!("../tests/hello_world.crox"),
            vec![
                Token {
                    typ: Print,
                    offset: 28,
                    len: 5,
                },
                Token {
                    typ: String,
                    offset: 35,
                    len: 13,
                },
            ],
        )
    }

    #[test]
    fn test_statements() -> Result {
        run_test(
            include_str!("../tests/statements.crox"),
            vec![
                Token {
                    typ: Print,
                    offset: 0,
                    len: 5,
                },
                Token {
                    typ: String,
                    offset: 7,
                    len: 13,
                },
                Token {
                    typ: Semicolon,
                    offset: 21,
                    len: 1,
                },
                Token {
                    typ: String,
                    offset: 25,
                    len: 15,
                },
                Token {
                    typ: Semicolon,
                    offset: 41,
                    len: 1,
                },
                Token {
                    typ: LeftBrace,
                    offset: 44,
                    len: 1,
                },
                Token {
                    typ: Print,
                    offset: 50,
                    len: 5,
                },
                Token {
                    typ: String,
                    offset: 57,
                    len: 14,
                },
                Token {
                    typ: Semicolon,
                    offset: 72,
                    len: 1,
                },
                Token {
                    typ: Print,
                    offset: 78,
                    len: 5,
                },
                Token {
                    typ: String,
                    offset: 85,
                    len: 15,
                },
                Token {
                    typ: Semicolon,
                    offset: 101,
                    len: 1,
                },
                Token {
                    typ: RightBrace,
                    offset: 103,
                    len: 1,
                },
            ],
        )
    }

    #[test]
    fn test_types() -> Result {
        run_test(
            include_str!("../tests/types.crox"),
            vec![
                Token {
                    typ: True,
                    offset: 0,
                    len: 4,
                },
                Token {
                    typ: Semicolon,
                    offset: 4,
                    len: 1,
                },
                Token {
                    typ: False,
                    offset: 19,
                    len: 5,
                },
                Token {
                    typ: Semicolon,
                    offset: 24,
                    len: 1,
                },
                Token {
                    typ: Number,
                    offset: 47,
                    len: 4,
                },
                Token {
                    typ: Semicolon,
                    offset: 51,
                    len: 1,
                },
                Token {
                    typ: Number,
                    offset: 67,
                    len: 5,
                },
                Token {
                    typ: Semicolon,
                    offset: 72,
                    len: 1,
                },
                Token {
                    typ: String,
                    offset: 96,
                    len: 13,
                },
                Token {
                    typ: Semicolon,
                    offset: 110,
                    len: 1,
                },
                Token {
                    typ: String,
                    offset: 125,
                    len: 0,
                },
                Token {
                    typ: Semicolon,
                    offset: 126,
                    len: 1,
                },
                Token {
                    typ: String,
                    offset: 149,
                    len: 3,
                },
                Token {
                    typ: Semicolon,
                    offset: 153,
                    len: 1,
                },
                Token {
                    typ: Nil,
                    offset: 190,
                    len: 3,
                },
                Token {
                    typ: Semicolon,
                    offset: 193,
                    len: 1,
                },
            ],
        )
    }

    #[test]
    fn test_variables() -> Result {
        run_test(
            include_str!("../tests/variables.crox"),
            vec![
                Token {
                    typ: Var,
                    offset: 0,
                    len: 3,
                },
                Token {
                    typ: Identifier,
                    offset: 4,
                    len: 11,
                },
                Token {
                    typ: Equal,
                    offset: 16,
                    len: 1,
                },
                Token {
                    typ: String,
                    offset: 19,
                    len: 16,
                },
                Token {
                    typ: Semicolon,
                    offset: 36,
                    len: 1,
                },
                Token {
                    typ: Var,
                    offset: 38,
                    len: 3,
                },
                Token {
                    typ: Identifier,
                    offset: 42,
                    len: 6,
                },
                Token {
                    typ: Semicolon,
                    offset: 48,
                    len: 1,
                },
                Token {
                    typ: Var,
                    offset: 51,
                    len: 3,
                },
                Token {
                    typ: Identifier,
                    offset: 55,
                    len: 9,
                },
                Token {
                    typ: Equal,
                    offset: 65,
                    len: 1,
                },
                Token {
                    typ: String,
                    offset: 68,
                    len: 6,
                },
                Token {
                    typ: Semicolon,
                    offset: 75,
                    len: 1,
                },
                Token {
                    typ: Print,
                    offset: 77,
                    len: 5,
                },
                Token {
                    typ: Identifier,
                    offset: 83,
                    len: 9,
                },
                Token {
                    typ: Semicolon,
                    offset: 92,
                    len: 1,
                },
                Token {
                    typ: Identifier,
                    offset: 106,
                    len: 9,
                },
                Token {
                    typ: Equal,
                    offset: 116,
                    len: 1,
                },
                Token {
                    typ: String,
                    offset: 119,
                    len: 8,
                },
                Token {
                    typ: Semicolon,
                    offset: 128,
                    len: 1,
                },
                Token {
                    typ: Print,
                    offset: 130,
                    len: 5,
                },
                Token {
                    typ: Identifier,
                    offset: 136,
                    len: 9,
                },
                Token {
                    typ: Semicolon,
                    offset: 145,
                    len: 1,
                },
            ],
        )
    }
}
