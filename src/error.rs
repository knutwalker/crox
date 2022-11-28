use crate::{Range, TokenSet, TokenType, Type, TypeSet};
use std::{
    cell::Cell,
    error::Error as StdError,
    fmt::{Debug, Display},
};

#[cfg(feature = "fancy")]
use miette::Diagnostic;

pub type Result<T = (), E = CroxError> = core::result::Result<T, E>;

#[derive(Clone, Debug)]
#[cfg_attr(feature = "fancy", derive(Diagnostic))]
#[cfg_attr(feature = "fancy", diagnostic())]
pub struct CroxErrors {
    #[cfg_attr(feature = "fancy", source_code)]
    src: String,
    #[cfg_attr(feature = "fancy", related)]
    errors: Vec<CroxError>,
}

impl From<(&str, Vec<CroxError>)> for CroxErrors {
    fn from((source, errors): (&str, Vec<CroxError>)) -> Self {
        Self {
            src: String::from(source),
            errors,
        }
    }
}

impl CroxErrors {
    pub fn scope(&self) -> CroxErrorScope {
        self.errors
            .iter()
            .map(|e| CroxErrorScope::from(&e.kind))
            .max()
            .unwrap_or(CroxErrorScope::Custom)
    }

    pub fn errors(&self) -> &[CroxError] {
        &self.errors
    }
}

impl Display for CroxErrors {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if cfg!(feature = "fancy") {
            writeln!(f, "Errors while running in crox")?;
        } else {
            for err in &self.errors {
                let err = SourceScanError::new(&self.src, err.span.clone(), &err.kind);
                Display::fmt(&err, f)?;
            }
        }

        Ok(())
    }
}

impl StdError for CroxErrors {}

pub struct CroxErrorsBuilder {
    errors: Cell<Vec<CroxError>>,
}

impl CroxErrorsBuilder {
    pub fn new() -> Self {
        Self {
            errors: Cell::new(Vec::new()),
        }
    }

    pub fn report(&self, err: CroxError) {
        let mut es = self.errors.take();
        es.push(err);
        self.errors.set(es);
    }

    pub fn ok<T>(&self, res: Result<T>) -> Option<T> {
        match res {
            Ok(v) => Some(v),
            Err(e) => {
                self.report(e);
                None
            }
        }
    }

    pub fn finish(self, src: &str) -> Option<CroxErrors> {
        let errs = self.errors.into_inner();
        if errs.is_empty() {
            None
        } else {
            Some(CroxErrors::from((src, errs)))
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "fancy", derive(Diagnostic))]
#[cfg_attr(feature = "fancy", diagnostic())]
pub struct CroxError {
    pub kind: CroxErrorKind,
    #[cfg_attr(feature = "fancy", label("{}", kind))]
    pub span: Range,
}

impl CroxError {
    pub fn new(kind: CroxErrorKind, span: impl Into<Range>) -> Self {
        Self {
            kind,
            span: span.into(),
        }
    }
}

impl Display for CroxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if cfg!(feature = "fancy") {
            f.write_str(self.kind.prefix().trim_end_matches(": "))
        } else {
            write!(f, "[offset {:?}] Error: {}", self.span, self.kind)
        }
    }
}

impl StdError for CroxError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        cfg!(not(feature = "fancy")).then_some(&self.kind)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "fancy", derive(Diagnostic))]
pub enum CroxErrorKind {
    #[cfg_attr(feature = "fancy", diagnostic())]
    UnexpectedInput { input: char },

    #[cfg_attr(feature = "fancy", diagnostic())]
    UnexpectedEndOfInput { expected: Option<TokenSet> },

    #[cfg_attr(feature = "fancy", diagnostic())]
    UnclosedStringLiteral,

    #[cfg_attr(feature = "fancy", diagnostic())]
    UnexpectedToken {
        expected: TokenSet,
        actual: TokenType,
    },

    #[cfg_attr(feature = "fancy", diagnostic())]
    UnclosedDelimiter { unclosed: TokenType },

    #[cfg_attr(feature = "fancy", diagnostic())]
    InvalidNumberLiteral {
        reason: Option<std::num::ParseFloatError>,
    },

    #[cfg_attr(feature = "fancy", diagnostic())]
    InvalidAssignmentTarget,

    #[cfg_attr(feature = "fancy", diagnostic())]
    InvalidType { expected: TypeSet, actual: Type },

    #[cfg_attr(feature = "fancy", diagnostic())]
    UndefinedVariable { name: String },

    #[cfg_attr(feature = "fancy", diagnostic())]
    UninitializedVariable { name: String },

    #[cfg_attr(feature = "fancy", diagnostic())]
    Other(String),
}

impl CroxErrorKind {
    pub fn of(input: impl Into<CroxErrorKind>) -> Self {
        input.into()
    }

    pub fn at(self, span: impl Into<Range>) -> CroxError {
        CroxError::new(self, span)
    }
}

impl From<char> for CroxErrorKind {
    fn from(input: char) -> Self {
        Some(input).into()
    }
}

impl From<()> for CroxErrorKind {
    fn from(_: ()) -> Self {
        None.into()
    }
}

impl From<Option<char>> for CroxErrorKind {
    fn from(input: Option<char>) -> Self {
        match input {
            Some(input) => CroxErrorKind::UnexpectedInput { input },
            None => CroxErrorKind::UnexpectedEndOfInput { expected: None },
        }
    }
}

impl From<TokenSet> for CroxErrorKind {
    fn from(input: TokenSet) -> Self {
        CroxErrorKind::UnexpectedEndOfInput {
            expected: Some(input),
        }
    }
}

impl From<(TokenType, TokenSet)> for CroxErrorKind {
    fn from((actual, expected): (TokenType, TokenSet)) -> Self {
        CroxErrorKind::UnexpectedToken { expected, actual }
    }
}

impl From<(TokenType, TokenType)> for CroxErrorKind {
    fn from((actual, expected): (TokenType, TokenType)) -> Self {
        (actual, TokenSet::from(expected)).into()
    }
}

impl CroxErrorKind {
    fn prefix(&self) -> &'static str {
        match self {
            Self::UnexpectedInput { .. } => "Unexpected character: ",
            Self::UnexpectedEndOfInput { expected: Some(_) } => "Unexpected end of input: ",
            Self::UnexpectedEndOfInput { expected: None } => "Unexpected end of input",
            Self::UnclosedStringLiteral => "Unterminated string",
            Self::UnexpectedToken { .. } => "Unexpected token: ",
            Self::UnclosedDelimiter { .. } => "Unclosed delimiter: ",
            Self::InvalidNumberLiteral { reason: None } => "Invalid number literal",
            Self::InvalidNumberLiteral { reason: Some(_) } => "Invalid number literal: ",
            Self::InvalidAssignmentTarget => "Invalid assignment target: ",
            Self::InvalidType { .. } => "Invalid type: ",
            Self::UndefinedVariable { .. } => "Undefined variable: ",
            Self::UninitializedVariable { .. } => "Uninitialized variable: ",
            Self::Other(_) => "Error: ",
        }
    }
}

impl Display for CroxErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !cfg!(feature = "fancy") {
            f.write_str(self.prefix())?;
        }

        match self {
            Self::UnexpectedInput { input } => {
                write!(f, "{}", input)?;
            }
            Self::UnexpectedEndOfInput { expected: Some(e) } if e.len() > 1 => {
                write!(f, "expected one of: {:?}", e)?;
            }
            Self::UnexpectedEndOfInput { expected: Some(e) } => {
                write!(f, "expected {:?}", e)?;
            }
            Self::UnexpectedEndOfInput { expected: None } => {}
            Self::UnclosedStringLiteral => {}
            Self::UnexpectedToken { expected, actual } if expected.len() > 1 => {
                write!(f, "expected one of {:?}, got `{:?}`", expected, actual)?;
            }
            Self::UnexpectedToken { expected, actual } => {
                write!(f, "expected {:?}, got `{:?}`", expected, actual)?;
            }
            Self::UnclosedDelimiter { unclosed } => {
                write!(f, "{:?}", unclosed)?;
            }
            Self::InvalidNumberLiteral { reason: None } => {}
            Self::InvalidNumberLiteral { reason: Some(r) } => {
                write!(f, "{}", r)?;
            }
            Self::InvalidAssignmentTarget => {
                write!(f, "expected an identifier")?;
            }
            Self::InvalidType { expected, actual } if expected.len() > 1 => {
                write!(f, "expected one of {:?}, got {:?}", expected, actual)?;
            }
            Self::InvalidType { expected, actual } => {
                write!(f, "expected {:?}, got {:?}", expected, actual)?;
            }
            Self::UndefinedVariable { name } => {
                f.write_str(name)?;
            }
            Self::UninitializedVariable { name } => {
                f.write_str(name)?;
            }
            Self::Other(msg) => {
                write!(f, "{}", msg)?;
            }
        }

        Ok(())
    }
}

impl StdError for CroxErrorKind {}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CroxErrorScope {
    Custom,
    Scanner,
    Parser,
    Interpreter,
}

impl From<&CroxErrorKind> for CroxErrorScope {
    fn from(kind: &CroxErrorKind) -> Self {
        use CroxErrorKind::*;
        match kind {
            UnexpectedInput { .. }
            | UnexpectedEndOfInput { expected: None }
            | UnclosedStringLiteral => Self::Scanner,
            UnexpectedEndOfInput { expected: Some(_) }
            | UnexpectedToken { .. }
            | UnclosedDelimiter { .. }
            | InvalidNumberLiteral { .. }
            | InvalidAssignmentTarget => Self::Parser,
            InvalidType { .. } | UndefinedVariable { .. } | UninitializedVariable { .. } => {
                Self::Interpreter
            }
            Other(_) => Self::Custom,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SourceScanError<'a> {
    line: &'a str,
    offset: usize,
    line_number: usize,
    kind: &'a CroxErrorKind,
}

impl<'a> SourceScanError<'a> {
    fn new(source: &'a str, span: Range, kind: &'a CroxErrorKind) -> Self {
        let offset = span.start;
        let offset = offset.min(source.len() - 1);

        let until_source = &source[..=offset];
        let line_offset = until_source
            .bytes()
            .rposition(|b| b == b'\n')
            .map(|p| p + 1)
            .unwrap_or(0);
        let line_number = until_source.lines().count();
        let offset = offset - line_offset;

        let next_line = source[line_offset..]
            .bytes()
            .position(|b| b == b'\n')
            .map(|p| p + line_offset)
            .unwrap_or(source.len());
        let line = &source[line_offset..next_line];

        Self {
            kind,
            line,
            offset,
            line_number,
        }
    }
}

impl Display for SourceScanError<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "[line {}, offset {}] Error: {}",
            self.line_number, self.offset, self.kind
        )?;

        if f.alternate() {
            writeln!(f, "{}", self.line)?;
            writeln!(f, "{0:~<start$}{0:^<1}", "", start = self.offset)?;
        }

        Ok(())
    }
}
