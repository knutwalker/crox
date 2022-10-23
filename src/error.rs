use super::token::Range;
use std::{
    error::Error as StdError,
    fmt::{Debug, Display},
};

#[cfg(feature = "fancy")]
use miette::Diagnostic;

pub type Result<T = (), E = CroxErrors> = core::result::Result<T, E>;

#[derive(Clone, Debug)]
#[cfg_attr(feature = "fancy", derive(Diagnostic))]
#[cfg_attr(feature = "fancy", diagnostic())]
pub struct CroxErrors {
    #[cfg_attr(feature = "fancy", source_code)]
    src: String,
    #[cfg_attr(feature = "fancy", related)]
    scan: Vec<ScanError>,
}

impl From<(&str, Vec<ScanError>)> for CroxErrors {
    fn from((source, scan): (&str, Vec<ScanError>)) -> Self {
        Self {
            src: String::from(source),
            scan,
        }
    }
}

impl Display for CroxErrors {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if cfg!(feature = "fancy") {
            writeln!(f, "Errors while running in crox")?;
        } else {
            for err in &self.scan {
                let err = SourceScanError::new(&self.src, err.span.clone(), &err.kind);
                Display::fmt(&err, f)?;
            }
        }

        Ok(())
    }
}

impl StdError for CroxErrors {}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "fancy", derive(Diagnostic))]
#[cfg_attr(feature = "fancy", diagnostic())]
pub struct ScanError {
    pub kind: ScanErrorKind,
    #[cfg_attr(feature = "fancy", label("{}", kind))]
    pub span: Range,
}

impl Display for ScanError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if cfg!(not(feature = "fancy")) {
            write!(f, "[offset {:?}] Error: {}", self.span, self.kind)?;
        }
        Ok(())
    }
}

impl StdError for ScanError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        Some(&self.kind)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "fancy", derive(Diagnostic))]
pub enum ScanErrorKind {
    #[cfg_attr(feature = "fancy", diagnostic())]
    UnexpectedInput(Option<char>),
    #[cfg_attr(feature = "fancy", diagnostic())]
    UnclosedStringLiteral,
    #[cfg_attr(feature = "fancy", diagnostic())]
    Other(String),
}

impl Display for ScanErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ScanErrorKind::UnexpectedInput(Some(input)) => {
                write!(f, "Unexpected character: {}", input)
            }
            ScanErrorKind::UnexpectedInput(None) => write!(f, "Unexpected end of input"),
            ScanErrorKind::UnclosedStringLiteral => write!(f, "Unterminated string"),
            ScanErrorKind::Other(msg) => write!(f, "{}", msg),
        }
    }
}

impl StdError for ScanErrorKind {}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SourceScanError<'a> {
    line: &'a str,
    offset: usize,
    line_number: usize,
    kind: &'a ScanErrorKind,
}

impl<'a> SourceScanError<'a> {
    fn new(source: &'a str, span: Range, kind: &'a ScanErrorKind) -> Self {
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
