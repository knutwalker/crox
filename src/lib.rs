mod error;
mod scanner;
mod token;

pub use error::{CroxErrors, Result, ScanError, ScanErrorKind};
pub use token::{Token, TokenType};

pub fn run(content: &str) -> Result<()> {
    let source = scan(content);
    let tokens = source.scan_all()?;

    for token in tokens {
        println!("{:?}", token);
    }

    Ok(())
}

pub fn scan(content: &str) -> scanner::Source<'_> {
    scanner::Source::new(content)
}
