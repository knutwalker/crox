mod error;
mod scanner;
mod token;

pub use error::{Result, RunError};
pub use token::{Token, TokenType};

pub fn run(content: &str) -> Result<()> {
    let source = scan(content);

    for token in source {
        let token = token?;
        println!("{:?}", token);
    }

    Ok(())
}

pub fn scan(content: &str) -> scanner::Source<'_> {
    scanner::Source::new(content)
}
