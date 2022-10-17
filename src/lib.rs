mod error;
mod parser;
mod token;

pub use error::{Result, RunError};
pub use token::{Token, TokenType};

pub fn run(content: &str) -> Result<()> {
    let source = parse(content);

    for token in source {
        let token = token?;
        println!("{:?}", token);
    }

    Ok(())
}

pub fn parse(content: &str) -> parser::Source<'_> {
    parser::Source::new(content)
}
