mod ast;
mod error;
mod parser;
mod scanner;
mod token;

pub use ast::{
    Associate, Associativity, BinaryOp, Expr, Literal, Node, OpGroup, Precedence, UnaryOp,
};
pub use error::{CroxErrors, Result, ScanError, ScanErrorKind};
pub use parser::parser;
pub use token::{Range, Span, Token, TokenType};

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
