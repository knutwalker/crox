mod ast;
mod error;
mod parser;
mod scanner;
mod token;

pub use ast::{
    Associate, Associativity, Ast, AstBuilder, BinaryOp, BoxedExpr, Expr, Idx, Literal, Node,
    OpGroup, Precedence, Resolve, UnaryOp,
};
pub use error::{CroxError, CroxErrorKind, CroxErrors, Result};
pub use parser::{parse, parser, Parser};
pub use scanner::{Scanner, Source};
pub use token::{Range, Span, Token, TokenSet, TokenType};

pub fn run(content: &str) -> Result<()> {
    let source = scan(content);
    let tokens = source.scan_all()?;

    for token in tokens {
        println!("{:?}", token);
    }

    Ok(())
}

pub fn scan(content: &str) -> Source<'_> {
    scanner::Source::new(content)
}
