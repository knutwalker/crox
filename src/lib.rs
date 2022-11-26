mod env;
mod error;
mod expr;
mod interp;
mod node;
mod parser;
mod rule;
mod scanner;
mod stmt;
mod token;
mod typer;
mod util;
mod value;

pub use env::Environment;
pub use error::{CroxError, CroxErrorKind, CroxErrorScope, CroxErrors, Result};
pub use expr::{BinaryOp, Expr, ExprNode, Literal, UnaryOp};
pub use interp::{expr_interpreter, stmt_interpreter};
pub use node::Node;
pub use parser::{expr_parser, stmt_parser, Parser};
pub use rule::{ExpressionRule, StatementRule};
pub use scanner::{Scanner, Source};
pub use stmt::{Stmt, StmtNode};
pub use token::{Range, Span, Spanned, Token, TokenSet, TokenType};
pub use typer::{Type, TypeSet};
pub use util::{EnumSet, ValueEnum};
pub use value::{Ast, Value, Valued};

use crate::error::CroxErrorsBuilder;

pub fn run(content: &str) -> Result<Ast<StmtNode<'_>>, CroxErrors> {
    let errs = CroxErrorsBuilder::new();

    let source = scan(content);
    let tokens = source.into_iter().filter_map(|t| errs.ok(t));
    let statements = stmt_parser(source, tokens).filter_map(|e| errs.ok(e));
    let values = stmt_interpreter(statements).filter_map(|e| errs.ok(e));
    let ast = values.collect();

    match errs.finish(source.source) {
        Some(errs) => Err(errs),
        None => Ok(ast),
    }
}

pub fn eval(content: &str) -> Result<Ast<ExprNode<'_>>, CroxErrors> {
    let errs = CroxErrorsBuilder::new();

    let source = scan(content);
    let tokens = source.into_iter().filter_map(|t| errs.ok(t));
    let statements = expr_parser(source, tokens).filter_map(|e| errs.ok(e));
    let values = expr_interpreter(statements).filter_map(|e| errs.ok(e));
    let ast = values.collect();

    match errs.finish(source.source) {
        Some(errs) => Err(errs),
        None => Ok(ast),
    }
}

pub fn scan(content: &str) -> Source<'_> {
    scanner::Source::new(content)
}
