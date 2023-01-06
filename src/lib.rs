#![warn(clippy::all, rust_2018_idioms)]
#![warn(clippy::uninlined_format_args)]

mod call;
mod context;
mod env;
mod error;
mod expr;
mod interp;
mod node;
mod parser;
mod resolver;
mod rule;
mod scanner;
mod stmt;
mod token;
mod typer;
mod util;
mod value;

use std::io::Write;

pub use call::{Callable, Clock, Function};
pub use context::Context;
pub use env::Environment;
pub use error::{CroxError, CroxErrorKind, CroxErrorScope, CroxErrors, Result};
pub use expr::{BinaryOp, Expr, ExprNode, FunctionDef, Literal, LogicalOp, UnaryOp, Var};
pub use interp::{expr_interpreter, stmt_interpreter, Interpreter};
pub use node::{Ident, Node, Spannable};
pub use parser::{expr_parser, stmt_parser, Parser};
pub use resolver::{expr_resolver, stmt_resolver, Resolver};
pub use rule::{ExpressionRule, StatementRule};
pub use scanner::{Scanner, Source};
pub use stmt::{FunctionDecl, Stmt, StmtNode};
pub use token::{Range, Span, Spanned, Token, TokenSet, TokenType};
pub use typer::{Type, TypeSet};
pub use util::{EnumSet, ValueEnum};
pub use value::{Ast, Value, Valued};

use crate::error::CroxErrorsBuilder;

pub fn run(mut out: impl Write, content: &str) -> Result<Ast<'_, StmtNode<'_>>, CroxErrors> {
    let errs = CroxErrorsBuilder::new();

    let source = scan(content);
    let tokens = source.into_iter().filter_map(|t| errs.ok(t));
    let statements = stmt_parser(source, tokens).filter_map(|e| errs.ok(e));
    let resolved = stmt_resolver(statements).filter_map(|e| errs.ok(e));
    let values = stmt_interpreter(&mut out, resolved).filter_map(|e| errs.ok(e));
    let ast = values.collect();

    match errs.finish(source.source) {
        Some(errs) => Err(errs),
        None => Ok(ast),
    }
}

pub fn eval(mut out: impl Write, content: &str) -> Result<Ast<'_, ExprNode<'_>>, CroxErrors> {
    let errs = CroxErrorsBuilder::new();

    let source = scan(content);
    let tokens = source.into_iter().filter_map(|t| errs.ok(t));
    let statements = expr_parser(source, tokens).filter_map(|e| errs.ok(e));
    let resolved = expr_resolver(statements).filter_map(|e| errs.ok(e));
    let values = expr_interpreter(&mut out, resolved).filter_map(|e| errs.ok(e));
    let ast = values.collect();

    match errs.finish(source.source) {
        Some(errs) => Err(errs),
        None => Ok(ast),
    }
}

pub fn scan(content: &str) -> Source<'_> {
    scanner::Source::new(content)
}

pub fn run_as_script(
    fancy: bool,
    out: impl Write,
    err: impl Write,
    content: &str,
) -> Result<Ast<'_, StmtNode<'_>>, i32> {
    run(out, content).map_err(move |e| {
        let scope = e.scope();
        report_error(fancy, err, e);
        match scope {
            CroxErrorScope::Custom | CroxErrorScope::Scanner | CroxErrorScope::Parser => 65,
            CroxErrorScope::Interpreter => 70,
        }
    })
}

pub fn print_ast<T: std::fmt::Debug>(verbose: bool, ast: Ast<'_, Node<T>>) {
    for node in ast.iter() {
        let value = &node.value;
        if verbose {
            println!("{:#?}", node.item);
            println!("{value:#?}");
        }
        if value != &Value::Nil {
            println!("{value}");
        }
    }
}

#[cfg(feature = "fancy")]
pub fn report_error(fancy: bool, mut w: impl Write, mut err: CroxErrors) {
    if fancy {
        let err = miette::Report::new(err);
        writeln!(w, "{err:?}").unwrap();
    } else {
        err.set_fancy(false);
        writeln!(w, "{err:#}").unwrap();
    }
}

#[cfg(not(feature = "fancy"))]
pub fn report_error(_fancy: bool, mut w: impl Write, mut err: CroxErrors) {
    err.set_fancy(false);
    writeln!(w, "{err:#}").unwrap();
}
