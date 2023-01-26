#![warn(clippy::all, rust_2018_idioms)]
#![warn(clippy::uninlined_format_args)]

mod builtin;
mod call;
mod context;
mod env;
mod error;
mod expr;
mod interp;
mod node;
mod oop;
mod parser;
mod resolver;
mod rule;
mod scanner;
mod stmt;
mod timing;
mod token;
mod typer;
mod util;
mod value;

use std::io::Write;

pub use builtin::{Builtins, Clock};
pub use call::{Callable, Function};
pub use context::{Context, InterpreterContext};
pub use env::{Environment, Scope, Scoped};
pub use error::{CroxError, CroxErrorKind, CroxErrorScope, CroxErrors, Result, TooMany};
pub use expr::{BinaryOp, Expr, ExprNode, FunctionDef, Literal, LogicalOp, UnaryOp, Var};
pub use interp::{expr_interpreter, stmt_interpreter, Interpreter, InterpreterError};
pub use node::{Ident, Node, Spannable};
pub use oop::{Class, Instance, InstanceLike, IntoValue, MutInstanceLike};
pub use parser::{expr_parser, stmt_parser, Parser};
pub use resolver::{expr_resolver, stmt_resolver, Resolver};
pub use rule::{ExpressionRule, StatementRule};
pub use scanner::{Scanner, Source};
pub use stmt::{ClassDecl, FunctionDecl, FunctionKind, Members, Stmt, StmtArg, StmtNode};
pub use timing::Timings;
pub use token::{Range, Span, Spanned, Token, TokenSet, TokenType};
pub use typer::{Type, TypeSet};
pub use util::{EnumSet, ValueEnum};
pub use value::{Ast, Value, Valued};

use crate::error::ErrorsCollector;
use crate::timing::TimingsBuilder;

pub fn run(out: impl Write, content: &str) -> Result<Ast<'_>, CroxErrors> {
    let env = Environment::default();
    run_with_env(out, env, content)
}

pub fn run_with_env<'a>(
    mut out: impl Write,
    env: Environment<'a>,
    content: &'a str,
) -> Result<Ast<'a>, CroxErrors> {
    let mut timings = TimingsBuilder::new();
    let source = scan(content);
    let tokens = timings.lex(|| source.collect_all(content))?;
    let statements = timings.parse(|| stmt_parser(source, tokens).collect_all(content))?;
    let resolved = timings.resolve(|| stmt_resolver(statements).collect_all(content))?;
    let values =
        timings.interpret(|| stmt_interpreter(&mut out, env, resolved).collect_all(content))?;
    Ok(Ast::new(values, timings.build()))
}

pub fn eval_with_env<'a>(
    mut out: impl Write,
    env: Environment<'a>,
    content: &'a str,
) -> Result<Ast<'a>, CroxErrors> {
    let mut timings = TimingsBuilder::new();
    let source = scan(content);
    let tokens = timings.lex(|| source.collect_all(content))?;
    let statements = timings.parse(|| expr_parser(source, tokens).collect_all(content))?;
    let resolved = timings.resolve(|| expr_resolver(statements).collect_all(content))?;
    let values =
        timings.interpret(|| expr_interpreter(&mut out, env, resolved).collect_all(content))?;
    Ok(Ast::new(values, timings.build()))
}

pub fn parse(content: &str) -> Result<Vec<StmtNode<'_>>, CroxErrors> {
    let source = scan(content);
    let tokens = source.collect_all(content)?;
    let statements = stmt_parser(source, tokens).collect_all(content)?;
    let resolved = stmt_resolver(statements).collect_all(content)?;
    Ok(resolved)
}

pub fn scan(content: &str) -> Source<'_> {
    scanner::Source::new(content)
}

pub fn run_as_script(
    fancy: bool,
    out: impl Write,
    err: impl Write,
    content: &str,
) -> Result<Ast<'_>, i32> {
    run(out, content).map_err(move |e| {
        let scope = e.scope();
        report_error(fancy, err, e);
        match scope {
            CroxErrorScope::Custom | CroxErrorScope::Scanner | CroxErrorScope::Parser => 65,
            CroxErrorScope::Interpreter => 70,
        }
    })
}

pub fn run_as_evaluator(fancy: bool, mut out: impl Write, err: impl Write, content: &str) {
    let env = Environment::default();
    match eval_with_env(&mut out, env, content) {
        Ok(ast) => print_ast(out, None, ast),
        Err(e) => report_error(fancy, err, e),
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct Config {
    pub show_ast: bool,
    pub show_timings: bool,
}

pub fn print_ast(mut out: impl Write, config: impl Into<Option<Config>>, ast: Ast<'_>) {
    let config = config.into().unwrap_or_default();
    try_print_ast(&mut out, config, ast).unwrap();
}

fn try_print_ast(mut out: impl Write, config: Config, ast: Ast<'_>) -> std::io::Result<()> {
    if config.show_timings {
        writeln!(out, "Lexing: {:?}", ast.timings.lex)?;
        writeln!(out, "Parsing: {:?}", ast.timings.parse)?;
        writeln!(out, "Resolving: {:?}", ast.timings.resolve)?;
        writeln!(out, "Interpreting: {:?}", ast.timings.interpret)?;
        writeln!(out, "Total: {:?}", ast.timings.total())?;
    }

    for node in ast.iter() {
        let value = &node.item;
        if config.show_ast {
            writeln!(out, "{:#?}", node.item)?;
            writeln!(out, "{value:#?}")?;
        }
        if value != &Value::Nil {
            writeln!(out, "{value}")?;
        }
    }

    Ok(())
}

pub fn report_error(fancy: bool, mut w: impl Write, mut err: CroxErrors) {
    if fancy {
        let err = miette::Report::new(err);
        writeln!(w, "{err:?}").unwrap();
    } else {
        err.set_fancy(false);
        writeln!(w, "{err:#}").unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unreached_undefined_does_not_trigger_error() {
        let mut out = Vec::new();
        let res = run(
            &mut out,
            r#"
if (false) {
  print notDefined;
}

print "ok";
        "#,
        );

        assert!(res.is_ok());
        assert_eq!(String::from_utf8(out).unwrap().trim(), "ok");
    }

    #[test]
    fn test_loop_var_shadowing_does_not_affect_loop_var() {
        let mut out = Vec::new();
        let res = run(
            &mut out,
            r#"
for (var i = 0; i < 1; i = i + 1) {
  print i;
  var i = -1;
  print i;
}
        "#,
        );

        assert!(res.is_ok());
        assert_eq!(String::from_utf8(out).unwrap().trim(), "0\n-1");
    }

    #[test]
    fn allow_shadowing_parameters() {
        let source = r#"
fun foo(a) {
    print a; // expect foo
    var a = "bar";
    print a; // expect: bar
}

foo("foo");
       "#;

        let mut out = Vec::new();
        let res = run(&mut out, source);

        assert!(res.is_ok());
        assert_eq!(String::from_utf8(out).unwrap().trim(), "foo\nbar");
    }
}
