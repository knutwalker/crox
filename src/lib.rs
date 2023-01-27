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
use bumpalo::Bump;
pub use call::{Callable, Function};
pub use context::{Context, InterpreterContext};
pub use env::{Environment, Scope, Scoped};
pub use error::{CroxError, CroxErrorKind, CroxErrorScope, CroxErrors, Result, TooMany};
pub use expr::{
    BinaryOp, BoxedExpr, Expr, ExprNode, FunctionDef, Literal, LogicalOp, UnaryOp, Var,
};
pub use interp::{expr_interpreter, stmt_interpreter, Interpreter, InterpreterError};
pub use node::{Ident, Node, Spannable};
pub use oop::{Class, Instance, InstanceLike, IntoValue, MutInstanceLike};
pub use parser::{expr_parser, stmt_parser, Parser};
pub use resolver::{expr_resolver, stmt_resolver, Resolver};
pub use rule::{ExpressionRule, StatementRule};
pub use scanner::{Scanner, Source};
pub use stmt::{ClassDecl, FunctionDecl, FunctionKind, Members, Stmt, StmtNode};
pub use timing::Timings;
pub use token::{Range, Span, Spanned, Token, TokenSet, TokenType};
pub use typer::{Type, TypeSet};
pub use util::{EnumSet, ValueEnum};
pub use value::{Ast, Value, Valued};

use crate::error::ErrorsCollector;
use crate::timing::TimingsBuilder;

pub fn run<'a>(
    mut out: impl Write,
    arena: &'a Bump,
    content: &'a str,
) -> Result<Ast<'a>, CroxErrors> {
    let env = Environment::default();
    let ctx = InterpreterContext::new(env, arena, &mut out);
    run_with_env(ctx, content)
}

pub fn run_with_env<'a: 'o, 'o>(
    ctx: InterpreterContext<'a, 'o>,
    content: &'a str,
) -> Result<Ast<'a>, CroxErrors> {
    let mut timings = TimingsBuilder::new();
    let source = scan(content);
    let tokens = timings.lex(|| source.collect_all(content))?;
    let statements =
        timings.parse(|| stmt_parser(source, tokens, ctx.arena).collect_all(content))?;
    let resolved = timings.resolve(|| stmt_resolver(statements, ctx.arena).collect_all(content))?;
    let values = timings.interpret(|| stmt_interpreter(ctx, resolved).collect_all(content))?;
    Ok(Ast::new(values, timings.build()))
}

pub fn eval_with_env<'a: 'o, 'o>(
    ctx: InterpreterContext<'a, 'o>,
    content: &'a str,
) -> Result<Ast<'a>, CroxErrors> {
    let mut timings = TimingsBuilder::new();
    let source = scan(content);
    let tokens = timings.lex(|| source.collect_all(content))?;
    let statements =
        timings.parse(|| expr_parser(source, tokens, ctx.arena).collect_all(content))?;
    let resolved = timings.resolve(|| expr_resolver(statements, ctx.arena).collect_all(content))?;
    let values = timings.interpret(|| expr_interpreter(ctx, resolved).collect_all(content))?;
    Ok(Ast::new(values, timings.build()))
}

pub fn parse<'a>(content: &'a str, arena: &'a Bump) -> Result<Vec<StmtNode<'a>>, CroxErrors> {
    let source = scan(content);
    let tokens = source.collect_all(content)?;
    let statements = stmt_parser(source, tokens, arena).collect_all(content)?;
    let resolved = stmt_resolver(statements, arena).collect_all(content)?;
    Ok(resolved)
}

pub fn scan(content: &str) -> Source<'_> {
    scanner::Source::new(content)
}

pub fn run_as_script<'a>(
    fancy: bool,
    out: impl Write,
    err: impl Write,
    arena: &'a Bump,
    content: &'a str,
) -> Result<Ast<'a>, i32> {
    run(out, arena, content).map_err(move |e| {
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
    let arena = Bump::new();
    let ctx = InterpreterContext::new(env, &arena, &mut out);
    match eval_with_env(ctx, content) {
        Ok(ast) => print_ast(out, None, ast),
        Err(e) => report_error(fancy, err, e),
    };
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
        let arena = Bump::new();
        let mut out = Vec::new();
        let res = run(
            &mut out,
            &arena,
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
        let arena = Bump::new();
        let mut out = Vec::new();
        let res = run(
            &mut out,
            &arena,
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
        let arena = Bump::new();
        let mut out = Vec::new();
        let res = run(
            &mut out,
            &arena,
            r#"
fun foo(a) {
    print a; // expect foo
    var a = "bar";
    print a; // expect: bar
}

foo("foo");
       "#,
        );

        assert!(res.is_ok());
        assert_eq!(String::from_utf8(out).unwrap().trim(), "foo\nbar");
    }
}
