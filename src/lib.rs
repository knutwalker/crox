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

pub use builtin::{Builtins, Clock};
pub use call::{Callable, Function};
pub use context::{Context, InterpreterContext};
pub use env::Environment;
pub use error::{CroxError, CroxErrorKind, CroxErrorScope, CroxErrors, Result};
pub use expr::{BinaryOp, Expr, ExprNode, FunctionDef, Literal, LogicalOp, UnaryOp, Var};
pub use interp::{expr_interpreter, stmt_interpreter, Interpreter, InterpreterError};
pub use node::{Ident, Node, Spannable};
pub use parser::{expr_parser, stmt_parser, Parser};
pub use resolver::{expr_resolver, stmt_resolver, Resolver};
pub use rule::{ExpressionRule, StatementRule};
pub use scanner::{Scanner, Source};
pub use stmt::{FunctionDecl, Stmt, StmtArg, StmtNode};
pub use token::{Range, Span, Spanned, Token, TokenSet, TokenType};
pub use typer::{Type, TypeSet};
pub use util::{EnumSet, ValueEnum};
pub use value::{Ast, Value, Valued};

use crate::error::ErrorsCollector;

pub fn run(mut out: impl Write, content: &str) -> Result<Ast<'_>, CroxErrors> {
    let env = Environment::default();
    let source = scan(content);
    let tokens = source.collect_all(source)?;
    let statements = stmt_parser(source, tokens).collect_all(source)?;
    let resolved = stmt_resolver(statements).collect_all(source)?;
    let values = stmt_interpreter(&mut out, env, resolved).collect_all(source)?;
    Ok(Ast::new(values))
}

pub fn eval(mut out: impl Write, content: &str) -> Result<Ast<'_>, CroxErrors> {
    let env = Environment::default();
    let source = scan(content);
    let tokens = source.collect_all(source)?;
    let statements = expr_parser(source, tokens).collect_all(source)?;
    let resolved = expr_resolver(statements).collect_all(source)?;
    let values = expr_interpreter(&mut out, env, resolved).collect_all(source)?;
    Ok(Ast::new(values))
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
    match eval(&mut out, content) {
        Ok(ast) => print_ast(out, false, ast),
        Err(e) => report_error(fancy, err, e),
    }
}

pub fn print_ast(mut out: impl Write, verbose: bool, ast: Ast<'_>) {
    for node in ast.iter() {
        let value = &node.item;
        if verbose {
            writeln!(out, "{:#?}", node.item).unwrap();
            writeln!(out, "{value:#?}").unwrap();
        }
        if value != &Value::Nil {
            writeln!(out, "{value}").unwrap();
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
