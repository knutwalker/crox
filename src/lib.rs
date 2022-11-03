mod ast;
mod error;
mod eval;
mod parser;
mod scanner;
mod token;
mod util;

use std::cell::Cell;

pub use ast::{
    Associate, Associativity, Ast, AstBuilder, BinaryOp, BoxedExpr, Expr, Idx, Literal, Node,
    OpGroup, Precedence, Resolve, UnaryOp,
};
pub use error::{CroxError, CroxErrorKind, CroxErrorScope, CroxErrors, Result};
pub use eval::{eval, Type, TypeSet, Value, ValueExpr};
pub use parser::{parse, parser, Parser};
pub use scanner::{Scanner, Source};
pub use token::{Range, Span, Spanned, Token, TokenSet, TokenType};
pub use util::{EnumSet, ValueEnum};

pub fn run(content: &str) -> Result<(Vec<ValueExpr>, Ast)> {
    let errs = Cell::new(Vec::new());

    let report = |e: CroxError| {
        let mut es = errs.take();
        es.push(e);
        errs.set(es);
    };

    let source = scan(content);

    let tokens = source.into_iter().filter_map(|t| match t {
        Ok(t) => Some(t),
        Err(e) => {
            report(e);
            None
        }
    });

    let mut parser = parser(source, tokens);
    let mut values = Vec::new();

    while let Some(expr) = parser.next() {
        let expr = match expr {
            Ok(e) => e,
            Err(e) => {
                report(e);
                continue;
            }
        };
        let val = eval(&parser, expr);
        let val = match val {
            Ok(val) => val,
            Err(e) => {
                report(e);
                continue;
            }
        };

        values.push(val);
    }

    let ast = parser.into_ast();
    let errs = errs.into_inner();

    if errs.is_empty() {
        Ok((values, ast))
    } else {
        Err(CroxErrors::from((source.source, errs)))
    }
}

pub fn scan(content: &str) -> Source<'_> {
    scanner::Source::new(content)
}
