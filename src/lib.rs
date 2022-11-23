mod ast;
mod error;
mod eval;
mod expr;
mod node;
mod parser;
mod scanner;
mod token;
mod typer;
mod util;

use std::cell::Cell;

pub use ast::Ast;
pub use error::{CroxError, CroxErrorKind, CroxErrorScope, CroxErrors, Result};
pub use eval::{eval, eval_node, evaluator, Value, ValueExpr};
pub use expr::{
    Associate, Associativity, BinaryOp, Expr, ExprNode, Literal, OpGroup, Precedence, UnaryOp,
};
pub use node::Node;
pub use parser::{parse, parser, Parser};
pub use scanner::{Scanner, Source};
pub use token::{Range, Span, Spanned, Token, TokenSet, TokenType};
pub use typer::{Type, TypeSet};
pub use util::{EnumSet, ValueEnum};

pub fn run(content: &str) -> Result<Ast, CroxErrors> {
    let errs = Cell::new(Vec::new());

    let report = |e: CroxError| {
        let mut es = errs.take();
        es.push(e);
        errs.set(es);
    };

    macro_rules! ok {
        ($e:expr) => {
            match $e {
                Ok(v) => Some(v),
                Err(e) => {
                    report(e);
                    None
                }
            }
        };
    }

    let source = scan(content);
    let tokens = source.into_iter().filter_map(|t| ok!(t));
    let expressions = parser(source, tokens).filter_map(|e| ok!(e));
    let values = evaluator(expressions).filter_map(|e| ok!(e));
    let ast = values.collect();

    let errs = errs.into_inner();
    if errs.is_empty() {
        Ok(ast)
    } else {
        Err(CroxErrors::from((source.source, errs)))
    }
}

pub fn scan(content: &str) -> Source<'_> {
    scanner::Source::new(content)
}
