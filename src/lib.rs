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

pub use ast::{
    Ast, TypedAst, TypedAstBuilder, UntypedAst, UntypedAstBuilder, ValuedAst, ValuedAstBuilder,
};
pub use error::{CroxError, CroxErrorKind, CroxErrorScope, CroxErrors, Result};
pub use eval::{eval, eval_ast, eval_node, Value, ValueNode};
pub use expr::{
    Associate, Associativity, BinaryOp, BoxedExpr, Expr, Literal, OpGroup, Precedence, UnaryOp,
};
pub use node::{Idx, Node, Resolve};
pub use parser::{parse, parser, Parser};
pub use scanner::{Scanner, Source};
pub use token::{Range, Span, Spanned, Token, TokenSet, TokenType};
pub use typer::{type_ast, type_ast_with, type_check, type_node, Type, TypeSet};
pub use util::{EnumSet, ValueEnum};

pub fn run(content: &str) -> Result<Ast, CroxErrors> {
    let errs = Cell::new(Vec::new());

    let report = |e: CroxError| {
        let mut es = errs.take();
        es.push(e);
        errs.set(es);
    };

    macro_rules! t {
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

    let tokens = source.into_iter().filter_map(|t| t!(t));

    let mut parser = parser(source, tokens);

    let nodes = parser.by_ref().filter_map(|n| t!(n)).collect::<Vec<_>>();

    let ast = parser.into_ast();
    let ast = type_ast_with(ast, report);

    let errs = errs.into_inner();
    if errs.is_empty() {
        let ast = eval_ast(ast);
        let ast = Ast::new(nodes, ast);
        Ok(ast)
    } else {
        Err(CroxErrors::from((source.source, errs)))
    }
}

pub fn scan(content: &str) -> Source<'_> {
    scanner::Source::new(content)
}
