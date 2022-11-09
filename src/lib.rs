mod ast;
mod error;
mod eval;
mod expr;
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
pub use eval::{eval, eval_ast, eval_expr, Value, ValueExpr};
pub use expr::{
    Associate, Associativity, BinaryOp, BoxedExpr, Expr, ExprNode, Idx, Literal, OpGroup,
    Precedence, Resolve, UnaryOp,
};
pub use parser::{parse, parser, Parser};
pub use scanner::{Scanner, Source};
pub use token::{Range, Span, Spanned, Token, TokenSet, TokenType};
pub use typer::{type_ast, type_ast_with, type_check, type_expr, Type, TypeSet};
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

    #[allow(clippy::needless_collect)]
    let exprs = parser.by_ref().filter_map(|t| t!(t)).collect::<Vec<_>>();

    let ast = parser.into_ast();
    let ast = type_ast_with(ast, report);

    let errs = errs.into_inner();
    if errs.is_empty() {
        let ast = eval_ast(ast);
        let ast = Ast::new(exprs, ast);
        Ok(ast)
    } else {
        Err(CroxErrors::from((source.source, errs)))
    }
}

pub fn scan(content: &str) -> Source<'_> {
    scanner::Source::new(content)
}
