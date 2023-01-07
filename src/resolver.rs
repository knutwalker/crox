use crate::{
    Context, CroxErrorKind, Environment, Expr, ExprNode, ExpressionRule, FunctionDef, Result,
    StatementRule, Stmt, StmtArg, StmtNode, Var,
};
use std::marker::PhantomData;

#[derive(Debug)]
pub struct Resolver<'a> {
    ctx: ResolveContext<'a>,
}

pub type ResolveContext<'a> = Context<'a, ScopeType, ()>;

impl<'a> Resolver<'a> {
    pub fn new() -> Self {
        Self {
            ctx: ResolveContext::new(Environment::empty(), ScopeType::TopLevel),
        }
    }
}

impl<'a> Default for Resolver<'a> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ScopeType {
    TopLevel,
    Function,
}

impl<'a> Resolver<'a> {
    pub fn eval_stmts_in_scope(ctx: &mut ResolveContext<'a>, stmts: &[StmtNode<'a>]) -> Result {
        stmts.iter().try_for_each(|stmt| Self::eval_stmt(ctx, stmt))
    }

    pub fn eval_stmt(ctx: &mut ResolveContext<'a>, stmt: &impl StmtArg<'a>) -> Result {
        match stmt.stmt() {
            Stmt::Expression { expr } => {
                Self::eval_expr(ctx, expr)?;
            }
            Stmt::Function(func) => {
                ctx.env.define(func.name.item, ());
                Self::resolve_function(ctx, &func.fun, ScopeType::Function)?;
            }
            Stmt::If {
                condition,
                then_,
                else_,
            } => {
                Self::eval_expr(ctx, condition)?;
                Self::eval_stmt(ctx, then_)?;
                if let Some(else_) = else_ {
                    Self::eval_stmt(ctx, else_)?;
                }
            }
            Stmt::Print { expr } => {
                Self::eval_expr(ctx, expr)?;
            }
            Stmt::Return { expr } => {
                if ctx.data == ScopeType::TopLevel {
                    return Err(CroxErrorKind::ReturnFromTopLevel.at(stmt.span()));
                }
                if let Some(expr) = expr.as_ref() {
                    Self::eval_expr(ctx, expr)?;
                }
            }
            Stmt::Var { name, initializer } => {
                // The book splits this into two steps to make shadowing an error.
                // In Crox, we allow shadowing.
                if let Some(init) = initializer.as_ref() {
                    Self::eval_expr(ctx, init)?;
                }
                ctx.env.define_local(name.item, ());
            }
            Stmt::While { condition, body } => {
                Self::eval_expr(ctx, condition)?;
                Self::eval_stmt(ctx, body)?;
            }
            Stmt::Block { stmts } => {
                ctx.run_with_new_scope(|ctx| Self::eval_stmts_in_scope(ctx, stmts))?;
            }
        };
        Ok(())
    }

    pub fn eval_expr(ctx: &mut ResolveContext<'a>, expr: &ExprNode<'a>) -> Result {
        match &*expr.item {
            Expr::Literal(_) => {}
            Expr::Var(var) => Self::resolve_local(ctx, var),
            Expr::Fun(func) => Self::resolve_function(ctx, func, ScopeType::Function)?,
            Expr::Assignment { var, value } => {
                Self::eval_expr(ctx, value)?;
                Self::resolve_local(ctx, var)
            }
            Expr::Unary { expr, .. } => {
                Self::eval_expr(ctx, expr)?;
            }
            Expr::Logical { lhs, rhs, .. } => {
                Self::eval_expr(ctx, lhs)?;
                Self::eval_expr(ctx, rhs)?;
            }
            Expr::Binary { lhs, rhs, .. } => {
                Self::eval_expr(ctx, lhs)?;
                Self::eval_expr(ctx, rhs)?;
            }
            Expr::Call { callee, arguments } => {
                Self::eval_expr(ctx, callee)?;
                arguments
                    .iter()
                    .try_for_each(|arg| Self::eval_expr(ctx, arg))?;
            }
            Expr::Group { expr } => {
                Self::eval_expr(ctx, expr)?;
            }
        };
        Ok(())
    }

    fn resolve_local(ctx: &mut ResolveContext<'a>, var: &Var<'a>) {
        if let Ok(scope) = ctx.env.scope_of(var.name) {
            var.resolved_scope.set(scope);
        }
    }

    fn resolve_function(
        ctx: &mut ResolveContext<'a>,
        func: &FunctionDef<'a>,
        scope_type: ScopeType,
    ) -> Result {
        ctx.run_with_new_scope(|ctx| {
            let mut guard = ctx.swap_data(scope_type);

            for param in func.params.iter() {
                guard
                    .env
                    .define_local_unique(param.item, ())
                    .map_err(|e| CroxErrorKind::from(e).at(param.span))?;
            }
            Self::eval_stmts_in_scope(&mut guard, &func.body)?;
            Ok(())
        })
    }
}

impl<'a> Resolver<'a> {
    pub fn eval_own_stmts_in_scope(&mut self, stmts: &[StmtNode<'a>]) -> Result {
        Self::eval_stmts_in_scope(&mut self.ctx, stmts)
    }

    pub fn eval_own_stmt(&mut self, stmt: &StmtNode<'a>) -> Result {
        Self::eval_stmt(&mut self.ctx, stmt)
    }

    pub fn eval_own_expr(&mut self, expr: &ExprNode<'a>) -> Result {
        Self::eval_expr(&mut self.ctx, expr)
    }
}

#[derive(Debug)]
pub struct StreamResolver<'a, R, I> {
    resolver: Resolver<'a>,
    input: I,
    _rule: PhantomData<R>,
}

impl<'a, R, I> StreamResolver<'a, R, I> {
    pub fn new(tokens: I) -> Self {
        Self {
            resolver: Resolver::new(),
            input: tokens,
            _rule: PhantomData,
        }
    }
}

pub fn stmt_resolver<'a, I>(tokens: I) -> impl Iterator<Item = Result<StmtNode<'a>>>
where
    I: IntoIterator<Item = StmtNode<'a>>,
{
    StreamResolver::<StatementRule, _>::new(tokens.into_iter())
}

pub fn expr_resolver<'a, I>(tokens: I) -> impl Iterator<Item = Result<ExprNode<'a>>>
where
    I: IntoIterator<Item = ExprNode<'a>>,
{
    StreamResolver::<ExpressionRule, _>::new(tokens.into_iter())
}

impl<'a, R, I> Iterator for StreamResolver<'a, R, I>
where
    R: ResolverRule,
    I: Iterator<Item = R::Input<'a>>,
{
    type Item = Result<I::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        let input = self.input.next()?;
        let res = R::resolve(&mut self.resolver, &input).map(|_| input);
        Some(res)
    }
}

pub trait ResolverRule: Sized {
    type Input<'a>;

    fn resolve<'a>(interpreter: &mut Resolver<'a>, input: &Self::Input<'a>) -> Result;
}

impl ResolverRule for ExpressionRule {
    type Input<'a> = ExprNode<'a>;

    fn resolve<'a>(interpreter: &mut Resolver<'a>, input: &Self::Input<'a>) -> Result {
        interpreter.eval_own_expr(input)
    }
}

impl ResolverRule for StatementRule {
    type Input<'a> = StmtNode<'a>;

    fn resolve<'a>(interpreter: &mut Resolver<'a>, input: &Self::Input<'a>) -> Result {
        interpreter.eval_own_stmt(input)
    }
}
