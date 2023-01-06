use crate::{Environment, Expr, ExprNode, ExpressionRule, StatementRule, Stmt, StmtNode, Var};
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct Resolver<'a> {
    pub(crate) env: Environment<'a, ()>,
}

impl<'a> Resolver<'a> {
    pub fn new() -> Self {
        Self {
            env: Environment::empty(),
        }
    }
}

impl<'a> Default for Resolver<'a> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> Resolver<'a> {
    pub fn eval_stmts_in_scope(env: &Environment<'a, ()>, stmts: &[StmtNode<'a>]) {
        stmts.iter().for_each(|stmt| {
            Self::eval_stmt(env, &stmt.item);
        });
    }

    pub fn eval_stmt(env: &Environment<'a, ()>, stmt: &Stmt<'a>) {
        match &stmt {
            Stmt::Expression { expr } => {
                Self::eval_expr(env, expr);
            }
            Stmt::Function(func) => {
                env.define(func.name.item, ());
                env.run_with_new_scope(|env| {
                    for param in func.fun.params.iter() {
                        env.define(param.item, ());
                    }
                    Self::eval_stmts_in_scope(env, &func.fun.body)
                });
            }
            Stmt::If {
                condition,
                then_,
                else_,
            } => {
                Self::eval_expr(env, condition);
                Self::eval_stmt(env, &then_.item);
                if let Some(else_) = else_ {
                    Self::eval_stmt(env, &else_.item);
                }
            }
            Stmt::Print { expr } => {
                Self::eval_expr(env, expr);
            }
            Stmt::Return { expr } => {
                if let Some(expr) = expr.as_ref() {
                    Self::eval_expr(env, expr);
                }
            }
            Stmt::Var { name, initializer } => {
                // The book splits this into two steps to make shadowing an error.
                // In Crox, we allow shadowing.
                if let Some(init) = initializer.as_ref() {
                    Self::eval_expr(env, init);
                }
                env.define(name.item, ());
            }
            Stmt::While { condition, body } => {
                Self::eval_expr(env, condition);
                Self::eval_stmt(env, &body.item);
            }
            Stmt::Block { stmts } => {
                env.run_with_new_scope(|env| Self::eval_stmts_in_scope(env, stmts));
            }
        };
    }

    pub fn eval_expr(env: &Environment<'a, ()>, expr: &ExprNode<'a>) {
        match &*expr.item {
            Expr::Literal(_) => {}
            Expr::Var(Var {
                name,
                resolved_scope,
            }) => {
                if let Ok(scope) = env.scope_of(name) {
                    resolved_scope.set(Some(scope));
                }
            }
            Expr::Fun(func) => {
                env.run_with_new_scope(|env| {
                    for param in func.params.iter() {
                        env.define(param.item, ());
                    }
                    Self::eval_stmts_in_scope(env, &func.body)
                });
            }
            Expr::Assignment { var, value } => {
                Self::eval_expr(env, value);
                if let Ok(scope) = env.scope_of(var.name) {
                    var.resolved_scope.set(Some(scope));
                }
            }
            Expr::Unary { expr, .. } => {
                Self::eval_expr(env, expr);
            }
            Expr::Logical { lhs, rhs, .. } => {
                Self::eval_expr(env, lhs);
                Self::eval_expr(env, rhs);
            }
            Expr::Binary { lhs, rhs, .. } => {
                Self::eval_expr(env, lhs);
                Self::eval_expr(env, rhs);
            }
            Expr::Call { callee, arguments } => {
                Self::eval_expr(env, callee);
                arguments.iter().for_each(|arg| Self::eval_expr(env, arg));
            }
            Expr::Group { expr } => {
                Self::eval_expr(env, expr);
            }
        };
    }
}

impl<'a> Resolver<'a> {
    pub fn eval_own_stmts_in_scope(&self, stmts: &[StmtNode<'a>]) {
        Self::eval_stmts_in_scope(&self.env, stmts)
    }

    pub fn eval_own_stmt(&self, stmt: &Stmt<'a>) {
        Self::eval_stmt(&self.env, stmt)
    }

    pub fn eval_own_expr(&self, expr: &ExprNode<'a>) {
        Self::eval_expr(&self.env, expr)
    }
}

#[derive(Clone, Debug)]
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

pub fn stmt_resolver<'a, I>(tokens: I) -> impl Iterator<Item = StmtNode<'a>>
where
    I: IntoIterator<Item = StmtNode<'a>>,
{
    StreamResolver::<StatementRule, _>::new(tokens.into_iter())
}

pub fn expr_resolver<'a, I>(tokens: I) -> impl Iterator<Item = ExprNode<'a>>
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
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        let input = self.input.next()?;
        R::resolve(&mut self.resolver, &input);
        Some(input)
    }
}

pub trait ResolverRule: Sized {
    type Input<'a>;

    fn resolve<'a>(interpreter: &mut Resolver<'a>, input: &Self::Input<'a>);
}

impl ResolverRule for ExpressionRule {
    type Input<'a> = ExprNode<'a>;

    fn resolve<'a>(interpreter: &mut Resolver<'a>, input: &Self::Input<'a>) {
        interpreter.eval_own_expr(input)
    }
}

impl ResolverRule for StatementRule {
    type Input<'a> = StmtNode<'a>;

    fn resolve<'a>(interpreter: &mut Resolver<'a>, input: &Self::Input<'a>) {
        interpreter.eval_own_stmt(&input.item)
    }
}
