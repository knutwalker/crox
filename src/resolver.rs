use crate::{
    Context, CroxErrorKind, Environment, Expr, ExprNode, ExpressionRule, FunctionDef, Result,
    Scoped, StatementRule, Stmt, StmtArg, StmtNode, Var,
};
use std::{marker::PhantomData, rc::Rc};

#[derive(Debug)]
pub struct Resolver<'a> {
    ctx: ResolveContext<'a>,
}

pub type ResolveContext<'a> = Context<'a, Current, ()>;

impl<'a> Resolver<'a> {
    pub fn new() -> Self {
        Self {
            ctx: ResolveContext::new(Environment::empty(), Current::default()),
        }
    }
}

impl<'a> Default for Resolver<'a> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct Current {
    scope: ScopeKind,
    class: ClassKind,
}

impl Current {
    fn with_scope(self, scope: ScopeKind) -> Self {
        Self { scope, ..self }
    }

    fn with_class(self, class: ClassKind) -> Self {
        Self { class, ..self }
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
enum ScopeKind {
    #[default]
    TopLevel,
    Function,
    Initializer,
    Method,
    ClassMethod,
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
enum ClassKind {
    #[default]
    Global,
    Class,
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
            Stmt::Class(class) => {
                ctx.env.define(class.name.item, ());
                if let Some(superclass) = &class.superclass {
                    if superclass.item.name == class.name.item {
                        return Err(CroxErrorKind::InheritsSelf.at(superclass.span));
                    }
                    let superclass = superclass.clone().map(|s| Rc::new(Expr::Var(s)));
                    Self::eval_expr(ctx, &superclass)?;
                }
                ctx.run_with_new_scope(|ctx| -> Result {
                    let mut guard = ctx.swap_data(ctx.data.with_class(ClassKind::Class));
                    for method in class.members().class_methods() {
                        Self::resolve_function(
                            &mut guard,
                            &method.item.fun,
                            ScopeKind::ClassMethod,
                        )?;
                    }
                    guard.env.define("this", ());
                    for property in class.members().properties() {
                        Self::resolve_function(&mut guard, &property.item.fun, ScopeKind::Method)?;
                    }
                    for method in class.members().methods() {
                        let scope_kind = if method.item.name.item == "init" {
                            ScopeKind::Initializer
                        } else {
                            ScopeKind::Method
                        };
                        Self::resolve_function(&mut guard, &method.item.fun, scope_kind)?;
                    }

                    Ok(())
                })?;
            }
            Stmt::Function(func) => {
                ctx.env.define(func.name.item, ());
                Self::resolve_function(ctx, &func.fun, ScopeKind::Function)?;
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
                if ctx.data.scope == ScopeKind::TopLevel {
                    return Err(CroxErrorKind::ReturnFromTopLevel.at(stmt.span()));
                }
                if let Some(expr) = expr.as_ref() {
                    if ctx.data.scope == ScopeKind::Initializer {
                        return Err(CroxErrorKind::ReturnFromInitializer.at(stmt.span()));
                    }
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
            Expr::Var(Var { name, scope }) => Self::resolve_local(ctx, name, scope),
            Expr::Fun(func) => Self::resolve_function(ctx, func, ScopeKind::Function)?,
            Expr::Assignment { name, scope, value } => {
                Self::eval_expr(ctx, value)?;
                Self::resolve_local(ctx, name, scope);
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
            Expr::Get { object, name: _ } => {
                Self::eval_expr(ctx, object)?;
            }
            Expr::Set {
                object,
                name: _,
                value,
            } => {
                Self::eval_expr(ctx, value)?;
                Self::eval_expr(ctx, object)?;
            }
            Expr::This { scope } => {
                if ctx.data.class == ClassKind::Global {
                    return Err(CroxErrorKind::ThisOutsideClass.at(expr.span));
                }
                if ctx.data.scope == ScopeKind::ClassMethod {
                    return Err(CroxErrorKind::ThisInClassMethod.at(expr.span));
                }
                Self::resolve_local(ctx, "this", scope);
            }
            Expr::Group { expr } => {
                Self::eval_expr(ctx, expr)?;
            }
        };
        Ok(())
    }

    fn resolve_local(ctx: &mut ResolveContext<'a>, name: &'a str, scope: &Scoped) {
        if let Ok(resolved) = ctx.env.scope_of(name) {
            scope.resolve(resolved);
        }
    }

    fn resolve_function(
        ctx: &mut ResolveContext<'a>,
        func: &FunctionDef<'a>,
        scope_type: ScopeKind,
    ) -> Result {
        ctx.run_with_new_scope(|ctx| {
            let mut guard = ctx.swap_data(ctx.data.with_scope(scope_type));

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
