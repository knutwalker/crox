use crate::{
    Bump, ClassDecl, Context, CroxErrorKind, Environment, Expr, ExprNode, ExpressionRule,
    FunctionDef, Result, Scoped, Span, StatementRule, Stmt, StmtNode, Var,
};
use std::marker::PhantomData;

#[derive(Debug)]
pub struct Resolver<'env> {
    ctx: ResolveContext<'env>,
}

pub type ResolveContext<'env> = Context<'env, Current, ()>;

impl<'env> Resolver<'env> {
    pub fn new(arena: &'env Bump) -> Self {
        Self {
            ctx: ResolveContext::new(Environment::empty(), arena, Current::default()),
        }
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
    Subclass,
}

impl<'env> Resolver<'env> {
    pub fn resolve_stmts_in_scope(
        ctx: &mut ResolveContext<'env>,
        stmts: &[StmtNode<'env>],
    ) -> Result {
        stmts
            .iter()
            .try_for_each(|stmt| Self::resolve_stmt(ctx, &stmt.item, stmt.span))
    }

    pub fn resolve_stmt(ctx: &mut ResolveContext<'env>, stmt: &Stmt<'env>, span: Span) -> Result {
        match stmt {
            Stmt::Expression { expr } => {
                Self::resolve_expr(ctx, expr.item, expr.span)?;
            }
            Stmt::Class(class) => {
                ctx.env.define(class.name.item, ());
                let mut guard = ctx.swap_data(ctx.data.with_class(ClassKind::Class));
                if let Some(superclass) = &class.superclass {
                    if superclass.item.name == class.name.item {
                        return Err(CroxErrorKind::InheritsSelf.at(superclass.span));
                    }

                    Self::resolve_local(&mut guard, superclass.item.name, superclass.item.scope);

                    let new_data = guard.data.with_class(ClassKind::Subclass);
                    let mut inner_guard = guard.swap_data(new_data);

                    inner_guard.run_with_new_scope(|ctx| {
                        ctx.env.define("super", ());
                        Self::resolve_class(ctx, class)
                    })?;
                } else {
                    Self::resolve_class(&mut guard, class)?;
                }
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
                Self::resolve_expr(ctx, condition.item, condition.span)?;
                Self::resolve_stmt(ctx, then_.item, then_.span)?;
                if let Some(else_) = else_ {
                    Self::resolve_stmt(ctx, else_.item, else_.span)?;
                }
            }
            Stmt::Print { expr } => {
                Self::resolve_expr(ctx, expr.item, expr.span)?;
            }
            Stmt::Return { expr } => {
                if ctx.data.scope == ScopeKind::TopLevel {
                    return Err(CroxErrorKind::ReturnFromTopLevel.at(span));
                }
                if let Some(expr) = expr.as_ref() {
                    if ctx.data.scope == ScopeKind::Initializer {
                        return Err(CroxErrorKind::ReturnFromInitializer.at(span));
                    }
                    Self::resolve_expr(ctx, expr.item, expr.span)?;
                }
            }
            Stmt::Var { name, initializer } => {
                // The book splits this into two steps to make shadowing an error.
                // In Crox, we allow shadowing.
                if let Some(init) = initializer.as_ref() {
                    Self::resolve_expr(ctx, init.item, init.span)?;
                }
                ctx.env.define_local(name.item, ());
            }
            Stmt::While { condition, body } => {
                Self::resolve_expr(ctx, condition.item, condition.span)?;
                Self::resolve_stmt(ctx, body.item, body.span)?;
            }
            Stmt::Block { stmts } => {
                ctx.run_with_new_scope(|ctx| Self::resolve_stmts_in_scope(ctx, stmts))?;
            }
        };
        Ok(())
    }

    pub fn resolve_expr(ctx: &mut ResolveContext<'env>, expr: &Expr<'env>, span: Span) -> Result {
        match expr {
            Expr::Literal(_) => {}
            Expr::Var(Var { name, scope }) => Self::resolve_local(ctx, name, scope),
            Expr::Fun(func) => Self::resolve_function(ctx, func, ScopeKind::Function)?,
            Expr::Assignment { name, scope, value } => {
                Self::resolve_expr(ctx, value.item, value.span)?;
                Self::resolve_local(ctx, name, scope);
            }
            Expr::Unary { expr, .. } => {
                Self::resolve_expr(ctx, expr.item, expr.span)?;
            }
            Expr::Logical { lhs, rhs, .. } => {
                Self::resolve_expr(ctx, lhs.item, lhs.span)?;
                Self::resolve_expr(ctx, rhs.item, rhs.span)?;
            }
            Expr::Binary { lhs, rhs, .. } => {
                Self::resolve_expr(ctx, lhs.item, lhs.span)?;
                Self::resolve_expr(ctx, rhs.item, rhs.span)?;
            }
            Expr::Call { callee, arguments } => {
                Self::resolve_expr(ctx, callee.item, callee.span)?;
                arguments
                    .iter()
                    .try_for_each(|arg| Self::resolve_expr(ctx, &arg.item, arg.span))?;
            }
            Expr::Get { object, name: _ } => {
                Self::resolve_expr(ctx, object.item, object.span)?;
            }
            Expr::Set {
                object,
                name: _,
                value,
            } => {
                Self::resolve_expr(ctx, value.item, value.span)?;
                Self::resolve_expr(ctx, object.item, object.span)?;
            }
            Expr::Super { method: _, scope } => {
                match ctx.data.class {
                    ClassKind::Global => return Err(CroxErrorKind::SuperOutsideClass.at(span)),
                    ClassKind::Class => {
                        return Err(CroxErrorKind::SuperInClassWithoutSuperclass.at(span))
                    }
                    ClassKind::Subclass => {}
                }
                Self::resolve_local(ctx, "super", scope);
            }
            Expr::This { scope } => {
                if ctx.data.class == ClassKind::Global {
                    return Err(CroxErrorKind::ThisOutsideClass.at(span));
                }
                if ctx.data.scope == ScopeKind::ClassMethod {
                    return Err(CroxErrorKind::ThisInClassMethod.at(span));
                }
                Self::resolve_local(ctx, "this", scope);
            }
            Expr::Group { expr } => {
                Self::resolve_expr(ctx, expr.item, expr.span)?;
            }
        };
        Ok(())
    }

    fn resolve_local(ctx: &mut ResolveContext<'env>, name: &'env str, scope: &Scoped) {
        if let Ok(resolved) = ctx.env.scope_of(name) {
            scope.resolve(resolved);
        }
    }

    fn resolve_function(
        ctx: &mut ResolveContext<'env>,
        func: &FunctionDef<'env>,
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
            Self::resolve_stmts_in_scope(&mut guard, func.body)?;
            Ok(())
        })
    }

    fn resolve_class(ctx: &mut ResolveContext<'env>, class: &ClassDecl<'env>) -> Result {
        ctx.run_with_new_scope(|ctx| -> Result {
            for method in class.members().class_methods() {
                Self::resolve_function(ctx, &method.item.fun, ScopeKind::ClassMethod)?;
            }
            ctx.env.define("this", ());
            for property in class.members().properties() {
                Self::resolve_function(ctx, &property.item.fun, ScopeKind::Method)?;
            }
            for method in class.members().methods() {
                let scope_kind = if method.item.name.item == "init" {
                    ScopeKind::Initializer
                } else {
                    ScopeKind::Method
                };
                Self::resolve_function(ctx, &method.item.fun, scope_kind)?;
            }

            Ok(())
        })?;
        Ok(())
    }
}

impl<'env> Resolver<'env> {
    pub fn resolve_own_stmt(&mut self, stmt: &StmtNode<'env>) -> Result {
        Self::resolve_stmt(&mut self.ctx, &stmt.item, stmt.span)
    }

    pub fn resolve_own_expr(&mut self, expr: &ExprNode<'env>) -> Result {
        Self::resolve_expr(&mut self.ctx, &expr.item, expr.span)
    }
}

#[derive(Debug)]
pub struct StreamResolver<'env, R, I> {
    resolver: Resolver<'env>,
    input: I,
    _rule: PhantomData<R>,
}

impl<'env, R, I> StreamResolver<'env, R, I> {
    pub fn new(tokens: I, arena: &'env Bump) -> Self {
        Self {
            resolver: Resolver::new(arena),
            input: tokens,
            _rule: PhantomData,
        }
    }
}

pub fn stmt_resolver<'env, I>(
    tokens: I,
    arena: &'env Bump,
) -> impl Iterator<Item = Result<StmtNode<'env>>>
where
    I: IntoIterator<Item = StmtNode<'env>>,
{
    StreamResolver::<StatementRule, _>::new(tokens.into_iter(), arena)
}

pub fn expr_resolver<'env, I>(
    tokens: I,
    arena: &'env Bump,
) -> impl Iterator<Item = Result<ExprNode<'env>>>
where
    I: IntoIterator<Item = ExprNode<'env>>,
{
    StreamResolver::<ExpressionRule, _>::new(tokens.into_iter(), arena)
}

impl<'env, R, I> Iterator for StreamResolver<'env, R, I>
where
    R: ResolverRule,
    I: Iterator<Item = R::Input<'env>>,
{
    type Item = Result<I::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        let input = self.input.next()?;
        let res = R::resolve(&mut self.resolver, &input).map(|_| input);
        Some(res)
    }
}

pub trait ResolverRule: Sized {
    type Input<'env>;

    fn resolve<'env>(interpreter: &mut Resolver<'env>, input: &Self::Input<'env>) -> Result;
}

impl ResolverRule for ExpressionRule {
    type Input<'env> = ExprNode<'env>;

    fn resolve<'env>(interpreter: &mut Resolver<'env>, input: &Self::Input<'env>) -> Result {
        interpreter.resolve_own_expr(input)
    }
}

impl ResolverRule for StatementRule {
    type Input<'env> = StmtNode<'env>;

    fn resolve<'env>(interpreter: &mut Resolver<'env>, input: &Self::Input<'env>) -> Result {
        interpreter.resolve_own_stmt(input)
    }
}
