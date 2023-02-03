use crate::{
    Bump, ClassDecl, Context, CroxErrorKind, Environment, Expr, ExprNode, ExpressionRule,
    FunctionDef, Result, Scoped, Span, StatementRule, Stmt, StmtNode, Var,
};
use std::marker::PhantomData;

pub type ResolverContext<'env> = Context<'env, Current, ()>;

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

impl<'env> ResolverContext<'env> {
    pub fn empty(arena: &'env Bump) -> Self {
        Self::new(Environment::empty(), arena, Current::default())
    }
}

impl<'env> ResolverContext<'env> {
    pub fn resolve_stmts_in_scope(&mut self, stmts: &[StmtNode<'env>]) -> Result {
        stmts
            .iter()
            .try_for_each(|stmt| self.resolve_stmt(&stmt.item, stmt.span))
    }

    pub fn resolve_stmt(&mut self, stmt: &Stmt<'env>, span: Span) -> Result {
        match stmt {
            Stmt::Expression { expr } => {
                self.resolve_expr(expr.item, expr.span)?;
            }
            Stmt::Class(class) => {
                self.env.define(class.name.item, ());
                let mut guard = self.swap_data(self.data.with_class(ClassKind::Class));
                if let Some(superclass) = &class.superclass {
                    if superclass.item.name == class.name.item {
                        return Err(CroxErrorKind::InheritsSelf.at(superclass.span));
                    }

                    guard.resolve_local(superclass.item.name, superclass.item.scope);

                    let new_data = guard.data.with_class(ClassKind::Subclass);
                    let mut inner_guard = guard.swap_data(new_data);

                    inner_guard.run_with_new_scope(|ctx| {
                        ctx.env.define("super", ());
                        ctx.resolve_class(class)
                    })?;
                } else {
                    guard.resolve_class(class)?;
                }
            }
            Stmt::Function(func) => {
                self.env.define(func.name.item, ());
                Self::resolve_function(self, &func.fun, ScopeKind::Function)?;
            }
            Stmt::If {
                condition,
                then_,
                else_,
            } => {
                self.resolve_expr(condition.item, condition.span)?;
                self.resolve_stmt(then_.item, then_.span)?;
                if let Some(else_) = else_ {
                    self.resolve_stmt(else_.item, else_.span)?;
                }
            }
            Stmt::Print { expr } => {
                self.resolve_expr(expr.item, expr.span)?;
            }
            Stmt::Return { expr } => {
                if self.data.scope == ScopeKind::TopLevel {
                    return Err(CroxErrorKind::ReturnFromTopLevel.at(span));
                }
                if let Some(expr) = expr.as_ref() {
                    if self.data.scope == ScopeKind::Initializer {
                        return Err(CroxErrorKind::ReturnFromInitializer.at(span));
                    }
                    self.resolve_expr(expr.item, expr.span)?;
                }
            }
            Stmt::Var { name, initializer } => {
                // The book splits this into two steps to make shadowing an error.
                // In Crox, we allow shadowing.
                if let Some(init) = initializer.as_ref() {
                    self.resolve_expr(init.item, init.span)?;
                }
                self.env.define_local(name.item, ());
            }
            Stmt::While { condition, body } => {
                self.resolve_expr(condition.item, condition.span)?;
                self.resolve_stmt(body.item, body.span)?;
            }
            Stmt::Block { stmts } => {
                self.run_with_new_scope(|ctx| ctx.resolve_stmts_in_scope(stmts))?;
            }
        };
        Ok(())
    }

    pub fn resolve_expr(&mut self, expr: &Expr<'env>, span: Span) -> Result {
        match expr {
            Expr::Literal(_) => {}
            Expr::Var(Var { name, scope }) => self.resolve_local(name, scope),
            Expr::Fun(func) => self.resolve_function(func, ScopeKind::Function)?,
            Expr::Assignment { name, scope, value } => {
                self.resolve_expr(value.item, value.span)?;
                self.resolve_local(name, scope);
            }
            Expr::Unary { expr, .. } => {
                self.resolve_expr(expr.item, expr.span)?;
            }
            Expr::Logical { lhs, rhs, .. } => {
                self.resolve_expr(lhs.item, lhs.span)?;
                self.resolve_expr(rhs.item, rhs.span)?;
            }
            Expr::Binary { lhs, rhs, .. } => {
                self.resolve_expr(lhs.item, lhs.span)?;
                self.resolve_expr(rhs.item, rhs.span)?;
            }
            Expr::Call { callee, arguments } => {
                self.resolve_expr(callee.item, callee.span)?;
                arguments
                    .iter()
                    .try_for_each(|arg| self.resolve_expr(&arg.item, arg.span))?;
            }
            Expr::Get {
                object,
                name: _,
                slot: _,
            } => {
                self.resolve_expr(object.item, object.span)?;
            }
            Expr::Set {
                object,
                name: _,
                value,
            } => {
                self.resolve_expr(value.item, value.span)?;
                self.resolve_expr(object.item, object.span)?;
            }
            Expr::Super {
                method: _,
                scope,
                slot: _,
            } => {
                match self.data.class {
                    ClassKind::Global => return Err(CroxErrorKind::SuperOutsideClass.at(span)),
                    ClassKind::Class => {
                        return Err(CroxErrorKind::SuperInClassWithoutSuperclass.at(span))
                    }
                    ClassKind::Subclass => {}
                }
                self.resolve_local("super", scope);
            }
            Expr::This { scope } => {
                if self.data.class == ClassKind::Global {
                    return Err(CroxErrorKind::ThisOutsideClass.at(span));
                }
                if self.data.scope == ScopeKind::ClassMethod {
                    return Err(CroxErrorKind::ThisInClassMethod.at(span));
                }
                self.resolve_local("this", scope);
            }
            Expr::Group { expr } => {
                self.resolve_expr(expr.item, expr.span)?;
            }
        };
        Ok(())
    }

    fn resolve_local(&mut self, name: &'env str, scope: &Scoped) {
        if let Ok(resolved) = self.env.scope_of(name) {
            scope.resolve(resolved);
        }
    }

    fn resolve_function(&mut self, func: &FunctionDef<'env>, scope_type: ScopeKind) -> Result {
        self.run_with_new_scope(|ctx| {
            let mut guard = ctx.swap_data(ctx.data.with_scope(scope_type));

            for param in func.params.iter() {
                guard
                    .env
                    .define_local_unique(param.item, ())
                    .map_err(|e| CroxErrorKind::from(e).at(param.span))?;
            }
            guard.resolve_stmts_in_scope(func.body)?;
            Ok(())
        })
    }

    fn resolve_class(&mut self, class: &ClassDecl<'env>) -> Result {
        self.run_with_new_scope(|ctx| -> Result {
            for method in class.members().class_methods() {
                ctx.resolve_function(&method.item.fun, ScopeKind::ClassMethod)?;
            }
            ctx.env.define("this", ());
            for property in class.members().properties() {
                ctx.resolve_function(&property.item.fun, ScopeKind::Method)?;
            }
            for method in class.members().methods() {
                let scope_kind = if method.item.name.item == "init" {
                    ScopeKind::Initializer
                } else {
                    ScopeKind::Method
                };
                ctx.resolve_function(&method.item.fun, scope_kind)?;
            }

            Ok(())
        })?;
        Ok(())
    }
}

#[derive(Debug)]
pub struct StreamResolver<'env, R, I> {
    context: ResolverContext<'env>,
    input: I,
    _rule: PhantomData<R>,
}

impl<'env, R, I> StreamResolver<'env, R, I> {
    pub fn new(tokens: I, arena: &'env Bump) -> Self {
        Self {
            context: ResolverContext::empty(arena),
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
        let res = R::resolve(&mut self.context, &input).map(|_| input);
        Some(res)
    }
}

pub trait ResolverRule: Sized {
    type Input<'env>;

    fn resolve<'env>(context: &mut ResolverContext<'env>, input: &Self::Input<'env>) -> Result;
}

impl ResolverRule for ExpressionRule {
    type Input<'env> = ExprNode<'env>;

    fn resolve<'env>(context: &mut ResolverContext<'env>, input: &Self::Input<'env>) -> Result {
        context.resolve_expr(&input.item, input.span)
    }
}

impl ResolverRule for StatementRule {
    type Input<'env> = StmtNode<'env>;

    fn resolve<'env>(context: &mut ResolverContext<'env>, input: &Self::Input<'env>) -> Result {
        context.resolve_stmt(&input.item, input.span)
    }
}
