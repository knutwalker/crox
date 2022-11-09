use crate::{
    BinaryOp, CroxError, CroxErrorKind, EnumSet, Expr, Idx, Literal, Node, Range, Resolve, Result,
    TypedAst, TypedAstBuilder, UnaryOp, UntypedAst, Value, ValueEnum,
};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Type {
    Bool,
    Number,
    String,
    Function,
    Class,
    Nil,
}

impl Literal<'_> {
    pub fn typ(&self) -> Type {
        match self {
            Self::Nil => Type::Nil,
            Self::True | Self::False => Type::Bool,
            Self::Number(_) => Type::Number,
            Self::String(_) => Type::String,
        }
    }
}

impl Value {
    pub fn typ(&self) -> Type {
        match self {
            Self::Nil => Type::Nil,
            Self::Bool(_) => Type::Bool,
            Self::Number(_) => Type::Number,
            Self::Str(_) => Type::String,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct TypedNode {
    pub node: Node,
    pub typ: Type,
}

pub fn type_ast(ast: UntypedAst<'_>) -> Result<TypedAst<'_>> {
    let mut builder = TypedAstBuilder::new(ast);
    let (exprs, mut adder) = builder.split();
    for expr in exprs {
        let typ = type_check(&adder, expr)?;
        adder.add(typ);
    }
    Ok(builder.build())
}

pub fn type_ast_with(ast: UntypedAst<'_>, mut report: impl FnMut(CroxError)) -> TypedAst<'_> {
    let mut builder = TypedAstBuilder::new(ast);
    let (exprs, mut adder) = builder.split();
    for expr in exprs {
        let typ = match type_check(&adder, expr) {
            Ok(typ) => typ,
            Err(err) => {
                report(err);
                Type::Nil
            }
        };
        adder.add(typ);
    }
    builder.build()
}

pub fn type_node<'a, R: Resolve<'a, Expr<'a>> + ?Sized>(
    resolver: &R,
    node: Node,
) -> Result<TypedNode> {
    struct ExprResolver<'x, R: ?Sized>(&'x R);

    impl<'a, 'x, R: Resolve<'a, Expr<'a>> + ?Sized> Resolve<'a, Result<Type>> for ExprResolver<'x, R> {
        fn resolve(&self, idx: Idx) -> Result<Type> {
            let node = self.0.resolve(idx);
            type_check(self, &node)
        }
    }

    let expr = resolver.resolve(node.idx);
    let typ = type_check(&ExprResolver(resolver), &expr)?;

    Ok(TypedNode { node, typ })
}

pub fn type_check<'a, R: Resolve<'a, Result<Type>> + ?Sized>(
    resolver: &R,
    expr: &Expr<'a>,
) -> Result<Type> {
    let typ = match expr {
        Expr::Literal(l) => l.typ(),
        Expr::Unary(op, node) => match op {
            UnaryOp::Neg => {
                let typ = resolver.resolve(node.idx)?;
                check_num(typ, node.span)?;
                Type::Number
            }
            UnaryOp::Not => Type::Bool,
        },
        Expr::Binary(lhs, op, rhs) => match op {
            BinaryOp::Equals
            | BinaryOp::NotEquals
            | BinaryOp::LessThan
            | BinaryOp::LessThanOrEqual
            | BinaryOp::GreaterThan
            | BinaryOp::GreaterThanOrEqual => Type::Bool,
            BinaryOp::Add => {
                let typ = resolver.resolve(lhs.idx)?;
                let typ = check(
                    typ,
                    TypeSet::from_iter([Type::Number, Type::String]),
                    lhs.span,
                )?;
                check(resolver.resolve(rhs.idx)?, TypeSet::from(typ), rhs.span)?;
                typ
            }
            BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div => {
                check_num(resolver.resolve(lhs.idx)?, lhs.span)?;
                check_num(resolver.resolve(rhs.idx)?, rhs.span)?;
                Type::Number
            }
        },
        Expr::Group(expr) => resolver.resolve(expr.idx)?,
    };
    Ok(typ)
}

fn check_num(typ: Type, span: impl Into<Range>) -> Result {
    check(typ, TypeSet::from(Type::Number), span)?;
    Ok(())
}

fn check(typ: Type, expected: TypeSet, span: impl Into<Range>) -> Result<Type> {
    if expected.contains(typ) {
        Ok(typ)
    } else {
        Err(CroxError::new(
            CroxErrorKind::InvalidType {
                expected,
                actual: typ,
            },
            span,
        ))
    }
}

impl ValueEnum for Type {
    fn to_ord(&self) -> u8 {
        *self as u8
    }

    unsafe fn from_ord(ord: u8) -> Self {
        std::mem::transmute_copy(&ord)
    }
}

pub type TypeSet = EnumSet<Type>;
