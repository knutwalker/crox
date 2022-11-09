use crate::{
    BinaryOp, CroxError, CroxErrorKind, EnumSet, Expr, ExprNode, Idx, Literal, Resolve, Result,
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
pub struct TypedExpr {
    pub expr: Expr,
    pub typ: Type,
}

pub fn type_ast(ast: UntypedAst<'_>) -> Result<TypedAst<'_>> {
    let mut builder = TypedAstBuilder::new(ast);
    let (nodes, mut adder) = builder.split();
    for node in nodes {
        let typ = type_check(&adder, node)?;
        adder.add(typ);
    }
    Ok(builder.build())
}

pub fn type_ast_with(ast: UntypedAst<'_>, mut report: impl FnMut(CroxError)) -> TypedAst<'_> {
    let mut builder = TypedAstBuilder::new(ast);
    let (nodes, mut adder) = builder.split();
    for node in nodes {
        let typ = match type_check(&adder, node) {
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

pub fn type_expr<'a, R: Resolve<'a, ExprNode<'a>> + ?Sized>(
    resolver: &R,
    expr: Expr,
) -> Result<TypedExpr> {
    struct ExprResolver<'x, R: ?Sized>(&'x R);

    impl<'a, 'x, R: Resolve<'a, ExprNode<'a>> + ?Sized> Resolve<'a, Result<Type>>
        for ExprResolver<'x, R>
    {
        fn resolve(&self, idx: Idx) -> Result<Type> {
            let node = self.0.resolve(idx);
            type_check(self, &node)
        }
    }

    let node = resolver.resolve(expr.idx);
    let typ = type_check(&ExprResolver(resolver), &node)?;

    Ok(TypedExpr { expr, typ })
}

pub fn type_check<'a, R: Resolve<'a, Result<Type>> + ?Sized>(
    resolver: &R,
    node: &ExprNode<'a>,
) -> Result<Type> {
    let typ = match node {
        ExprNode::Literal(l) => l.typ(),
        ExprNode::Unary(op, expr) => match op {
            UnaryOp::Neg => {
                let typ = resolver.resolve(expr.idx)?;
                check_num(typ, expr)?;
                Type::Number
            }
            UnaryOp::Not => Type::Bool,
        },
        ExprNode::Binary(lhs, op, rhs) => match op {
            BinaryOp::Equals
            | BinaryOp::NotEquals
            | BinaryOp::LessThan
            | BinaryOp::LessThanOrEqual
            | BinaryOp::GreaterThan
            | BinaryOp::GreaterThanOrEqual => Type::Bool,
            BinaryOp::Add => {
                let typ = resolver.resolve(lhs.idx)?;
                let typ = check(typ, TypeSet::from_iter([Type::Number, Type::String]), lhs)?;
                check(resolver.resolve(rhs.idx)?, TypeSet::from(typ), rhs)?;
                typ
            }
            BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div => {
                check_num(resolver.resolve(lhs.idx)?, lhs)?;
                check_num(resolver.resolve(rhs.idx)?, rhs)?;
                Type::Number
            }
        },
        ExprNode::Group(expr) => resolver.resolve(expr.idx)?,
    };
    Ok(typ)
}

fn check_num(typ: Type, expr: &Expr) -> Result {
    check(typ, TypeSet::from(Type::Number), expr)?;
    Ok(())
}

fn check(typ: Type, expected: TypeSet, expr: &Expr) -> Result<Type> {
    if expected.contains(typ) {
        Ok(typ)
    } else {
        Err(CroxError::new(
            CroxErrorKind::InvalidType {
                expected,
                actual: typ,
            },
            expr.span,
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
