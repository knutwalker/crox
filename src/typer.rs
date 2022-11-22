use crate::{
    BinaryOp, CroxError, CroxErrorKind, EnumSet, Expr, ExprNode, Literal, Node, Range, Result,
    UnaryOp, Value, ValueEnum,
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

#[derive(Clone, Debug, PartialEq)]
pub struct TypedExpr<'a> {
    pub expr: Expr<'a>,
    pub typ: Type,
}

pub fn typer<'a, I>(tokens: I) -> impl Iterator<Item = Result<Node<TypedExpr<'a>>>>
where
    I: IntoIterator<Item = ExprNode<'a>>,
{
    tokens.into_iter().map(type_node)
}

pub fn type_node(node: ExprNode<'_>) -> Result<Node<TypedExpr<'_>>> {
    let typ = type_check(&node.item)?;
    Ok(Node::new(
        TypedExpr {
            expr: *node.item,
            typ,
        },
        node.span,
    ))
}

pub fn type_check(expr: &Expr<'_>) -> Result<Type> {
    let typ = match expr {
        Expr::Literal(l) => l.typ(),
        Expr::Unary(op, node) => match op {
            UnaryOp::Neg => {
                let typ = type_check(&node.item)?;
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
                let typ = type_check(&lhs.item)?;
                let typ = check(
                    typ,
                    TypeSet::from_iter([Type::Number, Type::String]),
                    lhs.span,
                )?;

                check(type_check(&rhs.item)?, TypeSet::from(typ), rhs.span)?;
                typ
            }
            BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div => {
                check_num(type_check(&lhs.item)?, lhs.span)?;
                check_num(type_check(&rhs.item)?, rhs.span)?;
                Type::Number
            }
        },
        Expr::Group(expr) => type_check(&expr.item)?,
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
