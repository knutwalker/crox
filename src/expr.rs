use crate::{Bump, Ident, Node, Scoped, Slotted, StmtNode};
use std::fmt::{Debug, Display};

pub type ExprNode<'env> = Node<Expr<'env>>;
pub type BoxedExpr<'env> = Node<&'env Expr<'env>>;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Expr<'env> {
    Literal(Literal<'env>),
    Var(Var<'env>),
    Fun(FunctionDef<'env>),
    Assignment {
        name: &'env str,
        scope: &'env Scoped,
        value: BoxedExpr<'env>,
    },
    Unary {
        op: UnaryOp,
        expr: BoxedExpr<'env>,
    },
    Logical {
        lhs: BoxedExpr<'env>,
        op: LogicalOp,
        rhs: BoxedExpr<'env>,
    },
    Binary {
        lhs: BoxedExpr<'env>,
        op: BinaryOp,
        rhs: BoxedExpr<'env>,
    },
    Call {
        callee: BoxedExpr<'env>,
        arguments: &'env [ExprNode<'env>],
    },
    Get {
        object: BoxedExpr<'env>,
        name: Ident<'env>,
        slot: &'env Slotted,
    },
    Set {
        object: BoxedExpr<'env>,
        name: Ident<'env>,
        value: BoxedExpr<'env>,
    },
    Super {
        method: Ident<'env>,
        scope: &'env Scoped,
        slot: &'env Slotted,
    },
    This {
        scope: &'env Scoped,
    },
    Group {
        expr: BoxedExpr<'env>,
    },
}

impl<'env> Expr<'env> {
    pub fn nil() -> Self {
        Self::Literal(Literal::Nil)
    }

    pub fn tru() -> Self {
        Self::Literal(Literal::True)
    }

    pub fn fals() -> Self {
        Self::Literal(Literal::False)
    }

    pub fn number(num: f64) -> Self {
        Self::Literal(Literal::Number(num))
    }

    pub fn string(s: &'env str) -> Self {
        Self::Literal(Literal::String(s))
    }

    pub fn var(name: &'env str, arena: &'env Bump) -> Self {
        Self::Var(Var::new(name, arena))
    }

    pub fn fun(fun: FunctionDef<'env>) -> Self {
        Self::Fun(fun)
    }

    pub fn assign(name: &'env str, value: BoxedExpr<'env>, arena: &'env Bump) -> Self {
        Self::Assignment {
            name,
            scope: arena.alloc(Scoped::new()),
            value,
        }
    }

    pub fn neg(expr: BoxedExpr<'env>) -> Self {
        Self::Unary {
            op: UnaryOp::Neg,
            expr,
        }
    }

    pub fn not(expr: BoxedExpr<'env>) -> Self {
        Self::Unary {
            op: UnaryOp::Not,
            expr,
        }
    }

    pub fn unary(op: UnaryOp, expr: BoxedExpr<'env>) -> Self {
        Self::Unary { op, expr }
    }

    pub fn and(lhs: BoxedExpr<'env>, rhs: BoxedExpr<'env>) -> Self {
        Self::Logical {
            lhs,
            op: LogicalOp::And,
            rhs,
        }
    }

    pub fn or(lhs: BoxedExpr<'env>, rhs: BoxedExpr<'env>) -> Self {
        Self::Logical {
            lhs,
            op: LogicalOp::Or,
            rhs,
        }
    }

    pub fn logical(lhs: BoxedExpr<'env>, op: LogicalOp, rhs: BoxedExpr<'env>) -> Self {
        Self::Logical { lhs, op, rhs }
    }

    pub fn add(lhs: BoxedExpr<'env>, rhs: BoxedExpr<'env>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::Add,
            rhs,
        }
    }

    pub fn sub(lhs: BoxedExpr<'env>, rhs: BoxedExpr<'env>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::Sub,
            rhs,
        }
    }

    pub fn mul(lhs: BoxedExpr<'env>, rhs: BoxedExpr<'env>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::Mul,
            rhs,
        }
    }

    pub fn div(lhs: BoxedExpr<'env>, rhs: BoxedExpr<'env>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::Div,
            rhs,
        }
    }

    pub fn equals(lhs: BoxedExpr<'env>, rhs: BoxedExpr<'env>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::Equals,
            rhs,
        }
    }

    pub fn not_equals(lhs: BoxedExpr<'env>, rhs: BoxedExpr<'env>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::NotEquals,
            rhs,
        }
    }

    pub fn less_than(lhs: BoxedExpr<'env>, rhs: BoxedExpr<'env>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::LessThan,
            rhs,
        }
    }

    pub fn less_than_or_equal(lhs: BoxedExpr<'env>, rhs: BoxedExpr<'env>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::LessThanOrEqual,
            rhs,
        }
    }

    pub fn greater_than(lhs: BoxedExpr<'env>, rhs: BoxedExpr<'env>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::GreaterThan,
            rhs,
        }
    }

    pub fn greater_than_or_equal(lhs: BoxedExpr<'env>, rhs: BoxedExpr<'env>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::GreaterThanOrEqual,
            rhs,
        }
    }

    pub fn binary(lhs: BoxedExpr<'env>, op: BinaryOp, rhs: BoxedExpr<'env>) -> Self {
        Self::Binary { lhs, op, rhs }
    }

    pub fn call(callee: BoxedExpr<'env>, arguments: &'env [ExprNode<'env>]) -> Self {
        Self::Call { callee, arguments }
    }

    pub fn get(object: BoxedExpr<'env>, name: Ident<'env>, arena: &'env Bump) -> Self {
        Self::Get {
            object,
            name,
            slot: arena.alloc(Slotted::default()),
        }
    }

    pub fn set(object: BoxedExpr<'env>, name: Ident<'env>, value: BoxedExpr<'env>) -> Self {
        Self::Set {
            object,
            name,
            value,
        }
    }

    pub fn super_(method: Ident<'env>, arena: &'env Bump) -> Self {
        Self::Super {
            method,
            scope: arena.alloc(Scoped::new()),
            slot: arena.alloc(Slotted::default()),
        }
    }

    pub fn this(arena: &'env Bump) -> Self {
        Self::This {
            scope: arena.alloc(Scoped::new()),
        }
    }

    pub fn group(expr: BoxedExpr<'env>) -> Self {
        Self::Group { expr }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Literal<'env> {
    Nil,
    True,
    False,
    Number(f64),
    String(&'env str),
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Var<'env> {
    pub name: &'env str,
    pub scope: &'env Scoped,
}

impl<'env> Var<'env> {
    pub fn new(name: &'env str, arena: &'env Bump) -> Self {
        Self {
            name,
            scope: arena.alloc(Scoped::new()),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct FunctionDef<'env> {
    pub params: &'env [Ident<'env>],
    pub body: &'env [StmtNode<'env>],
}

impl<'env> FunctionDef<'env> {
    pub fn new(params: &'env [Ident<'env>], body: &'env [StmtNode<'env>]) -> Self {
        Self { params, body }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum LogicalOp {
    And,
    Or,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum BinaryOp {
    Equals,
    NotEquals,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    Add,
    Sub,
    Mul,
    Div,
}

impl Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Neg => f.write_str("-"),
            Self::Not => f.write_str("!"),
        }
    }
}

impl Display for LogicalOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::And => f.write_str("and"),
            Self::Or => f.write_str("or"),
        }
    }
}

impl Display for BinaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Equals => f.write_str("=="),
            Self::NotEquals => f.write_str("!="),
            Self::LessThan => f.write_str("<"),
            Self::LessThanOrEqual => f.write_str("<="),
            Self::GreaterThan => f.write_str(">"),
            Self::GreaterThanOrEqual => f.write_str(">="),
            Self::Add => f.write_str("+"),
            Self::Sub => f.write_str("-"),
            Self::Mul => f.write_str("*"),
            Self::Div => f.write_str("/"),
        }
    }
}
