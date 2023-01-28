use crate::{Bump, Ident, Node, Scoped, StmtNode};
use std::fmt::{Debug, Display};

pub type ExprNode<'a> = Node<Expr<'a>>;
pub type BoxedExpr<'a> = Node<&'a Expr<'a>>;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Expr<'a> {
    Literal(Literal<'a>),
    Var(Var<'a>),
    Fun(FunctionDef<'a>),
    Assignment {
        name: &'a str,
        scope: &'a Scoped,
        value: BoxedExpr<'a>,
    },
    Unary {
        op: UnaryOp,
        expr: BoxedExpr<'a>,
    },
    Logical {
        lhs: BoxedExpr<'a>,
        op: LogicalOp,
        rhs: BoxedExpr<'a>,
    },
    Binary {
        lhs: BoxedExpr<'a>,
        op: BinaryOp,
        rhs: BoxedExpr<'a>,
    },
    Call {
        callee: BoxedExpr<'a>,
        arguments: &'a [ExprNode<'a>],
    },
    Get {
        object: BoxedExpr<'a>,
        name: Ident<'a>,
    },
    Set {
        object: BoxedExpr<'a>,
        name: Ident<'a>,
        value: BoxedExpr<'a>,
    },
    Super {
        method: Ident<'a>,
        scope: &'a Scoped,
    },
    This {
        scope: &'a Scoped,
    },
    Group {
        expr: BoxedExpr<'a>,
    },
}

impl<'a> Expr<'a> {
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

    pub fn string(s: &'a str) -> Self {
        Self::Literal(Literal::String(s))
    }

    pub fn var(name: &'a str, arena: &'a Bump) -> Self {
        Self::Var(Var::new(name, arena))
    }

    pub fn fun(fun: FunctionDef<'a>) -> Self {
        Self::Fun(fun)
    }

    pub fn assign(name: &'a str, value: BoxedExpr<'a>, arena: &'a Bump) -> Self {
        Self::Assignment {
            name,
            scope: arena.alloc(Scoped::new()),
            value,
        }
    }

    pub fn neg(expr: BoxedExpr<'a>) -> Self {
        Self::Unary {
            op: UnaryOp::Neg,
            expr,
        }
    }

    pub fn not(expr: BoxedExpr<'a>) -> Self {
        Self::Unary {
            op: UnaryOp::Not,
            expr,
        }
    }

    pub fn unary(op: UnaryOp, expr: BoxedExpr<'a>) -> Self {
        Self::Unary { op, expr }
    }

    pub fn and(lhs: BoxedExpr<'a>, rhs: BoxedExpr<'a>) -> Self {
        Self::Logical {
            lhs,
            op: LogicalOp::And,
            rhs,
        }
    }

    pub fn or(lhs: BoxedExpr<'a>, rhs: BoxedExpr<'a>) -> Self {
        Self::Logical {
            lhs,
            op: LogicalOp::Or,
            rhs,
        }
    }

    pub fn logical(lhs: BoxedExpr<'a>, op: LogicalOp, rhs: BoxedExpr<'a>) -> Self {
        Self::Logical { lhs, op, rhs }
    }

    pub fn add(lhs: BoxedExpr<'a>, rhs: BoxedExpr<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::Add,
            rhs,
        }
    }

    pub fn sub(lhs: BoxedExpr<'a>, rhs: BoxedExpr<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::Sub,
            rhs,
        }
    }

    pub fn mul(lhs: BoxedExpr<'a>, rhs: BoxedExpr<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::Mul,
            rhs,
        }
    }

    pub fn div(lhs: BoxedExpr<'a>, rhs: BoxedExpr<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::Div,
            rhs,
        }
    }

    pub fn equals(lhs: BoxedExpr<'a>, rhs: BoxedExpr<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::Equals,
            rhs,
        }
    }

    pub fn not_equals(lhs: BoxedExpr<'a>, rhs: BoxedExpr<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::NotEquals,
            rhs,
        }
    }

    pub fn less_than(lhs: BoxedExpr<'a>, rhs: BoxedExpr<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::LessThan,
            rhs,
        }
    }

    pub fn less_than_or_equal(lhs: BoxedExpr<'a>, rhs: BoxedExpr<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::LessThanOrEqual,
            rhs,
        }
    }

    pub fn greater_than(lhs: BoxedExpr<'a>, rhs: BoxedExpr<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::GreaterThan,
            rhs,
        }
    }

    pub fn greater_than_or_equal(lhs: BoxedExpr<'a>, rhs: BoxedExpr<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::GreaterThanOrEqual,
            rhs,
        }
    }

    pub fn binary(lhs: BoxedExpr<'a>, op: BinaryOp, rhs: BoxedExpr<'a>) -> Self {
        Self::Binary { lhs, op, rhs }
    }

    pub fn call(callee: BoxedExpr<'a>, arguments: &'a [ExprNode<'a>]) -> Self {
        Self::Call { callee, arguments }
    }

    pub fn get(object: BoxedExpr<'a>, name: Ident<'a>) -> Self {
        Self::Get { object, name }
    }

    pub fn set(object: BoxedExpr<'a>, name: Ident<'a>, value: BoxedExpr<'a>) -> Self {
        Self::Set {
            object,
            name,
            value,
        }
    }

    pub fn super_(method: Ident<'a>, arena: &'a Bump) -> Self {
        Self::Super {
            method,
            scope: arena.alloc(Scoped::new()),
        }
    }

    pub fn this(arena: &'a Bump) -> Self {
        Self::This {
            scope: arena.alloc(Scoped::new()),
        }
    }

    pub fn group(expr: BoxedExpr<'a>) -> Self {
        Self::Group { expr }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Literal<'a> {
    Nil,
    True,
    False,
    Number(f64),
    String(&'a str),
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Var<'a> {
    pub name: &'a str,
    pub scope: &'a Scoped,
}

impl<'a> Var<'a> {
    pub fn new(name: &'a str, arena: &'a Bump) -> Self {
        Self {
            name,
            scope: arena.alloc(Scoped::new()),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct FunctionDef<'a> {
    pub params: &'a [Ident<'a>],
    pub body: &'a [StmtNode<'a>],
}

impl<'a> FunctionDef<'a> {
    pub fn new(params: &'a [Ident<'a>], body: &'a [StmtNode<'a>]) -> Self {
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
