use crate::{Node, Span};
use std::{
    fmt::{Debug, Display},
    rc::Rc,
};

pub type ExprNode<'a> = Node<Rc<Expr<'a>>>;

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<'a> {
    Literal(Literal<'a>),
    Var(&'a str),
    Assignment {
        name: &'a str,
        value: ExprNode<'a>,
    },
    Unary {
        op: UnaryOp,
        expr: ExprNode<'a>,
    },
    Logical {
        lhs: ExprNode<'a>,
        op: LogicalOp,
        rhs: ExprNode<'a>,
    },
    Binary {
        lhs: ExprNode<'a>,
        op: BinaryOp,
        rhs: ExprNode<'a>,
    },
    Call {
        callee: ExprNode<'a>,
        arguments: Rc<[ExprNode<'a>]>,
    },
    Group {
        expr: ExprNode<'a>,
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

    pub fn var(s: &'a str) -> Self {
        Self::Var(s)
    }

    pub fn assign(name: &'a str, value: ExprNode<'a>) -> Self {
        Self::Assignment { name, value }
    }

    pub fn neg(expr: ExprNode<'a>) -> Self {
        Self::Unary {
            op: UnaryOp::Neg,
            expr,
        }
    }

    pub fn not(expr: ExprNode<'a>) -> Self {
        Self::Unary {
            op: UnaryOp::Not,
            expr,
        }
    }

    pub fn unary(op: UnaryOp, expr: ExprNode<'a>) -> Self {
        Self::Unary { op, expr }
    }

    pub fn and(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Logical {
            lhs,
            op: LogicalOp::And,
            rhs,
        }
    }

    pub fn or(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Logical {
            lhs,
            op: LogicalOp::Or,
            rhs,
        }
    }

    pub fn logical(lhs: ExprNode<'a>, op: LogicalOp, rhs: ExprNode<'a>) -> Self {
        Self::Logical { lhs, op, rhs }
    }

    pub fn add(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::Add,
            rhs,
        }
    }

    pub fn sub(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::Sub,
            rhs,
        }
    }

    pub fn mul(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::Mul,
            rhs,
        }
    }

    pub fn div(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::Div,
            rhs,
        }
    }

    pub fn equals(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::Equals,
            rhs,
        }
    }

    pub fn not_equals(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::NotEquals,
            rhs,
        }
    }

    pub fn less_than(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::LessThan,
            rhs,
        }
    }

    pub fn less_than_or_equal(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::LessThanOrEqual,
            rhs,
        }
    }

    pub fn greater_than(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::GreaterThan,
            rhs,
        }
    }

    pub fn greater_than_or_equal(lhs: ExprNode<'a>, rhs: ExprNode<'a>) -> Self {
        Self::Binary {
            lhs,
            op: BinaryOp::GreaterThanOrEqual,
            rhs,
        }
    }

    pub fn binary(lhs: ExprNode<'a>, op: BinaryOp, rhs: ExprNode<'a>) -> Self {
        Self::Binary { lhs, op, rhs }
    }

    pub fn call(callee: ExprNode<'a>, arguments: impl Into<Rc<[ExprNode<'a>]>>) -> Self {
        Self::Call {
            callee,
            arguments: arguments.into(),
        }
    }

    pub fn group(expr: ExprNode<'a>) -> Self {
        Self::Group { expr }
    }

    pub fn at(self, span: impl Into<Span>) -> ExprNode<'a> {
        Node::new(Rc::new(self), span)
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
