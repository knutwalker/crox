use crate::{Node, Scoped, Span, StmtNode};
use std::{
    fmt::{Debug, Display},
    rc::Rc,
};

pub type ExprNode<'a> = Node<Rc<Expr<'a>>>;

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<'a> {
    Literal(Literal<'a>),
    Var(Var<'a>),
    Fun(FunctionDef<'a>),
    Assignment {
        name: &'a str,
        scope: Scoped,
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
    Get {
        object: ExprNode<'a>,
        name: Node<&'a str>,
    },
    Set {
        object: ExprNode<'a>,
        name: Node<&'a str>,
        value: ExprNode<'a>,
    },
    Super {
        method: Node<&'a str>,
        scope: Scoped,
    },
    This {
        scope: Scoped,
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

    pub fn var(name: &'a str) -> Self {
        Self::Var(Var::new(name))
    }

    pub fn fun(fun: FunctionDef<'a>) -> Self {
        Self::Fun(fun)
    }

    pub fn assign(name: &'a str, value: ExprNode<'a>) -> Self {
        Self::Assignment {
            name,
            scope: Scoped::new(),
            value,
        }
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

    pub fn get(object: ExprNode<'a>, name: Node<&'a str>) -> Self {
        Self::Get { object, name }
    }

    pub fn set(object: ExprNode<'a>, name: Node<&'a str>, value: ExprNode<'a>) -> Self {
        Self::Set {
            object,
            name,
            value,
        }
    }

    pub fn super_(method: Node<&'a str>) -> Self {
        Self::Super {
            method,
            scope: Scoped::new(),
        }
    }

    pub fn this() -> Self {
        Self::This {
            scope: Scoped::new(),
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

#[derive(Clone, Debug, PartialEq)]
pub struct Var<'a> {
    pub name: &'a str,
    pub scope: Scoped,
}

impl<'a> Var<'a> {
    pub fn new(name: &'a str) -> Self {
        Self {
            name,
            scope: Scoped::new(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct FunctionDef<'a> {
    pub params: Rc<[Node<&'a str>]>,
    pub body: Rc<[StmtNode<'a>]>,
}

impl<'a> FunctionDef<'a> {
    pub fn new(
        params: impl Into<Rc<[Node<&'a str>]>>,
        body: impl Into<Rc<[StmtNode<'a>]>>,
    ) -> Self {
        Self {
            params: params.into(),
            body: body.into(),
        }
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
