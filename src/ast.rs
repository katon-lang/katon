use crate::errors::{Span, Spanned};
use std::fmt::{Display, Formatter, Result};

pub type SExpr = Spanned<Expr>;
pub type SStmt = Spanned<Stmt>;

// A unique identifier for every definition/use in the program
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeId(pub u32);

#[derive(Debug, Clone, PartialEq)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Neq,
    And,
    Gt,
    Lt,
    Gte,
    Lte,
    Index,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    IntLit(i64),
    BoolLit(bool),
    Var(String, Option<NodeId>), // Var now stores its resolved ID after the name resolution pass
    Old(String, Option<NodeId>),
    Binary(Box<SExpr>, Op, Box<SExpr>),
    Cast(Type, Box<SExpr>),
    ArrayLit(Vec<SExpr>),
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Let {
        name: String,
        ty: Option<Type>,
        value: Option<SExpr>,
        id: Option<NodeId>,
    },
    Assign {
        target: String,
        target_id: Option<NodeId>, // Filled by the resolver
        value: SExpr,
    },
    If {
        cond: SExpr,
        then_block: Vec<SStmt>,
        else_block: Vec<SStmt>,
    },
    While {
        cond: SExpr,
        invariant: SExpr, // The user MUST use invariant for now
        body: Vec<SStmt>,
    },
    ArrayUpdate {
        target: String,
        target_id: Option<NodeId>,
        index: SExpr,
        value: SExpr,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    Nat,
    Bool,
    Array(usize, Box<Type>),
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Type::Int => write!(f, "int"),
            Type::Nat => write!(f, "nat"),
            Type::Bool => write!(f, "bool"),
            Type::Array(size, inner) => write!(f, "[{}; {}]", size, inner),
        }
    }
}

pub struct FnDecl {
    pub name: String,
    pub params: Vec<(NodeId, Type)>,
    pub param_names: Vec<String>,
    pub requires: Vec<SExpr>,
    pub ensures: Vec<SExpr>,
    pub body: Vec<SStmt>,
    pub span: Span,
}
