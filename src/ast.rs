#[derive(Debug, Clone, PartialEq)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Neq,
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
    Var(String),
    Old(String), // The "old(x)" operator
    Binary(Box<Expr>, Op, Box<Expr>),
    Cast(Type, Box<Expr>),
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Assign {
        target: String,
        value: Expr,
    },
    If {
        cond: Expr,
        then_block: Vec<Stmt>,
        else_block: Vec<Stmt>,
    },
    While {
        cond: Expr,
        invariant: Expr, // The user MUST use invariant for now
        body: Vec<Stmt>,
    },
    ArrayUpdate {
        target: String,
        index: Expr,
        value: Expr,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    Nat,
    Array(Box<Type>),
}

pub struct FnDecl {
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub requires: Vec<Expr>,
    pub ensures: Vec<Expr>,
    pub body: Vec<Stmt>,
}
