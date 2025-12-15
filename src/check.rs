// Implement the borrow checker
use crate::ast::{Expr, FnDecl, Stmt};
use std::collections::HashMap;

pub struct BorrowChecker {
    scope: HashMap<String, bool>, // Name -> IsAlive?
}

impl Default for BorrowChecker {
    fn default() -> Self {
        Self::new()
    }
}

impl BorrowChecker {
    pub fn new() -> Self {
        Self {
            scope: HashMap::new(),
        }
    }

    pub fn check_fn(&mut self, func: &FnDecl) -> Result<(), String> {
        // Initialize args as Alive
        for param in &func.params {
            self.scope.insert(param.clone(), true);
        }

        // Check Body
        for stmt in &func.body {
            self.check_stmt(stmt)?;
        }

        Ok(())
    }

    fn check_stmt(&mut self, stmt: &Stmt) -> Result<(), String> {
        match stmt {
            Stmt::Assign { target, value } => {
                self.check_expr(value)?; // Check RHS first (Use)
                self.scope.insert(target.clone(), true); // Revive LHS (Define)
                Ok(())
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                self.check_expr(cond)?;
                // Cloning scope for simplistic branch checking
                let start_scope = self.scope.clone();

                for s in then_block {
                    self.check_stmt(s)?;
                }
                // Restore for else? (Naive implementation for now)
                self.scope = start_scope;
                for s in else_block {
                    self.check_stmt(s)?;
                }

                Ok(())
            }
        }
    }

    fn check_expr(&mut self, expr: &Expr) -> Result<(), String> {
        match expr {
            Expr::Var(name) => {
                if let Some(true) = self.scope.get(name) {
                    Ok(())
                } else {
                    Err(format!(
                        "Borrow Error: Variable '{}' is undefined or moved.",
                        name
                    ))
                }
            }
            Expr::Binary(l, _, r) => {
                self.check_expr(l)?;
                self.check_expr(r)
            }
            _ => Ok(()),
        }
    }
}
