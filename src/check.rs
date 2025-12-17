// Implementation of affine types
use crate::ast::{Expr, FnDecl, Op, Stmt, Type};
use std::collections::HashMap;

pub struct BorrowChecker {
    scope: HashMap<String, (bool, Type)>, // Name -> IsAlive?
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
        // Register variable as Alive with its Type
        for (name, ty) in &func.params {
            self.scope.insert(name.clone(), (true, ty.clone()));
        }

        // Check Body
        for stmt in &func.body {
            self.check_stmt(stmt)?;
        }

        Ok(())
    }

    fn is_copy(&self, ty: &Type) -> bool {
        match ty {
            Type::Int | Type::Nat => true, // Primitives copy
            Type::Array(_) => false,       // Array moves
        }
    }

    fn check_stmt(&mut self, stmt: &Stmt) -> Result<(), String> {
        match stmt {
            Stmt::Assign { target, value } => {
                // Check RHS first (Use)
                self.check_expr(value)?;

                // Revive LHS (Define)
                // Note: We need to know the type of 'target'.
                // For simplified checking, we assume 'target' already exists in scope
                // or we need a symbol table pass before this.
                if let Some((_, ty)) = self.scope.get(target).cloned() {
                    self.scope.insert(target.clone(), (true, ty));
                } else {
                    // It's a new definition (e.g. x := 5)
                    // For now, default to Int if unknown, or error.
                    // Ideally, Katon AST needs type inference here.
                    self.scope.insert(target.clone(), (true, Type::Int));
                }
                Ok(())
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                self.check_expr(cond)?;

                let start_scope = self.scope.clone();

                // Then Branch
                for s in then_block {
                    self.check_stmt(s)?;
                }

                let then_scope = self.scope.clone();

                // Else Branch
                self.scope = start_scope.clone();
                for s in else_block {
                    self.check_stmt(s)?;
                }

                let else_scope = self.scope.clone();

                // Merge
                self.scope = self.merge_scopes(then_scope, else_scope);
                Ok(())
            }
            Stmt::While {
                cond,
                invariant,
                body,
            } => {
                self.check_expr(cond)?;
                self.check_expr(invariant)?;

                // Snapshot scope before loop
                let start_scope = self.scope.clone();

                // Check body
                for s in body {
                    self.check_stmt(s)?;
                }

                // Verify Loop Safety (No moves of outer variables)
                // We check: Did any variable that was alive at start become dead?
                for (name, (was_alive, _)) in &start_scope {
                    if *was_alive {
                        let (is_alive_after, _) = self.scope.get(name).unwrap();
                        if !is_alive_after {
                            return Err(format!(
                                "Borrow Error: Cannot move outer variable '{}' inside a loop.",
                                name
                            ));
                        }
                    }
                }

                // Reset Scope
                // After the loop, the state is effectively the same as start
                // (because we forbade moves), but variables defined INSIDE the loop die.
                self.scope = start_scope;

                Ok(())
            }
            Stmt::ArrayUpdate {
                target,
                index,
                value,
            } => {
                //  Check the Index expression (Read)
                self.check_expr(index)?;

                // 2. Check the Value expression (Read/Move)
                self.check_expr(value)?;

                // 3. Verify the Array itself is Valid
                if let Some((is_alive, ty)) = self.scope.get(target) {
                    // Rule: Katon cannot modify a moved array
                    if !is_alive {
                        return Err(format!(
                            "Borrow Error: Cannot assign to moved or uninitialized array '{}'.",
                            target
                        ));
                    }

                    // Rule: Must actually be an Array type
                    if !matches!(ty, Type::Array(_)) {
                        return Err(format!("Type Error: '{}' is not an array.", target));
                    }
                } else {
                    return Err(format!("Borrow Error: Undefined variable '{}'.", target));
                }

                Ok(())
            }
        }
    }

    fn check_expr(&mut self, expr: &Expr) -> Result<(), String> {
        match expr {
            Expr::Var(name) => {
                if let Some((is_alive, ty)) = self.scope.get(name).cloned() {
                    if !is_alive {
                        return Err(format!("Borrow Error: Use of moved value: {}", name));
                    }

                    // Only "Kill" if NOT Copy
                    if !self.is_copy(&ty) {
                        self.scope.insert(name.clone(), (false, ty));
                    }
                    Ok(())
                } else {
                    Err(format!("Borrow Error: Undefined variable: {}", name))
                }
            }
            Expr::Cast(_, inner) => self.check_expr(inner),
            Expr::Binary(lhs, Op::Index, rhs) => {
                // 1. Check the Index (rhs)
                self.check_expr(rhs)?;

                // 2. Check the Array (lhs) carefully
                // If lhs is a variable, we peek at it without killing it
                if let Expr::Var(name) = &**lhs
                    && let Some((is_alive, _)) = self.scope.get(name)
                {
                    if !is_alive {
                        return Err(format!("Borrow Error: Use of moved value: {}", name));
                    }

                    // DO NOT insert(false) here. Indexing borrows, it doesn't consume.
                    return Ok(());
                }

                // If lhs is complex (e.g. arr_factory()[0]), process recursively
                self.check_expr(lhs)
            }
            Expr::Binary(l, _, r) => {
                // Order matters! Left is evaluated/moved first.
                self.check_expr(l)?;
                self.check_expr(r)
            }
            Expr::Old(name) => {
                // old(x) usually borrows, so we might check existence without killing?
                // For safety, let's treat it as a read
                if self.scope.contains_key(name) {
                    Ok(())
                } else {
                    Err(format!("Undefined variable in old(): {}", name))
                }
            }
            _ => Ok(()),
        }
    }

    fn merge_scopes(
        &self,
        s1: HashMap<String, (bool, Type)>,
        s2: HashMap<String, (bool, Type)>,
    ) -> HashMap<String, (bool, Type)> {
        let mut result = HashMap::new();

        // We iterate over the union of keys, but practically iterating s1 is often enough
        // if we assume new variables declared inside blocks die at end of block.
        // But to be safe, let's look at s1.
        for (key, (alive1, ty1)) in s1 {
            if let Some((alive2, _)) = s2.get(&key) {
                // Alive only if alive in BOTH branches
                result.insert(key, (alive1 && *alive2, ty1));
            }
            // If missing in s2, it was defined in s1 block -> Drops out of scope (Dead)
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{Op, Type};

    use super::*;

    fn var(n: &str) -> Expr {
        Expr::Var(n.to_string())
    }

    fn int(n: i64) -> Expr {
        Expr::IntLit(n)
    }

    fn bin(l: Expr, op: Op, r: Expr) -> Expr {
        Expr::Binary(Box::new(l), op, Box::new(r))
    }

    #[test]
    fn test_borrow_checker_moves() {
        let mut bc = BorrowChecker::new();

        // fn test(x int) {
        //    if true {
        //       let y = x; // x is COPIED here (not moved)
        //    } else {
        //       // x alive here
        //    }
        //
        //    let z = x; // OK: x is still alive because Int is Copy
        // }

        let func = FnDecl {
            name: "test".to_string(),
            params: vec![("x".to_string(), Type::Int)],
            requires: vec![],
            ensures: vec![],
            body: vec![
                Stmt::If {
                    cond: Expr::BoolLit(true),
                    then_block: vec![Stmt::Assign {
                        target: "y".to_string(),
                        value: var("x"),
                    }],
                    else_block: vec![],
                },
                Stmt::Assign {
                    target: "z".to_string(),
                    value: var("x"),
                },
            ],
        };

        let result = bc.check_fn(&func);
        assert!(result.is_ok(), "Int should be Copy, so x remains alive");
    }

    #[test]
    fn test_copy_semantics_for_int_and_nat() {
        // SCENARIO:
        //
        // func test(x int, y nat) {
        //      z = x + x;
        //      w = y * y;
        // }
        //
        // This fails if Borrow Checker treats Int/Nat as "Move" (Affine)

        let mut bc = BorrowChecker::new();

        let func = FnDecl {
            name: "math_test".to_string(),
            params: vec![("x".to_string(), Type::Int), ("y".to_string(), Type::Nat)],
            requires: vec![],
            ensures: vec![],
            body: vec![
                // 1. Test Int Copy: z = x + x
                Stmt::Assign {
                    target: "z".to_string(),
                    value: bin(var("x"), Op::Add, var("x")),
                },
                // 2. Test Nat Copy: w = y * y
                Stmt::Assign {
                    target: "w".to_string(),
                    value: bin(var("y"), Op::Mul, var("y")),
                },
            ],
        };

        let result = bc.check_fn(&func);

        // Should pass
        assert!(result.is_ok(), "Int and Nat should be Copy types!")
    }

    #[test]
    fn test_scope_leak_if_block() {
        // SCENARIO:
        // func fail(x int) {
        //    if x > 0 {
        //       y = 10
        //    }
        //
        //    z = y  <-- ERROR: 'y' is not in scope here
        // }

        let mut bc = BorrowChecker::new();

        let func = FnDecl {
            name: "scope_leak".to_string(),
            params: vec![("x".to_string(), Type::Int)],
            requires: vec![],
            ensures: vec![],
            body: vec![
                Stmt::If {
                    cond: bin(var("x"), Op::Gt, int(0)),
                    then_block: vec![Stmt::Assign {
                        target: "y".to_string(),
                        value: int(10),
                    }],
                    else_block: vec![],
                },
                // The illegal access
                Stmt::Assign {
                    target: "z".to_string(),
                    value: var("y"),
                },
            ],
        };

        let result = bc.check_fn(&func);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "Borrow Error: Undefined variable: y");
    }

    #[test]
    fn test_merge_scope_correctness() {
        // SCENARIO:
        // func merge(cond int) {
        //    if cond > 0 {
        //       y = 1
        //    } else {
        //       y = 2
        //    }
        //
        //    z = y  <-- OK: 'y' is defined in BOTH branches
        // }

        let mut bc = BorrowChecker::new();

        let func = FnDecl {
            name: "merge_valid".to_string(),
            params: vec![("cond".to_string(), Type::Int)],
            requires: vec![],
            ensures: vec![],
            body: vec![
                Stmt::If {
                    cond: bin(var("cond"), Op::Gt, int(0)),
                    then_block: vec![Stmt::Assign {
                        target: "y".to_string(),
                        value: int(1),
                    }],
                    else_block: vec![Stmt::Assign {
                        target: "y".to_string(),
                        value: int(2),
                    }],
                },
                // Should succeed because 'y' exists in both paths
                Stmt::Assign {
                    target: "z".to_string(),
                    value: var("y"),
                },
            ],
        };

        let result = bc.check_fn(&func);
        assert!(result.is_ok())
    }

    #[test]
    fn test_undefined_variable() {
        // SCENARIO
        // z = unknown_var

        let mut bc = BorrowChecker::new();

        let func = FnDecl {
            name: "bad_var".to_string(),
            params: vec![], // No params
            requires: vec![],
            ensures: vec![],
            body: vec![Stmt::Assign {
                target: "z".to_string(),
                value: var("unknown_var"),
            }],
        };

        let result = bc.check_fn(&func);
        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .contains("Undefined variable: unknown_var")
        );
    }
}
