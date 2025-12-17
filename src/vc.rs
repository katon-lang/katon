use crate::ast::{Expr, FnDecl, Op, Stmt, Type};
use std::collections::{BTreeMap, BTreeSet};

struct Env {
    global_gen: BTreeMap<String, usize>,
    current_scope: BTreeMap<String, usize>,
    var_types: BTreeMap<String, Type>,
}

impl Env {
    fn new() -> Self {
        Self {
            global_gen: BTreeMap::new(),
            current_scope: BTreeMap::new(),
            var_types: BTreeMap::new(),
        }
    }

    // Register a variable's type (called during declaration/params)
    fn register_var(&mut self, name: &str, ty: Type) {
        self.var_types.insert(name.to_string(), ty);
    }

    // Check if a variable is a Nat
    fn is_nat(&self, name: &str) -> bool {
        matches!(self.var_types.get(name), Some(Type::Nat))
    }

    // Get current SSA name (e.g., "x_2")
    fn get(&self, name: &str) -> String {
        let ver = self.current_scope.get(name).unwrap_or(&0);
        format!("{}_{}", name, ver)
    }

    // Get original entry name (e.g., "x_0") for old()
    fn get_old(&self, name: &str) -> String {
        format!("{}_0", name)
    }

    fn new_version(&mut self, name: &str) -> String {
        let new_gen = self.global_gen.entry(name.to_string()).or_insert(0);
        *new_gen += 1; // Always increment global counter
        let new_ver = *new_gen;

        self.current_scope.insert(name.to_string(), new_ver);
        format!("{}_{}", name, new_ver)
    }
}

fn expr_to_smt(expr: &Expr, env: &Env) -> String {
    match expr {
        Expr::IntLit(n) => n.to_string(),
        Expr::BoolLit(b) => b.to_string(),
        Expr::Var(name) => env.get(name),
        Expr::Old(name) => env.get_old(name),
        Expr::Cast(_, inner) => expr_to_smt(inner, env), // The safety check happens at the assignment level
        Expr::Binary(lhs, op, rhs) => {
            let l = expr_to_smt(lhs, env);
            let r = expr_to_smt(rhs, env);
            let op_str = match op {
                Op::Add => "+",
                Op::Sub => "-",
                Op::Eq => "=",
                Op::Gt => ">",
                Op::Lt => "<",
                Op::Gte => ">=",
                Op::Lte => "<=",
                Op::Mul => "*",
                Op::Neq => "distinct",
                Op::Div => "div",
                Op::Index => "select",
            };
            format!("({} {} {})", op_str, l, r)
        }
    }
}

fn get_modified_vars(stmts: &[Stmt]) -> Vec<String> {
    let mut vars = Vec::new();
    for stmt in stmts {
        match stmt {
            Stmt::Assign { target, .. } => vars.push(target.clone()),
            Stmt::If {
                then_block,
                else_block,
                ..
            } => {
                vars.extend(get_modified_vars(then_block));
                vars.extend(get_modified_vars(else_block));
            }
            Stmt::While { body, .. } => {
                vars.extend(get_modified_vars(body));
            }
            Stmt::ArrayUpdate { target, .. } => vars.push(target.clone()),
        }
    }

    vars.sort();
    vars.dedup(); // Remove duplicates
    vars
}

fn type_to_smt(ty: &Type) -> String {
    match ty {
        Type::Int | Type::Nat => "Int".to_string(),
        Type::Array(inner) => format!("(Array Int {})", type_to_smt(inner)),
    }
}

fn process_block(stmts: &[Stmt], env: &mut Env, smt: &mut String) {
    for stmt in stmts {
        match stmt {
            Stmt::Assign { target, value } => {
                let val_smt = expr_to_smt(value, env);

                // If target is Nat, we MUST prove value >= 0 before proceeding
                if env.is_nat(target) {
                    smt.push_str(&format!("; SAFETY CHECK: {} must be Nat\n", target));
                    smt.push_str("(push)\n");
                    // We assert the negation: "Is it possible for val to be < 0?"
                    smt.push_str(&format!("(assert (< {} 0))\n", val_smt));
                    smt.push_str("(check-sat)\n");
                    // If SAT -> Verification Error: "Assignment violates nat type"
                    smt.push_str("(pop)\n");
                }

                let new_target = env.new_version(target);

                // Get the type string (e.g., "Int" or "(Array Int Int)")
                let ty_smt = if let Some(ty) = env.var_types.get(target) {
                    type_to_smt(ty)
                } else {
                    "Int".to_string() // Fallback/Error
                };

                smt.push_str(&format!("(declare-const {} {})\n", new_target, ty_smt));
                smt.push_str(&format!("(assert (= {} {}))\n", new_target, val_smt));

                // Add the type constraint to the main path too, so future logic knows it's positive
                if env.is_nat(target) {
                    smt.push_str(&format!("(assert (>= {} 0))\n", new_target));
                }
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                let cond_smt = expr_to_smt(cond, env);

                // 1. Save Scope (NOT global counters)
                let start_scope = env.current_scope.clone();

                // 2. Process THEN
                process_block(then_block, env, smt);
                let then_scope = env.current_scope.clone();

                // 3. Restore Scope & Process ELSE
                env.current_scope = start_scope.clone(); // Reset local scope
                process_block(else_block, env, smt);
                let else_scope = env.current_scope.clone();

                let mut vars = BTreeSet::new();
                vars.extend(start_scope.keys().cloned());
                vars.extend(then_scope.keys().cloned());
                vars.extend(else_scope.keys().cloned());

                for var in vars {
                    let v_start = *start_scope.get(&var).unwrap_or(&0);
                    let v_then = *then_scope.get(&var).unwrap_or(&v_start);
                    let v_else = *else_scope.get(&var).unwrap_or(&v_start);

                    if v_then != v_start || v_else != v_start {
                        let merged = env.new_version(&var);
                        smt.push_str(&format!("(declare-const {} Int)\n", merged));
                        let then_name = format!("{}_{}", var, v_then);
                        let else_name = format!("{}_{}", var, v_else);

                        smt.push_str(&format!(
                            "(assert (= {} (ite {} {} {})))\n",
                            merged, cond_smt, then_name, else_name
                        ));
                    }
                }
            }
            Stmt::While {
                cond,
                invariant,
                body,
            } => {
                // Assert Invariant holds on Entry
                // Does the invariant hold BEFORE the loop starts?
                let inv_entry = expr_to_smt(invariant, env);
                smt.push_str("; CHECK 1: Loop Entry Invariant\n");
                smt.push_str("(push)\n");
                smt.push_str(&format!("(assert (not {}))\n", inv_entry)); // Negate to find bug
                smt.push_str("(check-sat)\n");
                smt.push_str("(pop)\n");

                // Fast-forward to an arbitrary iteration
                let modified = get_modified_vars(body);
                for var in &modified {
                    let new_ver = env.new_version(var);
                    smt.push_str(&format!("(declare-const {} Int)\n", new_ver));
                }

                // Assume we are in a valid state (Invariant is True)
                let inv_havoc = expr_to_smt(invariant, env);
                smt.push_str(&format!("(assert {})\n", inv_havoc));

                // If (Cond is True) AND (Body runs) -> Does Invariant still hold?
                smt.push_str("; CHECK 2: Loop Body Maintenance\n");
                smt.push_str("(push)\n");

                // A. Assume Loop Condition is True
                let cond_havoc = expr_to_smt(cond, env);
                smt.push_str(&format!("(assert {})\n", cond_havoc));

                // B. Run Body (This advances variable versions in 'env')
                // CRITICAL: We need a temporary env clone so we don't mess up the main path
                let mut body_env = Env {
                    global_gen: env.global_gen.clone(),
                    current_scope: env.current_scope.clone(),
                    var_types: env.var_types.clone(),
                };

                process_block(body, &mut body_env, smt);

                // C. Check Invariant Post-Body
                let inv_post = expr_to_smt(invariant, &body_env);
                smt.push_str(&format!("(assert (not {}))\n", inv_post)); // Negate to check
                smt.push_str("(check-sat)\n");
                smt.push_str("(pop)\n");

                // Continue the main analysis assuming the Loop Condition is FALSE
                let cond_exit = expr_to_smt(cond, env);
                smt.push_str(&format!("(assert (not {}))\n", cond_exit));
            }
            Stmt::ArrayUpdate {
                target,
                index,
                value,
            } => {
                let idx_smt = expr_to_smt(index, env);
                let val_smt = expr_to_smt(value, env);
                let current_arr = env.get(target);

                // [STRICT] Bounds check would go here:
                // (assert (>= idx 0))
                // (assert (< idx len))

                // Create new array version
                let new_arr = env.new_version(target);
                let ty_smt = type_to_smt(env.var_types.get(target).unwrap());

                // Declare: (declare-const a_2 (Array Int Int))
                smt.push_str(&format!("(declare-const {} {})\n", new_arr, ty_smt));

                // Logic: (assert (= a_2 (store a_1 i v)))
                smt.push_str(&format!(
                    "(assert (= {} (store {} {} {})))\n",
                    new_arr, current_arr, idx_smt, val_smt
                ));
            }
        }
    }
}

pub fn compile(func: &FnDecl) -> String {
    let mut smt = String::from("(set-logic QF_AUFNIA)\n");
    let mut env = Env::new();

    for (name, ty) in &func.params {
        env.register_var(name, ty.clone());
        let ty_smt = type_to_smt(ty);

        smt.push_str(&format!("(declare-const {}_0 {})\n", name, ty_smt));
        env.current_scope.insert(name.clone(), 0);

        if let Type::Nat = ty {
            smt.push_str(&format!("(assert (>= {}_0 0))\n", name));
        }
    }

    // Preconditions
    let requires = if func.requires.is_empty() {
        "true".to_string()
    } else {
        format!(
            "(and {})",
            func.requires
                .iter()
                .map(|r| expr_to_smt(r, &env))
                .collect::<Vec<_>>()
                .join(" ")
        )
    };

    smt.push_str(&format!("(assert {})\n", requires));

    // Body
    process_block(&func.body, &mut env, &mut smt);

    // Postconditions
    // We check: implies(BodyLogic, Ensures)
    // By checking SAT of: BodyLogic AND (NOT Ensures)
    for ens in &func.ensures {
        let post = expr_to_smt(ens, &env);
        smt.push_str("; CHECK POSTCONDITION\n");
        smt.push_str("(push)\n");
        smt.push_str(&format!("(assert (not {}))\n", post));
        smt.push_str("(check-sat)\n");
        smt.push_str("(pop)\n");
    }

    smt
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runner::verify_with_z3;

    fn var(s: &str) -> Box<Expr> {
        Box::new(Expr::Var(s.to_string()))
    }

    fn int(i: i64) -> Box<Expr> {
        Box::new(Expr::IntLit(i))
    }

    fn bin(l: Box<Expr>, op: Op, r: Box<Expr>) -> Expr {
        Expr::Binary(l, op, r)
    }

    #[test]
    fn test_compile_abs_function_with_merge() {
        // LOGIC TO TEST:
        // fn abs(x: int) {
        //    let y = x;       <-- y_1 defined here (Start Scope for IF)
        //    if x < 0 {
        //       y = 0 - x;    <-- y_2 (Then Branch)
        //    } else {
        //       y = x;        <-- y_3 (Else Branch)
        //    }
        //    // Merge happens here: y_4 = ite(..., y_2, y_3)
        // }
        // ensures y >= 0

        let func = FnDecl {
            name: "abs".to_string(),
            params: vec![("x".to_string(), Type::Int)], // x_0 declared automatically
            requires: vec![],
            body: vec![
                // 1. Init y = x
                Stmt::Assign {
                    target: "y".to_string(),
                    value: Expr::Var("x".to_string()),
                },
                // 2. If x < 0
                Stmt::If {
                    cond: bin(var("x"), Op::Lt, int(0)),
                    then_block: vec![
                        // y = 0 - x
                        Stmt::Assign {
                            target: "y".to_string(),
                            value: bin(int(0), Op::Sub, var("x")),
                        },
                    ],
                    else_block: vec![
                        // y = x
                        Stmt::Assign {
                            target: "y".to_string(),
                            value: Expr::Var("x".to_string()),
                        },
                    ],
                },
            ],
            ensures: vec![
                // y >= 0
                bin(var("y"), Op::Gte, int(0)),
            ],
        };

        let smt_output = compile(&func);

        println!("Generated SMT:\n{}", smt_output);

        // --- ASSERTIONS ---

        // 1. Verify Inputs
        assert!(smt_output.contains("(declare-const x_0 Int)"));

        // 2. Verify Initial Assignment (y = x) -> y_1
        // Note: env.new_version increments first, so 0->1.
        assert!(smt_output.contains("(declare-const y_1 Int)"));
        assert!(smt_output.contains("(= y_1 x_0)"));

        // 3. Verify Branches (y_2 and y_3)
        // Then block: y = 0 - x
        assert!(smt_output.contains("(= y_2 (- 0 x_0))"));

        // Else block: y = x (Depending on scope reuse, likely y_3)
        assert!(smt_output.contains("(= y_3 x_0)"));

        // 4. Verify THE MERGE (Phi Node)
        // This is the critical part. It must define y_4 using 'ite'
        assert!(smt_output.contains("(declare-const y_4 Int)"));
        assert!(smt_output.contains("ite (< x_0 0) y_2 y_3"));

        // 5. Verify Post-condition Negation
        // Must check (not (>= y_4 0))
        assert!(smt_output.contains("(not (>= y_4 0))"));

        // 6. Verify Solver Command
        assert!(smt_output.contains("(check-sat)"));
    }

    #[test]
    fn test_loop_body_verification_fails() {
        // BUGGY CODE:
        // i = 0
        // while i < n invariant i <= n {
        //    i = i - 1; // <--- BUG! This breaks the invariant (i <= n) or termination?
        //               // Actually, if i becomes -1, -1 <= n is still true...
        //               // Let's make a clearer bug:
        //               // Invariant: i >= 0. Body: i = i - 1.
        // }

        let func = FnDecl {
            name: "buggy_loop".to_string(),
            params: vec![("n".to_string(), Type::Int)],
            requires: vec![bin(var("n"), Op::Gt, int(0))],
            body: vec![
                Stmt::Assign {
                    target: "i".to_string(),
                    value: Expr::IntLit(0),
                },
                Stmt::While {
                    cond: bin(var("i"), Op::Lt, var("n")),
                    invariant: bin(var("i"), Op::Gte, int(0)), // i must stay positive
                    body: vec![
                        // BUG: Decrementing i makes it negative!
                        Stmt::Assign {
                            target: "i".to_string(),
                            value: bin(var("i"), Op::Sub, int(1)),
                        },
                    ],
                },
            ],
            ensures: vec![],
        };

        let smt = compile(&func);
        let result = verify_with_z3(&smt);

        // This MUST fail. If it says "Ok", the verifier is broken.
        assert!(result.is_err());
    }

    #[test]
    fn test_compile_array_update() {
        // SCENARIO:
        // func update(arr []int) {
        //    arr[0] = 99
        //    ensures arr[0] == 99
        //    ensures arr[1] == old(arr)[1] // Frame property
        // }

        let func = FnDecl {
            name: "update".to_string(),
            params: vec![("arr".to_string(), Type::Array(Box::new(Type::Int)))],
            requires: vec![],
            body: vec![Stmt::ArrayUpdate {
                target: "arr".to_string(),
                index: Expr::IntLit(0),
                value: Expr::IntLit(99),
            }],
            ensures: vec![
                // arr[0] == 99
                bin(
                    Box::new(bin(var("arr"), Op::Index, int(0))),
                    Op::Eq,
                    int(99),
                ),
                // arr[1] == old(arr)[1] (Prove we didn't touch index 1)
                bin(
                    Box::new(bin(var("arr"), Op::Index, int(1))),
                    Op::Eq,
                    Box::new(Expr::Binary(
                        Box::new(Expr::Old("arr".to_string())),
                        Op::Index,
                        int(1),
                    )),
                ),
            ],
        };

        let smt = compile(&func);
        println!("{}", smt);

        // 1. Declare Array
        assert!(smt.contains("(declare-const arr_0 (Array Int Int))"));

        // 2. Store Operation (Assign 99 to index 0)
        assert!(smt.contains("(declare-const arr_1 (Array Int Int))"));
        assert!(smt.contains("(= arr_1 (store arr_0 0 99))"));

        // 3. Post-conditions (Select)
        // Checks arr_1[0] == 99
        assert!(smt.contains("(select arr_1 0)"));
        // Checks arr_1[1] == arr_0[1]
        assert!(smt.contains("(select arr_1 1)"));
        assert!(smt.contains("(select arr_0 1)"));
    }
}
