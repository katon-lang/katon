use crate::ast::{Expr, FnDecl, Op, Stmt};
use std::collections::{HashMap, HashSet};

struct Env {
    global_gen: HashMap<String, usize>,
    current_scope: HashMap<String, usize>,
}

impl Env {
    fn new() -> Self {
        Self {
            global_gen: HashMap::new(),
            current_scope: HashMap::new(),
        }
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
                Op::Neq => "!=",
                Op::Div => "/",
            };
            format!("({} {} {})", op_str, l, r)
        }
    }
}

fn process_block(stmts: &[Stmt], env: &mut Env, smt: &mut String) {
    for stmt in stmts {
        match stmt {
            Stmt::Assign { target, value } => {
                let val_smt = expr_to_smt(value, env);
                let new_target = env.new_version(target);
                smt.push_str(&format!("(declare-const {} Int)\n", new_target));
                smt.push_str(&format!("(assert (= {} {}))\n", new_target, val_smt));
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

                // 4. MERGE (Phi Node)
                // Identify all vars modified in either branch
                let mut all_vars: HashSet<String> = HashSet::new();
                for k in then_scope.keys() {
                    all_vars.insert(k.clone());
                }

                for k in else_scope.keys() {
                    all_vars.insert(k.clone());
                }

                for var in all_vars {
                    let v_then = then_scope.get(&var).unwrap_or(&0);
                    let v_else = else_scope.get(&var).unwrap_or(&0);
                    let v_start = start_scope.get(&var).unwrap_or(&0);

                    // If either branch changed the variable relative to start...
                    if v_then != v_start || v_else != v_start {
                        let name_then = format!("{}_{}", var, v_then);
                        let name_else = format!("{}_{}", var, v_else);

                        // Create a NEW global version for the merge
                        let name_merged = env.new_version(&var);

                        smt.push_str(&format!("(declare-const {} Int)\n", name_merged));
                        smt.push_str(&format!(
                            "(assert (= {} (ite {} {} {})))\n",
                            name_merged, cond_smt, name_then, name_else
                        ));
                    }
                    // Else: variable wasn't touched in either branch, do nothing.
                }
            }
        }
    }
}

pub fn compile(func: &FnDecl) -> String {
    let mut smt = String::from("(set-logic QF_LIA)\n");
    let mut env = Env::new();

    // Inputs (Version 0)
    for param in &func.params {
        smt.push_str(&format!("(declare-const {}_0 Int)\n", param));
    }

    // Preconditions
    for req in &func.requires {
        smt.push_str(&format!("(assert {})\n", expr_to_smt(req, &env)));
    }

    // Body
    process_block(&func.body, &mut env, &mut smt);

    // Postconditions
    for ens in &func.ensures {
        let cond = expr_to_smt(ens, &env);
        smt.push_str(&format!("(assert (not {}))\n", cond));
    }

    smt.push_str("(check-sat)\n");
    smt
}
