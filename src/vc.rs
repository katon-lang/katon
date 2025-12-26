use crate::{
    ast::{Expr, FnDecl, NodeId, Op, SExpr, SStmt, Stmt, Type},
    symbol_table::TyCtx,
};
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

// We make the variable SSA immutable by default
#[derive(Clone)]
struct Env {
    versions: HashMap<NodeId, usize>, // current SSA version
    gens: Rc<RefCell<HashMap<NodeId, usize>>>,
    var_types: HashMap<NodeId, Type>,
}

impl Env {
    fn new() -> Self {
        Self {
            versions: HashMap::new(),
            gens: Rc::new(RefCell::new(HashMap::new())),
            var_types: HashMap::new(),
        }
    }

    fn name(&self, id: NodeId, tcx: &TyCtx) -> String {
        let v = self.versions.get(&id).copied().unwrap_or(0);
        format!("{}_{}", tcx.get_name(&id), v)
    }

    fn old(&self, id: NodeId, tcx: &TyCtx) -> String {
        format!("{}_1", tcx.get_name(&id))
    }

    /// Create a fresh SSA version (immutable)
    fn assign(&self, id: NodeId) -> (Self, usize) {
        let mut next_env = self.clone();

        let mut gens = self.gens.borrow_mut();
        let v = gens.entry(id).or_insert(0);
        *v += 1;

        let new_ver = *v;
        next_env.versions.insert(id, new_ver);

        (next_env, new_ver)
    }

    fn register_var(&mut self, id: NodeId, ty: Type) {
        self.var_types.insert(id, ty);
    }
}

fn expr_to_smt(expr: &SExpr, env: &Env, tcx: &TyCtx, smt: &mut String) -> String {
    match &expr.node {
        Expr::IntLit(n) => n.to_string(),
        Expr::BoolLit(b) => b.to_string(),
        Expr::Var(name, Some(id)) => {
            if name.ends_with("_length") {
                name.clone()
            } else {
                env.name(*id, tcx)
            }
        }
        Expr::Old(_name, Some(id)) => env.old(*id, tcx),
        Expr::Cast(_, inner) => expr_to_smt(inner, env, tcx, smt), // The safety check happens at the assignment level
        Expr::Binary(lhs, op, rhs) => {
            let l_smt = expr_to_smt(lhs, env, tcx, smt);
            let r_smt = expr_to_smt(rhs, env, tcx, smt);

            match op {
                Op::Index => {
                    if let Expr::Var(name, _) = &lhs.node {
                        let len_name = format!("{}_length", name);
                        smt.push_str("; Safety Check: Array Read\n(push)\n");
                        smt.push_str(&format!(
                            "(assert (not (and (>= {0} 0) (< {0} {1}))))\n",
                            r_smt, len_name
                        ));
                        smt.push_str("(check-sat)\n(pop)\n");
                    }
                    format!("(select {} {})", l_smt, r_smt)
                }
                Op::Sub => format!("(- {} {})", l_smt, r_smt),
                Op::Lt => format!("(< {} {})", l_smt, r_smt),
                Op::Gte => format!("(>= {} {})", l_smt, r_smt),
                Op::Add => format!("(+ {} {})", l_smt, r_smt),
                Op::And => format!("(and {} {})", l_smt, r_smt),
                Op::Gt => format!("(> {} {})", l_smt, r_smt),
                Op::Eq => format!("(= {} {})", l_smt, r_smt),
                Op::Mul => format!("(* {} {})", l_smt, r_smt),
                Op::Div => format!("(div {} {})", l_smt, r_smt),
                _ => unimplemented!("Operator {:?} not implemented in SMT gen", op),
            }
        }
        Expr::ArrayLit(elems) => {
            // Determine the inner type of the array to create the correct 'as const'
            // Assuming Int for now based on your logic, but we specify the sort (Int) for the value 0
            // let mut current_array = format!("((as const (Array Int Int)) 0)");

            // CHANGE: If Z3 still complains, use the fully qualified version:
            let mut current_array = "((as const (Array Int Int)) 0)".to_string();

            // Note: If your array is of Bools, this would need to be ((as const (Array Int Bool)) false)

            for (i, elem) in elems.iter().enumerate() {
                let val_smt = expr_to_smt(elem, env, tcx, smt);
                current_array = format!("(store {} {} {})", current_array, i, val_smt);
            }

            current_array
        }
        _ => unimplemented!(),
    }
}

fn get_modified_vars(stmts: &[SStmt]) -> HashSet<NodeId> {
    let mut modified = HashSet::new();
    for stmt in stmts {
        match &stmt.node {
            Stmt::Let { id, .. } => {
                if let Some(id) = id {
                    modified.insert(*id);
                }
            }
            Stmt::Assign { target_id, .. } => {
                if let Some(id) = target_id {
                    modified.insert(*id);
                }
            }
            Stmt::ArrayUpdate { target_id, .. } => {
                if let Some(id) = target_id {
                    modified.insert(*id);
                }
            }
            Stmt::If {
                then_block,
                else_block,
                ..
            } => {
                modified.extend(get_modified_vars(then_block));
                modified.extend(get_modified_vars(else_block));
            }
            Stmt::While { body, .. } => {
                modified.extend(get_modified_vars(body));
            }
        }
    }
    modified
}

fn type_to_smt(ty: &Type) -> String {
    match ty {
        Type::Int | Type::Nat => "Int".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::Array(_size, inner) => format!("(Array Int {})", type_to_smt(inner)),
    }
}

fn process_block(
    stmts: &[SStmt],
    env: Env,
    smt: &mut String,
    tcx: &TyCtx,
    vcs: &mut Vec<String>,
) -> Env {
    let mut env = env;

    for stmt in stmts {
        match &stmt.node {
            Stmt::Assign {
                target_id, value, ..
            } => {
                let id = target_id.unwrap();
                let val_smt = expr_to_smt(value, &env, tcx, smt);
                let ty_obj = env.var_types.get(&id).unwrap();

                // If target is a Nat, the new value must be >= 0
                // Capture the entire state up to now, plus the failure condition
                if matches!(ty_obj, Type::Nat) {
                    let check = format!("{}\n(assert (not (>= {} 0)))\n(check-sat)", smt, val_smt);
                    vcs.push(check);
                }

                let (env2, ver) = env.assign(id);
                let name = format!("{}_{}", tcx.get_name(&id), ver);
                let ty_smt = type_to_smt(ty_obj);

                smt.push_str(&format!("(declare-const {} {})\n", name, ty_smt));
                smt.push_str(&format!("(assert (= {} {}))\n", name, val_smt));
                env = env2;
            }
            Stmt::Let { value, id, .. } => {
                let id = id.expect("Resolver must assign ID");
                let ty_obj = env.var_types.get(&id).expect("Type missing in env");

                if let Some(expr) = value {
                    let val_smt = expr_to_smt(expr, &env, tcx, smt);

                    // Safety Check: Nat Declaration
                    if matches!(ty_obj, Type::Nat) {
                        let check = format!(
                            "{smt}\n(assert (not (>= {val_smt} 0)))\n(check-sat)",
                            smt = smt,
                            val_smt = val_smt
                        );
                        vcs.push(check);
                    }

                    // Standard SSA assignment logic
                    let mut gens = env.gens.borrow_mut();
                    let v = gens.entry(id).or_insert(0);
                    *v += 1;
                    let ver = *v;
                    env.versions.insert(id, ver);

                    let name = format!("{}_{}", tcx.get_name(&id), ver);
                    smt.push_str(&format!(
                        "(declare-const {} {})\n",
                        name,
                        type_to_smt(ty_obj)
                    ));
                    smt.push_str(&format!("(assert (= {} {}))\n", name, val_smt));
                } else {
                    // --- CASE: let x: type; ---
                    // We don't declare a version yet (version remains 0).
                    // We just ensure the type is registered in the env (already done by compile()).
                    // This variable is now "known" but has no SMT identity until Assigned.
                }
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                let cond_smt = expr_to_smt(cond, &env, tcx, smt);

                // Process Then Block
                // We pass the main 'smt' string so declarations are recorded globally,
                // but we use a local_smt for assertions specific to this branch's safety checks.
                let mut then_smt = smt.clone();
                then_smt.push_str(&format!("(assert {})\n", cond_smt));

                // We need process_block to update the main 'smt'
                // with any new (declare-const) it creates.
                let then_env = process_block(then_block, env.clone(), smt, tcx, vcs);

                // Process Else Block
                let else_env = process_block(else_block, env.clone(), smt, tcx, vcs);

                // Merging (Phi functions)
                let mut merged_env = env.clone();
                let vars: HashSet<NodeId> = then_env
                    .versions
                    .keys()
                    .chain(else_env.versions.keys())
                    .cloned()
                    .collect();

                for id in vars {
                    let v_orig = env.versions.get(&id).copied().unwrap_or(0);
                    let v_then = then_env.versions.get(&id).copied().unwrap_or(v_orig);
                    let v_else = else_env.versions.get(&id).copied().unwrap_or(v_orig);

                    if v_then != v_orig || v_else != v_orig {
                        let (next, v_phi) = merged_env.assign(id);
                        merged_env = next;

                        let name = format!("{}_{}", tcx.get_name(&id), v_phi);
                        let ty = type_to_smt(merged_env.var_types.get(&id).unwrap());

                        // These go into the main 'smt' string
                        smt.push_str(&format!("(declare-const {} {})\n", name, ty));
                        smt.push_str(&format!(
                            "(assert (= {} (ite {} {}_{} {}_{})))\n",
                            name,
                            cond_smt,
                            tcx.get_name(&id),
                            v_then,
                            tcx.get_name(&id),
                            v_else
                        ));
                    }
                }

                env = merged_env;
            }
            Stmt::While {
                cond,
                invariant,
                body,
            } => {
                // Assert Invariant holds on Entry
                // Does the invariant hold BEFORE the loop starts?
                // Initial Check
                let inv_init = expr_to_smt(invariant, &env, tcx, smt);
                let entry_check = format!("{}\n(assert (not {}))\n(check-sat)", smt, inv_init);
                vcs.push(entry_check);

                // Havoc (Abstracting modified variables)
                let modified = get_modified_vars(body);
                let mut loop_env = env.clone();
                for id in modified {
                    let (next, ver) = loop_env.assign(id);
                    loop_env = next;
                    let ty_obj = loop_env.var_types.get(&id).unwrap();
                    let name = format!("{}_{}", tcx.get_name(&id), ver);

                    smt.push_str(&format!(
                        "(declare-const {} {})\n",
                        name,
                        type_to_smt(ty_obj)
                    ));

                    if matches!(ty_obj, Type::Nat) {
                        smt.push_str(&format!("(assert (>= {} 0))\n", name));
                    }
                }

                // Assume Invariant at start of arbitrary iteration
                let inv_head = expr_to_smt(invariant, &loop_env, tcx, smt);
                smt.push_str(&format!("(assert {})\n", inv_head));

                // Check: Maintenance
                let c_smt = expr_to_smt(cond, &loop_env, tcx, smt);
                let mut body_smt = smt.clone(); // Branching the state for the body check
                body_smt.push_str(&format!("(assert {})\n", c_smt));

                // Recursively process body to get final state for maintenance check
                let body_env = process_block(body, loop_env.clone(), &mut body_smt, tcx, vcs);
                let inv_post = expr_to_smt(invariant, &body_env, tcx, &mut body_smt);

                let maintenance_check =
                    format!("{}\n(assert (not {}))\n(check-sat)", body_smt, inv_post);
                vcs.push(maintenance_check);

                // Exit: After loop, we only know (Inv AND (NOT Cond))
                let c_exit = expr_to_smt(cond, &loop_env, tcx, smt);
                smt.push_str(&format!("(assert (not {}))\n", c_exit));

                env = loop_env;
            }
            Stmt::ArrayUpdate {
                target_id,
                index,
                value,
                ..
            } => {
                let id = target_id.expect("Missing ID");
                let old_name = env.name(id, tcx);
                let idx_smt = expr_to_smt(index, &env, tcx, smt);
                let val_smt = expr_to_smt(value, &env, tcx, smt);

                // 1. Safety Check: Array Bounds
                let var_base_name = tcx.get_name(&id);
                let len_name = format!("{}_length", var_base_name);

                // Create a standalone VC for this specific bounds check
                let bounds_check = format!(
                    "{smt}\n(assert (not (and (>= {idx} 0) (< {idx} {len}))))\n(check-sat)",
                    smt = smt,
                    idx = idx_smt,
                    len = len_name
                );
                vcs.push(bounds_check);

                // 2. Update the state (SSA)
                let (next_env, ver) = env.assign(id);
                let new_name = format!("{}_{}", tcx.get_name(&id), ver);
                let ty_smt = type_to_smt(env.var_types.get(&id).unwrap());

                smt.push_str(&format!("(declare-const {} {})\n", new_name, ty_smt));
                smt.push_str(&format!(
                    "(assert (= {} (store {} {} {})))\n",
                    new_name, old_name, idx_smt, val_smt
                ));

                env = next_env;
            }
        }
    }

    env
}

pub fn compile(func: &FnDecl, tcx: &TyCtx) -> Vec<String> {
    let mut smt = String::from("(set-logic ALL)\n");
    let mut vcs = Vec::new();
    let mut env = Env::new();

    // Register all types from Type Context
    for (id, ty) in &tcx.node_types {
        env.register_var(*id, ty.clone());
    }

    // 1. Setup Parameters
    for (param_id, _) in &func.params {
        let (next_env, ver) = env.assign(*param_id);
        env = next_env;

        let var_name = tcx.get_name(param_id);
        let name = format!("{}_{}", var_name, ver);
        let ty_obj = env.var_types.get(param_id).unwrap();

        smt.push_str(&format!(
            "(declare-const {} {})\n",
            name,
            type_to_smt(ty_obj)
        ));

        if matches!(ty_obj, Type::Nat) {
            smt.push_str(&format!("(assert (>= {} 0))\n", name));
        }
        if let Type::Array(size, _) = ty_obj {
            smt.push_str(&format!("(declare-const {}_length Int)\n", var_name));
            smt.push_str(&format!("(assert (= {}_length {}))\n", var_name, size));
        }
    }

    // 2. Add Preconditions (Assumptions)
    for req in &func.requires {
        let req_smt = expr_to_smt(req, &env, tcx, &mut smt);
        smt.push_str(&format!("(assert {})\n", req_smt));
    }

    // 3. Process Body
    let final_env = process_block(&func.body, env, &mut smt, tcx, &mut vcs);

    // 4. Add Postconditions as Checks
    for ens in &func.ensures {
        let post_smt = expr_to_smt(ens, &final_env, tcx, &mut smt);
        // A postcondition is just another safety check at the very end
        let check = format!("{}\n(assert (not {}))\n(check-sat)", smt, post_smt);
        vcs.push(check);
    }

    vcs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::errors::{Span, Spanned};
    use crate::runner::verify_with_z3;

    fn var(name: &str, id: u32) -> SExpr {
        Spanned::dummy(Expr::Var(name.to_string(), Some(NodeId(id))))
    }

    fn old(name: &str, id: u32) -> SExpr {
        Spanned::dummy(Expr::Old(name.to_string(), Some(NodeId(id))))
    }

    fn int(n: i64) -> SExpr {
        Spanned::dummy(Expr::IntLit(n))
    }

    fn bin(l: SExpr, op: Op, r: SExpr) -> SExpr {
        Spanned::dummy(Expr::Binary(Box::new(l), op, Box::new(r)))
    }

    #[test]
    fn test_compile_abs_function_with_merge() {
        // LOGIC TO TEST:
        // func abs(x: int) {
        //    let y = x;       <-- y_1 defined here (Start Scope for IF)
        //    if x < 0 {
        //       y = 0 - x;    <-- y_2 (Then Branch)
        //    } else {
        //       y = x;        <-- y_3 (Else Branch)
        //    }
        //    // Merge happens here: y_4 = ite(..., y_2, y_3)
        // }
        // ensures y >= 0

        let mut tcx = TyCtx::new();

        let x_id = NodeId(0);
        let y_id = NodeId(1);

        // Register types in the symbol table
        tcx.define_local(x_id, "x", Type::Int);
        tcx.define_local(y_id, "y", Type::Int);

        let func = FnDecl {
            name: "abs".to_string(),
            span: Span::dummy(),
            params: vec![(x_id, Type::Int)],
            param_names: vec!["x".to_string()],
            requires: vec![],
            body: vec![
                // 1. Init y = x
                // Current x is x_1. This creates y_1 (or y_2 if y was initialized to 0)
                Spanned::dummy(Stmt::Assign {
                    target: "y".to_string(),
                    target_id: Some(y_id),
                    value: var("x", 0),
                }),
                // 2. If x < 0
                Spanned::dummy(Stmt::If {
                    cond: bin(var("x", 0), Op::Lt, int(0)),
                    then_block: vec![
                        // y = 0 - x -> creates y_2
                        Spanned::dummy(Stmt::Assign {
                            target: "y".to_string(),
                            target_id: Some(y_id),
                            value: bin(int(0), Op::Sub, var("x", 0)),
                        }),
                    ],
                    else_block: vec![
                        // y = x -> creates y_3
                        Spanned::dummy(Stmt::Assign {
                            target: "y".to_string(),
                            target_id: Some(y_id),
                            value: var("x", 0),
                        }),
                    ],
                }),
            ],
            ensures: vec![
                // y >= 0. This must point to the merged version (y_4)
                bin(var("y", 1), Op::Gte, int(0)),
            ],
        };

        let vcs = compile(&func, &tcx);
        let smt_output = vcs.join("\n---\n");
        // 1. Parameters
        // compile() calls env.assign(x), so parameter is x_1
        assert!(smt_output.contains(&"(declare-const x_1 Int)".to_string()));

        // 2. First assignment: y = x
        // env.assign(y) creates y_1
        assert!(smt_output.contains(&"(declare-const y_1 Int)".to_string()));
        assert!(smt_output.contains(&"(= y_1 x_1)".to_string()));

        // 3. Inside branches
        // "then" block calls env.assign(y) -> y_2
        assert!(smt_output.contains(&"(declare-const y_2 Int)".to_string()));
        assert!(smt_output.contains(&"(= y_2 (- 0 x_1))".to_string()));

        // "else" block calls env.assign(y) -> y_3
        assert!(smt_output.contains(&"(declare-const y_3 Int)".to_string()));
        assert!(smt_output.contains(&"(= y_3 x_1)".to_string()));

        // 4. THE PHI MERGE
        // process_block detects y changed in branches and creates a new version y_4
        assert!(smt_output.contains(&"(declare-const y_4 Int)".to_string()));
        assert!(smt_output.contains(&"(assert (= y_4 (ite (< x_1 0) y_2 y_3)))".to_string()));

        // 5. POSTCONDITION
        // The final_env has y at version 4.
        assert!(smt_output.contains(&"(assert (not (>= y_4 0)))".to_string()));
        assert!(smt_output.contains(&"(check-sat)".to_string()));
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

        let mut tcx = TyCtx::new();

        let n_id = NodeId(0);
        let i_id = NodeId(1);

        tcx.define_local(n_id, "n", Type::Int);
        tcx.define_local(i_id, "i", Type::Int);

        let func = FnDecl {
            name: "buggy_loop".to_string(),
            span: Span::dummy(),
            param_names: vec!["n".to_string()],
            params: vec![(n_id, Type::Int)],
            requires: vec![bin(var("n", 0), Op::Gt, int(0))],
            body: vec![
                Spanned::dummy(Stmt::Assign {
                    target: "i".to_string(),
                    target_id: Some(i_id),
                    value: int(0),
                }),
                Spanned::dummy(Stmt::While {
                    cond: bin(var("i", 1), Op::Lt, var("n", 0)),
                    invariant: bin(var("i", 1), Op::Gte, int(0)), // i must stay positive
                    body: vec![
                        // BUG: Decrementing i makes it negative!
                        Spanned::dummy(Stmt::Assign {
                            target: "i".to_string(),
                            target_id: Some(i_id),
                            value: bin(var("i", 1), Op::Sub, int(1)),
                        }),
                    ],
                }),
            ],
            ensures: vec![],
        };

        let result = verify_with_z3(&func, &tcx);

        // Z3 will find that if i=0 and we do i = i - 1, then i becomes -1.
        // -1 >= 0 is FALSE, so the invariant is violated.
        assert!(
            result.is_err(),
            "Verification should fail for decreasing invariant"
        );
    }

    #[test]
    fn test_compile_array_update() {
        // SCENARIO:
        // func update(arr []int) {
        //    arr[0] = 99
        //    ensures arr[0] == 99
        //    ensures arr[1] == old(arr)[1] // Frame property
        // }

        let mut tcx = TyCtx::new();
        let arr_id = NodeId(0);

        tcx.define_local(arr_id, "arr", Type::Array(99, Box::new(Type::Int)));

        let func = FnDecl {
            name: "update".to_string(),
            span: Span::dummy(),
            param_names: vec!["arr".to_string()],
            params: vec![(arr_id, Type::Array(99, Box::new(Type::Int)))],
            requires: vec![],
            body: vec![Spanned::dummy(Stmt::ArrayUpdate {
                target: "arr".to_string(),
                target_id: Some(arr_id),
                index: int(0),
                value: int(99),
            })],
            ensures: vec![
                // arr[0] == 99
                bin(bin(var("arr", 0), Op::Index, int(0)), Op::Eq, int(99)),
                // arr[1] == old(arr)[1] (Prove we didn't touch index 1)
                bin(
                    bin(var("arr", 0), Op::Index, int(1)),
                    Op::Eq,
                    bin(old("arr", 0), Op::Index, int(1)),
                ),
            ],
        };

        let vcs = compile(&func, &tcx);
        let smt = vcs.join("\n\n");

        assert!(smt.contains(&"(declare-const arr_1 (Array Int Int))".to_string()));
        assert!(smt.contains(&"(declare-const arr_2 (Array Int Int))".to_string()));
        assert!(smt.contains(&"(= arr_2 (store arr_1 0 99))".to_string()));
        assert!(smt.contains(&"(select arr_2 0)".to_string()));
    }
}
