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
        format!("{}_0", tcx.get_name(&id))
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

fn expr_to_smt(expr: &SExpr, env: &Env, tcx: &TyCtx) -> String {
    match &expr.node {
        Expr::IntLit(n) => n.to_string(),
        Expr::BoolLit(b) => b.to_string(),
        Expr::Var(_name, Some(id)) => env.name(*id, tcx),
        Expr::Old(_name, Some(id)) => env.old(*id, tcx),
        Expr::Cast(_, inner) => expr_to_smt(inner, env, tcx), // The safety check happens at the assignment level
        Expr::Binary(lhs, op, rhs) => {
            let l = expr_to_smt(lhs, env, tcx);
            let r = expr_to_smt(rhs, env, tcx);
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
        _ => unimplemented!(),
    }
}

fn get_modified_vars(stmts: &[SStmt]) -> HashSet<NodeId> {
    let mut modified = HashSet::new();
    for stmt in stmts {
        match &stmt.node {
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
        Type::Array(inner) => format!("(Array Int {})", type_to_smt(inner)),
    }
}

fn process_block(stmts: &[SStmt], env: Env, smt: &mut String, tcx: &TyCtx) -> Env {
    let mut env = env;

    for stmt in stmts {
        match &stmt.node {
            Stmt::Assign {
                target_id, value, ..
            } => {
                let id = target_id.unwrap();
                let val = expr_to_smt(value, &env, tcx);

                let (env2, ver) = env.assign(id);
                let name = format!("{}_{}", tcx.get_name(&id), ver);
                let ty = type_to_smt(env.var_types.get(&id).unwrap());

                smt.push_str(&format!("(declare-const {} {})\n", name, ty));
                smt.push_str(&format!("(assert (= {} {}))\n", name, val));

                env = env2;
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                let cond_smt = expr_to_smt(cond, &env, tcx);

                let then_env = process_block(then_block, env.clone(), smt, tcx);
                let else_env = process_block(else_block, env.clone(), smt, tcx);

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
                        // Get a truly unique new version for the merged result
                        let (next, v_phi) = merged_env.assign(id);
                        merged_env = next;

                        let name = format!("{}_{}", tcx.get_name(&id), v_phi);
                        let ty = type_to_smt(merged_env.var_types.get(&id).unwrap());

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

                return merged_env;
            }
            Stmt::While {
                cond,
                invariant,
                body,
            } => {
                // Assert Invariant holds on Entry
                // Does the invariant hold BEFORE the loop starts?
                // 1. Initial Check
                let inv_init = expr_to_smt(invariant, &env, tcx);
                smt.push_str("; Check: Invariant on Entry\n(push)\n");
                smt.push_str(&format!(
                    "(assert (not {}))\n(check-sat)\n(pop)\n",
                    inv_init
                ));

                // 2. Havoc
                let modified = get_modified_vars(body);
                let mut loop_env = env.clone();
                for id in modified {
                    let (next, ver) = loop_env.assign(id);
                    loop_env = next;
                    let ty = type_to_smt(loop_env.var_types.get(&id).unwrap());
                    smt.push_str(&format!(
                        "(declare-const {}_{} {})\n",
                        tcx.get_name(&id),
                        ver,
                        ty
                    ));
                }

                // 3. Assume Invariant and Maintenance
                let inv_head = expr_to_smt(invariant, &loop_env, tcx);
                smt.push_str(&format!("(assert {})\n", inv_head));

                smt.push_str("; Check: Maintenance\n(push)\n");
                let c_smt = expr_to_smt(cond, &loop_env, tcx);
                smt.push_str(&format!("(assert {})\n", c_smt));

                let body_env = process_block(body, loop_env.clone(), smt, tcx);
                let inv_post = expr_to_smt(invariant, &body_env, tcx);
                smt.push_str(&format!(
                    "(assert (not {}))\n(check-sat)\n(pop)\n",
                    inv_post
                ));

                // 4. Exit
                let c_exit = expr_to_smt(cond, &loop_env, tcx);
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
                let idx_smt = expr_to_smt(index, &env, tcx);
                let val_smt = expr_to_smt(value, &env, tcx);

                // Bounds Check
                let len_name = format!("{}_length", tcx.get_name(&id));
                smt.push_str("; Safety Check: Array Bounds\n(push)\n");
                smt.push_str(&format!(
                    "(assert (not (and (>= {0} 0) (< {0} {1}))))\n",
                    idx_smt, len_name
                ));
                smt.push_str("(check-sat)\n(pop)\n");

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

pub fn compile(func: &FnDecl, tcx: &TyCtx) -> String {
    let mut smt = String::from("(set-logic QF_AUFNIA)\n");
    let mut env = Env::new();

    // Pass 1: Pre-register all types from Symbol Table
    let modified = get_modified_vars(&func.body);
    let all_vars = func.params.iter().map(|(id, _)| *id).chain(modified);
    for id in all_vars {
        if let Some(ty) = tcx.get_type(&id) {
            env.register_var(id, ty.clone());
        }
    }

    // Pass 2: Declare Parameters
    for (id, ty) in &func.params {
        let (next_env, ver) = env.assign(*id);
        env = next_env;

        let name = tcx.get_name(id);
        let ssa_name = format!("{}_{}", name, ver);
        smt.push_str(&format!(
            "(declare-const {} {})\n",
            ssa_name,
            type_to_smt(ty)
        ));

        if let Type::Nat = ty {
            smt.push_str(&format!("(assert (>= {} 0))\n", ssa_name));
        }
        if let Type::Array(_) = ty {
            smt.push_str(&format!(
                "(declare-const {}_length Int)\n(assert (>= {}_length 0))\n",
                name, name
            ));
        }
    }

    // Preconditions
    let reqs = func
        .requires
        .iter()
        .map(|r| expr_to_smt(r, &env, tcx))
        .collect::<Vec<_>>();
    if !reqs.is_empty() {
        smt.push_str(&format!("(assert (and {}))\n", reqs.join(" ")));
    }

    // Body
    let final_env = process_block(&func.body, env, &mut smt, tcx);

    // Postconditions
    for ens in &func.ensures {
        let post = expr_to_smt(ens, &final_env, tcx);
        smt.push_str("\n; Check Postcondition\n(push)\n");
        smt.push_str(&format!("(assert (not {}))\n(check-sat)\n(pop)\n", post));
    }

    smt
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::errors::Spanned;
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

        let smt_output = compile(&func, &tcx);

        // 1. Parameters
        // compile() calls env.assign(x), so parameter is x_1
        assert!(smt_output.contains("(declare-const x_1 Int)"));

        // 2. First assignment: y = x
        // env.assign(y) creates y_1
        assert!(smt_output.contains("(declare-const y_1 Int)"));
        assert!(smt_output.contains("(= y_1 x_1)"));

        // 3. Inside branches
        // "then" block calls env.assign(y) -> y_2
        assert!(smt_output.contains("(declare-const y_2 Int)"));
        assert!(smt_output.contains("(= y_2 (- 0 x_1))"));

        // "else" block calls env.assign(y) -> y_3
        assert!(smt_output.contains("(declare-const y_3 Int)"));
        assert!(smt_output.contains("(= y_3 x_1)"));

        // 4. THE PHI MERGE
        // process_block detects y changed in branches and creates a new version y_4
        assert!(smt_output.contains("(declare-const y_4 Int)"));
        assert!(smt_output.contains("(assert (= y_4 (ite (< x_1 0) y_2 y_3)))"));

        // 5. POSTCONDITION
        // The final_env has y at version 4.
        assert!(smt_output.contains("(assert (not (>= y_4 0)))"));
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

        let mut tcx = TyCtx::new();

        let n_id = NodeId(0);
        let i_id = NodeId(1);

        tcx.define_local(n_id, "n", Type::Int);
        tcx.define_local(i_id, "i", Type::Int);

        let func = FnDecl {
            name: "buggy_loop".to_string(),
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

        let smt = compile(&func, &tcx);
        let result = verify_with_z3(&smt);

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

        tcx.define_local(arr_id, "arr", Type::Array(Box::new(Type::Int)));

        let func = FnDecl {
            name: "update".to_string(),
            param_names: vec!["arr".to_string()],
            params: vec![(arr_id, Type::Array(Box::new(Type::Int)))],
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

        let smt = compile(&func, &tcx);
        assert!(smt.contains("(declare-const arr_1 (Array Int Int))"));
        assert!(smt.contains("(declare-const arr_2 (Array Int Int))"));
        assert!(smt.contains("(= arr_2 (store arr_1 0 99))"));
        assert!(smt.contains("(select arr_2 0)"));
    }
}
