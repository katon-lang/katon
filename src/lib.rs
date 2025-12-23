pub mod ast;
pub mod check;
pub mod errors;
pub mod runner;
pub mod symbol_table;
pub mod typecheck;
pub mod vc;
use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub katon);

#[cfg(test)]
mod tests {
    use super::ast::{Expr, FnDecl, NodeId, Op, SExpr, Stmt, Type};
    use super::check::BorrowChecker;
    use super::errors::{CheckError, Span, Spanned};
    use super::katon;
    use super::runner;
    use super::symbol_table::TyCtx;
    use super::vc;

    fn var(name: &str, id: Option<u32>) -> SExpr {
        Spanned::dummy(Expr::Var(name.to_string(), id.map(NodeId)))
    }

    fn int(n: i64) -> SExpr {
        Spanned::dummy(Expr::IntLit(n))
    }

    fn bool_lit(b: bool) -> SExpr {
        Spanned::dummy(Expr::BoolLit(b))
    }

    fn bin(l: SExpr, op: Op, r: SExpr) -> SExpr {
        Spanned::dummy(Expr::Binary(Box::new(l), op, Box::new(r)))
    }

    fn remove_spans(expr: &mut SExpr) {
        // 1. Zero out the current span
        expr.span = Span::dummy();

        // 2. Recurse into children
        match &mut expr.node {
            Expr::Binary(lhs, _, rhs) => {
                remove_spans(lhs); // Deref Box and recurse
                remove_spans(rhs);
            }
            Expr::Cast(_, inner) => {
                remove_spans(inner);
            }
            // Leaf nodes (IntLit, Var, etc.) have no children to clean
            _ => {}
        }
    }

    #[test]
    fn test_basic_arithmetic() {
        let parser = katon::ExprParser::new();

        // Test 1: "1 + 2"
        let mut res = parser.parse("1 + 2").unwrap();
        remove_spans(&mut res); // <--- Normalize the spans
        assert_eq!(res, bin(int(1), Op::Add, int(2)));

        // Test 2: "x == 1 + 2"
        let mut res = parser.parse("x == 1 + 2").unwrap();
        remove_spans(&mut res); // <--- Normalize the spans
        assert_eq!(
            res,
            bin(var("x", None), Op::Eq, bin(int(1), Op::Add, int(2)))
        );
    }

    #[test]
    fn test_arithmetic_associativity() {
        let parser = katon::ExprParser::new();

        // We use PEMDAS Logic to define arithmetic e.g 1 + (2 * 3)
        let mut res = parser.parse("1 + 2 * 3").unwrap();
        remove_spans(&mut res);

        assert_eq!(res, bin(int(1), Op::Add, bin(int(2), Op::Mul, int(3))));
    }

    #[test]
    fn test_factor_and_atoms() {
        let parser = katon::ExprParser::new();

        // Compare only the .node
        let res = parser.parse("(123)").unwrap();
        assert_eq!(res.node, int(123).node);

        // Deep comparison will fail due to nested Spans.
        // We verify structure manually instead of using assert_eq! on the whole tree.
        let neg = parser.parse("-5").unwrap();
        match neg.node {
            Expr::Binary(lhs, op, rhs) => {
                // Check 0 - 5
                assert_eq!(lhs.node, Expr::IntLit(0)); // Check inner .node
                assert_eq!(op, Op::Sub);
                assert_eq!(rhs.node, Expr::IntLit(5)); // Check inner .node
            }
            _ => panic!("Expected Binary expression for -5, got {:?}", neg),
        }

        // Compare only the .node
        let old_res = parser.parse("old(balance)").unwrap();
        assert_eq!(old_res.node, Expr::Old("balance".to_string(), None));
    }

    #[test]
    fn test_statements() {
        let parser = katon::StmtParser::new();

        // Assignment
        let assign = parser.parse("x = 100;").unwrap();
        match assign.node {
            Stmt::Assign { target, value, .. } => {
                assert_eq!(target, "x");
                assert_eq!(value.node, int(100).node);
            }
            _ => panic!("Expected Assign"),
        }

        // If-Else
        let if_stmt = parser.parse("if x > 0 { y = 1; } else { y = 2; }").unwrap();
        match if_stmt.node {
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                assert!(matches!(
                    cond,
                    Spanned {
                        node: Expr::Binary(..),
                        ..
                    }
                ));
                assert_eq!(then_block.len(), 1);
                assert_eq!(else_block.len(), 1);
            }
            _ => panic!("Expected If"),
        }

        // If without Else (should have empty else_block)
        let if_only = parser.parse("if x > 0 { y = 1; }").unwrap();
        match if_only.node {
            Stmt::If { else_block, .. } => {
                assert!(else_block.is_empty());
            }
            _ => panic!("Expected If"),
        }
    }

    #[test]
    fn test_function_decl() {
        let parser = katon::FnDeclParser::new();

        let code = r#"
            func transfer(from: int, to: int, amount: int) {
                requires amount > 0;
                requires from > amount;
                
                from = from - amount;
                to = to + amount;

                ensures to > old(to);
            }
        "#;

        let func = parser.parse(code).unwrap();

        assert_eq!(func.name, "transfer");

        let param_types: Vec<Type> = func
            .params
            .iter()
            .map(|(_, ty): &(NodeId, Type)| ty.clone())
            .collect();

        assert_eq!(param_types, vec![Type::Int, Type::Int, Type::Int]);
        assert_eq!(func.requires.len(), 2); // Two requires statements
        assert_eq!(func.body.len(), 2); // Two assignments
        assert_eq!(func.ensures.len(), 1); // One ensures statement
    }

    #[test]
    fn test_vacuous_truth() {
        // func Vacuous(x nat) {
        //     requires x > 10
        //     requires x < 5  <-- Impossible!
        //     x = 99999
        //     ensures x == 0  <-- Should pass because premises are false
        // }

        let mut tcx = TyCtx::new();

        let x_id = NodeId(0);
        tcx.define_local(x_id, "x", Type::Nat);

        let func = FnDecl {
            name: "Vacuous".to_string(),
            param_names: vec!["x".to_string()],
            params: vec![(x_id, Type::Nat)],
            requires: vec![
                bin(var("x", Some(0)), Op::Gt, int(10)),
                bin(var("x", Some(0)), Op::Lt, int(5)),
            ],
            body: vec![Spanned::dummy(Stmt::Assign {
                target: "x".to_string(),
                target_id: Some(x_id),
                value: int(99999),
            })],
            ensures: vec![bin(var("x", Some(0)), Op::Eq, int(0))],
        };

        // This must PASS Z3
        let smt = vc::compile(&func, &tcx);
        let result = runner::verify_with_z3(&smt);
        assert!(
            result.is_ok(),
            "Vacuous truth failed: Impossible preconditions should verify anything."
        );
    }

    #[test]
    fn test_uninitialized_merge_scope() {
        // func BrokenScope(c int) {
        //     if c > 0 {
        //         let y = 50
        //     } else {
        //         // y NOT defined
        //     }
        //
        //     let z = y + 1 <-- ERROR: y is undefined
        // }

        let mut tcx = TyCtx::new();

        let c_id = NodeId(0);
        tcx.define_local(c_id, "c", Type::Int);

        let func = FnDecl {
            name: "BrokenScope".to_string(),
            params: vec![(c_id, Type::Int)],
            param_names: vec!["c".to_string()],
            requires: vec![],
            ensures: vec![],
            body: vec![
                Spanned::dummy(Stmt::If {
                    cond: bin(var("c", Some(0)), Op::Gt, int(0)),
                    then_block: vec![Spanned::dummy(Stmt::Assign {
                        target: "y".to_string(),
                        target_id: Some(NodeId(1)),
                        value: int(50),
                    })],
                    else_block: vec![
                        // Empty else
                    ],
                }),
                Spanned::dummy(Stmt::Assign {
                    target: "z".to_string(),
                    target_id: Some(NodeId(2)),
                    value: bin(var("y", Some(1)), Op::Add, int(1)),
                }),
            ],
        };

        // This must FAIL the BORROW CHECKER (not Z3)
        let mut checker = BorrowChecker::new();
        let result = checker.check_fn(&func, &mut tcx);

        assert!(
            result.is_err(),
            "Borrow checker failed to catch uninitialized merge."
        );

        let err = result.unwrap_err();
        assert_eq!(
            err.error,
            CheckError::UndefinedVariable {
                var: "y".to_string()
            }
        );
    }

    #[test]
    fn test_nested_ssa_logic() {
        // func Nested(x int) {
        //    if true {
        //       if true { x = 1 } else { x = 2 }
        //    } else {
        //       x = 3
        //    }
        //    ensures x == 1
        // }

        let mut tcx = TyCtx::new();

        let x_id = NodeId(0);
        tcx.define_local(x_id, "x", Type::Int);

        let func = FnDecl {
            name: "Nested".to_string(),
            param_names: vec!["x".to_string()],
            params: vec![(x_id, Type::Int)],
            requires: vec![],
            body: vec![Spanned::dummy(Stmt::If {
                cond: bool_lit(true),
                then_block: vec![Spanned::dummy(Stmt::If {
                    cond: bool_lit(true),
                    then_block: vec![Spanned::dummy(Stmt::Assign {
                        target: "x".to_string(),
                        target_id: Some(x_id),
                        value: int(1),
                    })],
                    else_block: vec![Spanned::dummy(Stmt::Assign {
                        target: "x".to_string(),
                        target_id: Some(x_id),
                        value: int(2),
                    })],
                })],
                else_block: vec![Spanned::dummy(Stmt::Assign {
                    target: "x".to_string(),
                    target_id: Some(x_id),
                    value: int(3),
                })],
            })],
            ensures: vec![bin(var("x", Some(0)), Op::Eq, int(1))],
        };

        let smt = vc::compile(&func, &tcx);
        let result = runner::verify_with_z3(&smt);
        assert!(result.is_ok(), "Nested IF logic failed verification.");
    }

    #[test]
    fn test_integer_division_math() {
        // func Math(x int) {
        //    requires x > 0
        //    y = x * x
        //    z = y / x
        //    ensures z == x
        // }
        // Note: In SMT-LIB (div x y) is Euclidean division.
        // For positive numbers, this identity should hold.

        let mut tcx = TyCtx::new();

        let x_id = NodeId(0);
        let y_id = NodeId(1);
        let z_id = NodeId(2);

        tcx.define_local(x_id, "x", Type::Int);
        tcx.define_local(y_id, "y", Type::Int);
        tcx.define_local(z_id, "z", Type::Int);

        let func = FnDecl {
            name: "Math".to_string(),
            param_names: vec!["x".to_string()],
            params: vec![(x_id, Type::Int)],
            requires: vec![bin(var("x", Some(0)), Op::Gt, int(0))],
            body: vec![
                Spanned::dummy(Stmt::Assign {
                    target: "y".to_string(),
                    target_id: Some(y_id),
                    value: bin(var("x", Some(0)), Op::Mul, var("x", Some(0))),
                }),
                Spanned::dummy(Stmt::Assign {
                    target: "z".to_string(),
                    target_id: Some(z_id),
                    value: bin(var("y", Some(0)), Op::Div, var("x", Some(0))),
                }),
            ],
            ensures: vec![bin(var("z", Some(0)), Op::Eq, var("x", Some(0)))],
        };

        let smt = vc::compile(&func, &tcx);

        println!("{}", smt);
        let result = runner::verify_with_z3(&smt);
        assert!(result.is_ok(), "Integer division logic failed.");
    }

    #[test]
    fn test_bad_loop_entry() {
        // func BadLoop(x int) {
        //    x = 0
        //    // Invariant: x > 10.
        //    // This fails immediately on entry because x is 0!
        //    while x < 100 invariant x > 10 {
        //       x = x + 1
        //    }
        // }
        let mut tcx = TyCtx::new();

        let x_id = NodeId(0);
        tcx.define_local(x_id, "x", Type::Int);

        let func = FnDecl {
            name: "BadLoop".to_string(),
            param_names: vec!["x".to_string()],
            params: vec![(x_id, Type::Int)],
            requires: vec![],
            ensures: vec![],
            body: vec![
                Spanned::dummy(Stmt::Assign {
                    target: "x".to_string(),
                    target_id: Some(x_id),
                    value: int(0),
                }),
                Spanned::dummy(Stmt::While {
                    cond: bin(var("x", Some(0)), Op::Lt, int(100)),
                    invariant: bin(var("x", Some(0)), Op::Gt, int(10)), // 0 > 10 is False
                    body: vec![Spanned::dummy(Stmt::Assign {
                        target: "x".to_string(),
                        target_id: Some(x_id),
                        value: bin(var("x", Some(0)), Op::Add, int(1)),
                    })],
                }),
            ],
        };

        let smt = vc::compile(&func, &tcx);
        let result = runner::verify_with_z3(&smt);

        // We EXPECT this to fail.
        assert!(
            result.is_err(),
            "Verifier failed to catch invalid Loop Entry invariant"
        );
    }
}
