pub mod ast;
pub mod check;
pub mod runner;
pub mod vc;

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub otter);

fn main() {
    // SOURCE CODE (Hardcoded for now, or read from args later)
    let src = r#"
        func Abs(x) {
            requires x > -100
            
            if x < 0 { 
                x = 0 - x 
            } else { 
                x = x 
            }

            ensures x >= 0
        }
    "#;

    println!("Compiling Otter program...");

    // PARSE
    let parser = otter::FnDeclParser::new();
    let parse_result = parser.parse(src);

    match parse_result {
        Ok(func_decl) => {
            println!("> Parsing: ✅");

            // BORROW CHECK
            let mut checker = check::BorrowChecker::new();
            match checker.check_fn(&func_decl) {
                Ok(_) => {
                    println!("> Borrow Checker: ✅");

                    // COMPILE TO SMT (VC GENERATION)
                    let z3_code = vc::compile(&func_decl);

                    // RUN VERIFIER
                    println!("> Verifying Logic with Z3...");
                    match runner::verify_with_z3(&z3_code) {
                        Ok(_) => {
                            println!("\n✨ SUCCESS: Program verified successfully.");
                        }
                        Err(e) => {
                            println!("\n❌ VERIFICATION FAILED.");
                            println!("Reason: {}", e);
                            std::process::exit(1);
                        }
                    }
                }

                Err(e) => {
                    println!("❌ Borrow Check Failed: {}", e);
                    std::process::exit(1);
                }
            }
        }
        Err(e) => {
            // Error handling for parser (same as before)
            println!("❌ Parse Error: {:?}", e);
            std::process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::ast::{Expr, FnDecl, Op, Stmt};
    use super::check::BorrowChecker;
    use super::otter;
    use super::runner;
    use super::vc;

    fn int(i: i64) -> Box<Expr> {
        Box::new(Expr::IntLit(i))
    }

    fn var(s: &str) -> Box<Expr> {
        Box::new(Expr::Var(s.to_string()))
    }

    fn bin(l: Box<Expr>, op: Op, r: Box<Expr>) -> Expr {
        Expr::Binary(l, op, r)
    }

    #[test]
    fn test_basic_arithmetic() {
        let parser = otter::ExprParser::new();

        let res = parser.parse("1 + 2").unwrap();
        assert_eq!(res, bin(int(1), Op::Add, int(2)));

        let res = parser.parse("x == 1 + 2").unwrap();
        assert_eq!(
            res,
            bin(var("x"), Op::Eq, Box::new(bin(int(1), Op::Add, int(2))))
        );
    }

    #[test]
    fn test_arithmetic_associativity() {
        let parser = otter::ExprParser::new();

        // We use PEMDAS Logic to define arithmetic e.g 1 + (2 * 3)
        let res = parser.parse("1 + 2 * 3").unwrap();

        assert_eq!(
            res,
            bin(int(1), Op::Add, Box::new(bin(int(2), Op::Mul, int(3))))
        );
    }

    #[test]
    fn test_factor_and_atoms() {
        let parser = otter::ExprParser::new();

        assert_eq!(parser.parse("(123)").unwrap(), Expr::IntLit(123));

        // Negative numbers (unary minus)
        // "-5" parses as "0 - 5" based on your grammar rule: "-" <f:Factor> => 0 - f
        assert_eq!(parser.parse("-5").unwrap(), bin(int(0), Op::Sub, int(5)));

        assert_eq!(
            parser.parse("old(balance)").unwrap(),
            Expr::Old("balance".to_string())
        );
    }

    #[test]
    fn test_statements() {
        let parser = otter::StmtParser::new();

        // Assignment
        let assign = parser.parse("x = 100").unwrap();
        match assign {
            Stmt::Assign { target, value } => {
                assert_eq!(target, "x");
                assert_eq!(value, Expr::IntLit(100));
            }
            _ => panic!("Expected Assign"),
        }

        // If-Else
        let if_stmt = parser.parse("if x > 0 { y = 1 } else { y = 2 }").unwrap();
        match if_stmt {
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                assert!(matches!(cond, Expr::Binary(..)));
                assert_eq!(then_block.len(), 1);
                assert_eq!(else_block.len(), 1);
            }
            _ => panic!("Expected If"),
        }

        // If without Else (should have empty else_block)
        let if_only = parser.parse("if x > 0 { y = 1 }").unwrap();
        match if_only {
            Stmt::If { else_block, .. } => {
                assert!(else_block.is_empty());
            }
            _ => panic!("Expected If"),
        }
    }

    #[test]
    fn test_function_decl() {
        let parser = otter::FnDeclParser::new();

        let code = r#"
            func transfer(from, to, amount) {
                requires amount > 0
                requires from > amount
                
                from = from - amount
                to = to + amount

                ensures to > old(to)
            }
        "#;

        let func = parser.parse(code).unwrap();

        assert_eq!(func.name, "transfer");
        assert_eq!(func.params, vec!["from", "to", "amount"]);
        assert_eq!(func.requires.len(), 2); // Two requires statements
        assert_eq!(func.body.len(), 2); // Two assignments
        assert_eq!(func.ensures.len(), 1); // One ensures statement
    }

    #[test]
    fn test_vacuous_truth() {
        // func Vacuous(x) {
        //     requires x > 10
        //     requires x < 5  <-- Impossible!
        //     x = 99999
        //     ensures x == 0  <-- Should pass because premises are false
        // }
        let func = FnDecl {
            name: "Vacuous".to_string(),
            params: vec!["x".to_string()],
            requires: vec![
                bin(var("x"), Op::Gt, int(10)),
                bin(var("x"), Op::Lt, int(5)),
            ],
            body: vec![Stmt::Assign {
                target: "x".to_string(),
                value: Expr::IntLit(99999),
            }],
            ensures: vec![bin(var("x"), Op::Eq, int(0))],
        };

        // This must PASS Z3
        let smt = vc::compile(&func);
        let result = runner::verify_with_z3(&smt);
        assert!(
            result.is_ok(),
            "Vacuous truth failed: Impossible preconditions should verify anything."
        );
    }

    #[test]
    fn test_uninitialized_merge_scope() {
        // func BrokenScope(c) {
        //     if c > 0 {
        //         y = 50
        //     } else {
        //         // y NOT defined
        //     }
        //     z = y + 1 <-- ERROR: y is undefined
        // }
        let func = FnDecl {
            name: "BrokenScope".to_string(),
            params: vec!["c".to_string()],
            requires: vec![],
            ensures: vec![],
            body: vec![
                Stmt::If {
                    cond: bin(var("c"), Op::Gt, int(0)),
                    then_block: vec![Stmt::Assign {
                        target: "y".to_string(),
                        value: Expr::IntLit(50),
                    }],
                    else_block: vec![
                        // Empty else
                    ],
                },
                Stmt::Assign {
                    target: "z".to_string(),
                    value: bin(var("y"), Op::Add, int(1)),
                },
            ],
        };

        // This must FAIL the BORROW CHECKER (not Z3)
        let mut checker = BorrowChecker::new();
        let result = checker.check_fn(&func);

        assert!(
            result.is_err(),
            "Borrow checker failed to catch uninitialized merge."
        );
        assert!(result.unwrap_err().contains("Borrow Error"));
    }

    #[test]
    fn test_nested_ssa_logic() {
        // func Nested(x) {
        //    if true {
        //       if true { x = 1 } else { x = 2 }
        //    } else {
        //       x = 3
        //    }
        //    ensures x == 1
        // }
        let func = FnDecl {
            name: "Nested".to_string(),
            params: vec!["x".to_string()],
            requires: vec![],
            body: vec![Stmt::If {
                cond: Expr::BoolLit(true),
                then_block: vec![Stmt::If {
                    cond: Expr::BoolLit(true),
                    then_block: vec![Stmt::Assign {
                        target: "x".to_string(),
                        value: Expr::IntLit(1),
                    }],
                    else_block: vec![Stmt::Assign {
                        target: "x".to_string(),
                        value: Expr::IntLit(2),
                    }],
                }],
                else_block: vec![Stmt::Assign {
                    target: "x".to_string(),
                    value: Expr::IntLit(3),
                }],
            }],
            ensures: vec![bin(var("x"), Op::Eq, int(1))],
        };

        let smt = vc::compile(&func);
        let result = runner::verify_with_z3(&smt);
        assert!(result.is_ok(), "Nested IF logic failed verification.");
    }

    #[test]
    fn test_integer_division_math() {
        // func Math(x) {
        //    requires x > 0
        //    y = x * x
        //    z = y / x
        //    ensures z == x
        // }
        // Note: In SMT-LIB (div x y) is Euclidean division.
        // For positive numbers, this identity should hold.
        let func = FnDecl {
            name: "Math".to_string(),
            params: vec!["x".to_string()],
            requires: vec![bin(var("x"), Op::Gt, int(0))],
            body: vec![
                Stmt::Assign {
                    target: "y".to_string(),
                    value: bin(var("x"), Op::Mul, var("x")),
                },
                Stmt::Assign {
                    target: "z".to_string(),
                    value: bin(var("y"), Op::Div, var("x")),
                },
            ],
            ensures: vec![bin(var("z"), Op::Eq, var("x"))],
        };

        let smt = vc::compile(&func);
        let result = runner::verify_with_z3(&smt);
        assert!(result.is_ok(), "Integer division logic failed.");
    }

    #[test]
    fn test_bad_loop_entry() {
        // func BadLoop(x) {
        //    x = 0
        //    // Invariant: x > 10.
        //    // This fails immediately on entry because x is 0!
        //    while x < 100 invariant x > 10 {
        //       x = x + 1
        //    }
        // }
        let func = FnDecl {
            name: "BadLoop".to_string(),
            params: vec!["x".to_string()],
            requires: vec![],
            ensures: vec![],
            body: vec![
                Stmt::Assign {
                    target: "x".to_string(),
                    value: Expr::IntLit(0),
                },
                Stmt::While {
                    cond: bin(var("x"), Op::Lt, int(100)),
                    invariant: bin(var("x"), Op::Gt, int(10)), // 0 > 10 is False
                    body: vec![Stmt::Assign {
                        target: "x".to_string(),
                        value: bin(var("x"), Op::Add, int(1)),
                    }],
                },
            ],
        };

        let smt = vc::compile(&func);
        let result = runner::verify_with_z3(&smt);

        // We EXPECT this to fail.
        assert!(
            result.is_err(),
            "Verifier failed to catch invalid Loop Entry invariant"
        );
    }
}
