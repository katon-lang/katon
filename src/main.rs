pub mod ast;
pub mod check;
pub mod vc;

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub otter);

fn main() {
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

    let parser = otter::FnDeclParser::new();
    let parse_result = parser.parse(src);

    match parse_result {
        Ok(func_decl) => {
            println!("Parsed '{}' successfully.", func_decl.name);

            // 3. BORROW CHECK IT
            let mut checker = check::BorrowChecker::new();
            match checker.check_fn(&func_decl) {
                Ok(_) => {
                    println!("Borrow Checker Passed.");

                    let z3_code = vc::compile(&func_decl);
                    println!("\n--- Z3 SMT OUTPUT ---\n");
                    println!("{}", z3_code);
                }

                Err(e) => println!("❌ Borrow Check Failed: {}", e),
            }
        }
        Err(e) => {
            use lalrpop_util::ParseError;

            // Map the error to a simple (start, message) tuple
            // We underscore variables we don't use (like `_expected`) to silence warnings
            let (span, message) = match &e {
                ParseError::InvalidToken { location } => {
                    (*location..*location + 1, "Invalid token found here")
                }
                ParseError::UnrecognizedEof {
                    location,
                    expected: _,
                } => (*location..*location, "Unexpected end of file."),
                ParseError::UnrecognizedToken { token, expected: _ } => {
                    let (start, _, end) = token;
                    (*start..*end, "Unrecognized token")
                }
                ParseError::ExtraToken { token } => {
                    let (start, _, end) = token;
                    (*start..*end, "Extra token found")
                }
                ParseError::User { error: _ } => (0..0, "User error"),
            };

            // Simple error printing using ariadne logic (simplified here for standard output)
            println!("Error: {} at {:?}", message, span);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::otter;
    use super::ast::{Expr, Op, Stmt};

    fn int(i: i64) -> Box<Expr> { Box::new(Expr::IntLit(i)) }
    fn var(s: &str) -> Box<Expr> { Box::new(Expr::Var(s.to_string())) }
    fn bin(l: Box<Expr>, op: Op, r: Box<Expr>) -> Expr { Expr::Binary(l, op, r) }

    #[test]
    fn test_basic_arithmetic() {
        let parser = otter::ExprParser::new();

        let res = parser.parse("1 + 2").unwrap();
        assert_eq!(res, bin(int(1), Op::Add, int(2)));

        let res = parser.parse("x == 1 + 2").unwrap();
        assert_eq!(res, bin(
            var("x"), 
            Op::Eq, 
            Box::new(bin(int(1), Op::Add, int(2)))
        ));
    }

    #[test]
    fn test_arithmetic_associativity() {
        let parser = otter::ExprParser::new();

        // In `Term` grammar we handles +, -, *, / in the same tier
        // This results in Left-Associativity for all of them. 
        // "1 + 2 * 3" parses as "(1 + 2) * 3", NOT "1 + (2 * 3)".
        let res = parser.parse("1 + 2 * 3").unwrap();

        assert_eq!(res, bin(
            Box::new(bin(int(1), Op::Add, int(2))), // (1+2) happens first
            Op::Mul, 
            int(3)
        ));
    }

    #[test]
    fn test_factor_and_atoms() {
        let parser = otter::ExprParser::new();

        assert_eq!(parser.parse("(123)").unwrap(), Expr::IntLit(123));

        // Negative numbers (unary minus)
        // "-5" parses as "0 - 5" based on your grammar rule: "-" <f:Factor> => 0 - f
        assert_eq!(parser.parse("-5").unwrap(), bin(int(0), Op::Sub, int(5)));

        assert_eq!(parser.parse("old(balance)").unwrap(), Expr::Old("balance".to_string()));
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
            },
            _ => panic!("Expected Assign"),
        }

        // If-Else
        let if_stmt = parser.parse("if x > 0 { y = 1 } else { y = 2 }").unwrap();
        match if_stmt {
            Stmt::If { cond, then_block, else_block } => {
                assert!(matches!(cond, Expr::Binary(..)));
                assert_eq!(then_block.len(), 1);
                assert_eq!(else_block.len(), 1);
            },
            _ => panic!("Expected If"),
        }
        
        // If without Else (should have empty else_block)
        let if_only = parser.parse("if x > 0 { y = 1 }").unwrap();
        match if_only {
            Stmt::If { else_block, .. } => {
                assert!(else_block.is_empty());
            },
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
        assert_eq!(func.body.len(), 2);     // Two assignments
        assert_eq!(func.ensures.len(), 1);  // One ensures statement
    }
}