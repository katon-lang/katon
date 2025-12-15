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
