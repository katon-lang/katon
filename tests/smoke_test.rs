#[cfg(test)]
mod tests {
    use katon::ast::FnDecl;
    use katon::check::BorrowChecker;
    use katon::errors::{Diagnostic, Spanned};
    use katon::katon::FnDeclParser;
    use katon::runner::verify_with_z3;
    use katon::symbol_table::{Resolver, TyCtx};
    use katon::typecheck::TypeChecker;
    use katon::vc::compile;
    use std::fs;
    use std::path::Path;

    fn run_smoke_test(file_path: &Path) -> Result<(), String> {
        let source =
            fs::read_to_string(file_path).map_err(|e| format!("Failed to read the file {}", e))?;

        let parser = FnDeclParser::new();

        let mut fn_decl: Spanned<FnDecl> = parser
            .parse(&source)
            .map_err(|e| format!("Parser error: {}", e))?;

        let mut tcx = TyCtx::new();
        let mut resolver = Resolver::new();

        // Resolve names
        resolver
            .resolve_function(&mut fn_decl.node, &mut tcx)
            .map_err(|e| format!("Resolution Error: {:?}", e.error))?;

        // Run Type Checker
        // Note: New takes &mut tcx, check_fn takes ONLY &fn_decl
        let mut type_checker = TypeChecker::new(&mut tcx);
        type_checker
            .check_fn(&fn_decl.node)
            .map_err(|e| format!("Type Error: {:?}", e.error))?;

        // Run Borrow Checker
        // Note: New takes nothing, check_fn takes BOTH &fn_decl and &mut tcx
        let mut bc = BorrowChecker::new();
        bc.check_fn(&fn_decl.node, &mut tcx)
            .map_err(|e| format!("Borrow Error: {:?}", e.error))?;

        // Generate SMT
        let _smt_code = compile(&fn_decl.node, &tcx);

        // When calling the verifier, pass the node inside
        match verify_with_z3(&fn_decl.node, &tcx) {
            Ok(_) => Ok(()),
            Err(e) => {
                let diag = Diagnostic {
                    error: e,
                    span: fn_decl.span,
                };
                diag.emit(&source);
                Err("Verification failed".to_string())
            }
        }
    }

    #[test]
    fn test_all_suites() {
        let suites = [
            ("tests/success", true),
            ("tests/fail_borrow", false),
            ("tests/fail_logic", false),
        ];

        for (dir, should_pass) in suites {
            let paths = fs::read_dir(dir).expect("Failed to read test directory");
            for path in paths {
                let path = path.unwrap().path();
                if path.extension().and_then(|s| s.to_str()) == Some("ktn") {
                    let result = run_smoke_test(&path);

                    match (result, should_pass) {
                        (Ok(_), true) => println!("PASS: {:?}", path),
                        (Err(_), false) => println!("CORRECTLY FAILED: {:?}", path),
                        (Ok(_), false) => panic!("Test {:?} passed but was expected to FAIL", path),
                        (Err(e), true) => {
                            panic!("Test {:?} failed but was expected to PASS: {}", path, e)
                        }
                    }
                }
            }
        }
    }
}
