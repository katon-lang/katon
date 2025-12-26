use crate::ast::FnDecl;
use crate::errors::{CheckError, VerificationError};
use crate::symbol_table::TyCtx;
use crate::vc::compile;
use z3::*;

pub fn verify_with_z3(func: &FnDecl, tcx: &TyCtx) -> Result<(), CheckError> {
    let solver = Solver::new();

    let vcs = compile(func, tcx);

    for (i, vc_text) in vcs.iter().enumerate() {
        // Debug:
        // println!("--- VC {} ---\n{}", i, vc_text);

        solver.push(); // Use solver stack or reset for clean state
        solver.from_string(vc_text.as_str());

        match solver.check() {
            SatResult::Sat => {
                let model = solver.get_model().unwrap();
                return Err(CheckError::VerificationError {
                    kind: VerificationError::AssertionMayFail {
                        details: format!("Counter-example for Check #{}:\n{}", i, model),
                    },
                });
            }
            SatResult::Unknown => {
                return Err(CheckError::InternalError("Z3 returned Unknown".to_string()));
            }
            SatResult::Unsat => {
                solver.pop(1);
            }
        }
    }

    Ok(())
}
