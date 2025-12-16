use std::io::Write;
use std::process::{Command, Stdio};

pub fn verify_with_z3(smt_code: &str) -> Result<(), String> {
    let mut child = Command::new("z3")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|_| "Could not find 'z3' binary")?;

    child
        .stdin
        .as_mut()
        .ok_or("Failed to open stdin")?
        .write_all(smt_code.as_bytes())
        .map_err(|e| e.to_string())?;

    let output = child.wait_with_output().map_err(|e| e.to_string())?;
    let stdout = String::from_utf8_lossy(&output.stdout);

    // Check process exit code
    if !output.status.success() {
        return Err(format!("Z3 crashed or failed: {}", stdout));
    }

    let mut verification_count = 0;

    for line in stdout.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }

        if trimmed == "sat" {
            return Err("Verification Failed: Counter-example found".to_string());
        } else if trimmed == "unsat" {
            verification_count += 1;
        } else if trimmed.starts_with("(error") {
            return Err(format!("Z3 Error: {}", trimmed));
        }
    }

    // Ensure we actually ran something
    if verification_count == 0 {
        return Err("Z3 produced no output (empty SMT?)".to_string());
    }

    Ok(())
}
