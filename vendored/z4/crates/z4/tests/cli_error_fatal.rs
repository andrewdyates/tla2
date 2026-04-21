// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

struct CleanupGuard(std::path::PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn write_temp_smt2(contents: &str) -> (std::path::PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "z4_cli_error_fatal_{}_{}.smt2",
        std::process::id(),
        file_id
    ));
    std::fs::write(&path, contents).unwrap();
    (path.clone(), CleanupGuard(path))
}

#[test]
#[timeout(60000)]
fn test_cli_executor_error_fatal_in_file_mode() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let input = r#"(set-logic QF_LIA)
(get-value (x))
(check-sat)
"#;

    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(z4_path)
        .arg(&temp_path)
        .output()
        .expect("Failed to spawn z4");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    eprintln!("Z4 stdout: {stdout:?}");
    eprintln!("Z4 stderr: {stderr:?}");
    eprintln!("Z4 exit: {:?}", output.status);

    assert!(
        !output.status.success(),
        "Expected non-zero exit status, got {:?}",
        output.status
    );
    assert!(
        stdout.trim().is_empty(),
        "Expected empty stdout, got: {stdout}"
    );
    assert!(
        stderr.contains("(error"),
        "Expected SMT-LIB error on stderr, got: {stderr}"
    );
}

#[test]
#[timeout(60000)]
fn test_cli_executor_error_fatal_on_piped_stdin() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let input = r#"(set-logic QF_LIA)
(get-value (x))
(check-sat)
"#;

    let mut child = Command::new(z4_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn z4");

    {
        use std::io::Write;
        let stdin = child.stdin.as_mut().unwrap();
        stdin.write_all(input.as_bytes()).unwrap();
    }

    let output = child.wait_with_output().expect("Failed to wait on z4");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    eprintln!("Z4 stdin stdout: {stdout:?}");
    eprintln!("Z4 stdin stderr: {stderr:?}");
    eprintln!("Z4 stdin exit: {:?}", output.status);

    assert!(
        !output.status.success(),
        "Expected non-zero exit status, got {:?}",
        output.status
    );
    assert!(
        stdout.trim().is_empty(),
        "Expected empty stdout, got: {stdout}"
    );
    assert!(
        stderr.contains("(error"),
        "Expected SMT-LIB error on stderr, got: {stderr}"
    );
}

#[test]
#[timeout(60000)]
fn test_cli_accepts_quantified_bv_logic() {
    // BV logic (quantified bitvectors) is routed to QF_BV solver since 8d790229a.
    // This formula is a tautology (bvadd commutativity), so sat is correct.
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let input = r#"(set-logic BV)
(declare-fun x () (_ BitVec 8))
(assert (forall ((y (_ BitVec 8))) (= (bvadd x y) (bvadd y x))))
(check-sat)
"#;

    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(z4_path)
        .arg(&temp_path)
        .output()
        .expect("Failed to spawn z4");

    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );
    let result = stdout.trim();
    assert!(
        result == "sat" || result == "unknown",
        "Expected sat or unknown for quantified BV tautology, got: {result}"
    );
}

#[test]
#[timeout(60000)]
fn test_cli_reports_bvadd_arity_error() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let input = r#"(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= (bvadd x) #x01))
(check-sat)
"#;

    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(z4_path)
        .arg(&temp_path)
        .output()
        .expect("Failed to spawn z4");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        !output.status.success(),
        "Expected non-zero exit status, got {:?}",
        output.status
    );
    assert!(
        stdout.trim().is_empty(),
        "Expected empty stdout, got: {stdout}"
    );
    assert!(
        stderr.contains("elaboration error: invalid constant: bvadd requires at least 2 arguments"),
        "Expected bvadd arity error, got: {stderr}"
    );
}
