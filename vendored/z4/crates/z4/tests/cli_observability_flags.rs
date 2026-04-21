// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn temp_path(extension: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "z4_cli_observability_{}_{}.{}",
        std::process::id(),
        file_id,
        extension
    ));
    (path.clone(), CleanupGuard(path))
}

fn write_temp(contents: &str, extension: &str) -> (PathBuf, CleanupGuard) {
    let (path, cleanup) = temp_path(extension);
    std::fs::write(&path, contents).expect("write temp input");
    (path, cleanup)
}

#[test]
#[timeout(60_000)]
fn test_proof_flag_writes_alethe_for_unsat_smt() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let smt = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
"#;
    let (input_path, _input_cleanup) = write_temp(smt, "smt2");
    let (proof_path, _proof_cleanup) = temp_path("alethe");

    let output = Command::new(z4_path)
        .arg("--proof")
        .arg(&proof_path)
        .arg(&input_path)
        .output()
        .expect("spawn z4");

    assert!(
        output.status.success(),
        "z4 failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("unsat"),
        "expected unsat output, got {}",
        String::from_utf8_lossy(&output.stdout)
    );

    let proof = std::fs::read_to_string(&proof_path).expect("proof file");
    assert!(!proof.is_empty(), "expected non-empty proof file");
    assert!(proof.contains("(assume "), "expected assume steps in proof");
    assert!(proof.contains("(step "), "expected step entries in proof");
}

#[test]
#[timeout(60_000)]
fn test_proof_flag_writes_drat_for_unsat_dimacs() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp(cnf, "cnf");
    let (proof_path, _proof_cleanup) = temp_path("drat");

    let output = Command::new(z4_path)
        .arg("--proof")
        .arg(&proof_path)
        .arg(&input_path)
        .output()
        .expect("spawn z4");

    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT exit code 20: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("UNSATISFIABLE"),
        "expected UNSAT, got {}",
        String::from_utf8_lossy(&output.stdout)
    );

    let proof = std::fs::read_to_string(&proof_path).expect("proof file");
    assert!(!proof.trim().is_empty(), "expected non-empty DRAT output");
}

#[test]
#[timeout(60_000)]
fn test_proof_flag_writes_lrat_for_unsat_dimacs() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp(cnf, "cnf");
    let (proof_path, _proof_cleanup) = temp_path("lrat");

    let output = Command::new(z4_path)
        .arg("--proof")
        .arg(&proof_path)
        .arg(&input_path)
        .output()
        .expect("spawn z4");

    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT exit code 20: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("UNSATISFIABLE"),
        "expected UNSAT, got {}",
        String::from_utf8_lossy(&output.stdout)
    );

    let proof = std::fs::read_to_string(&proof_path).expect("proof file");
    assert!(!proof.trim().is_empty(), "expected non-empty LRAT output");
}

#[test]
#[timeout(60_000)]
fn test_stats_flag_includes_formula_statistics_block() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let smt = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(check-sat)
"#;
    let (input_path, _input_cleanup) = write_temp(smt, "smt2");

    let output = Command::new(z4_path)
        .arg("--stats")
        .arg(&input_path)
        .output()
        .expect("spawn z4");

    assert!(
        output.status.success(),
        "z4 failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("(:statistics"),
        "expected solver stats block, got {stderr}"
    );
    assert!(
        stderr.contains("(:formula-statistics"),
        "expected formula stats block, got {stderr}"
    );
    assert!(
        stderr.contains(":terms"),
        "expected term-count key in formula stats, got {stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn test_replay_flag_activates_production_replay() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let cnf = "p cnf 2 3\n1 0\n-1 2 0\n-2 0\n";
    let (input_path, _input_cleanup) = write_temp(cnf, "cnf");
    let (trace_path, _trace_cleanup) = temp_path("z4trace");

    let first = Command::new(z4_path)
        .arg(&input_path)
        .env("Z4_DECISION_TRACE_FILE", &trace_path)
        .output()
        .expect("spawn z4 for trace recording");
    assert_eq!(
        first.status.code(),
        Some(20),
        "trace recording: expected UNSAT exit code 20: {}",
        String::from_utf8_lossy(&first.stderr)
    );
    assert!(trace_path.exists(), "expected decision trace file");

    let replay = Command::new(z4_path)
        .arg("--replay")
        .arg(&trace_path)
        .arg(&input_path)
        .output()
        .expect("spawn z4 replay run");
    assert_eq!(
        replay.status.code(),
        Some(20),
        "replay: expected UNSAT exit code 20: {}",
        String::from_utf8_lossy(&replay.stderr)
    );
    assert!(
        String::from_utf8_lossy(&replay.stdout).contains("UNSATISFIABLE"),
        "expected UNSAT replay result, got {}",
        String::from_utf8_lossy(&replay.stdout)
    );
}
