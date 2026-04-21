// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use z4_drat_check::checker::DratChecker;
use z4_drat_check::cnf_parser::parse_cnf;
use z4_drat_check::drat_parser::parse_drat;
use z4_lrat_check::checker::LratChecker;
use z4_lrat_check::dimacs::parse_cnf_with_ids;
use z4_lrat_check::lrat_parser::{parse_binary_lrat, parse_text_lrat};

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn temp_path(stem: &str, extension: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "z4_cli_proof_formats_{}_{}_{}.{}",
        std::process::id(),
        stem,
        file_id,
        extension
    ));
    (path.clone(), CleanupGuard(path))
}

fn write_temp_cnf(contents: &str) -> (PathBuf, CleanupGuard) {
    let (path, cleanup) = temp_path("input", "cnf");
    std::fs::write(&path, contents).expect("write temp CNF");
    (path, cleanup)
}

fn run_unsat_cli(flag: &str, proof_path: &Path, input_path: &Path) -> Vec<u8> {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let output = Command::new(z4_path)
        .arg(flag)
        .arg(proof_path)
        .arg(input_path)
        .output()
        .expect("spawn z4");

    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT exit code 20 for {flag}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("UNSATISFIABLE"),
        "expected UNSAT output for {flag}, got {}",
        String::from_utf8_lossy(&output.stdout)
    );

    std::fs::read(proof_path).unwrap_or_else(|error| {
        panic!(
            "failed to read proof file {}: {error}",
            proof_path.display()
        )
    })
}

fn verify_drat_proof(cnf: &str, proof_bytes: &[u8]) {
    let formula = parse_cnf(cnf.as_bytes()).expect("parse CNF");
    let proof = parse_drat(proof_bytes).expect("parse DRAT");
    let mut checker = DratChecker::new(formula.num_vars, true);
    checker
        .verify(&formula.clauses, &proof)
        .expect("verify DRAT proof");
}

fn verify_lrat_text_proof(cnf: &str, proof_bytes: &[u8]) {
    let formula = parse_cnf_with_ids(cnf.as_bytes()).expect("parse CNF with IDs");
    let proof_text = std::str::from_utf8(proof_bytes).expect("LRAT text should be UTF-8");
    let proof = parse_text_lrat(proof_text).expect("parse LRAT text");
    let mut checker = LratChecker::new(formula.num_vars);
    for (id, clause) in &formula.clauses {
        assert!(
            checker.add_original(*id, clause),
            "load original clause {id}"
        );
    }
    assert!(checker.verify_proof(&proof), "verify LRAT text proof");
}

fn verify_lrat_binary_proof(cnf: &str, proof_bytes: &[u8]) {
    let formula = parse_cnf_with_ids(cnf.as_bytes()).expect("parse CNF with IDs");
    let proof = parse_binary_lrat(proof_bytes).expect("parse LRAT binary");
    let mut checker = LratChecker::new(formula.num_vars);
    for (id, clause) in &formula.clauses {
        assert!(
            checker.add_original(*id, clause),
            "load original clause {id}"
        );
    }
    assert!(checker.verify_proof(&proof), "verify LRAT binary proof");
}

#[test]
#[timeout(60_000)]
fn test_explicit_drat_flag_writes_verifiable_text_proof() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("drat_text", "proof");

    let proof_bytes = run_unsat_cli("--drat", &proof_path, &input_path);
    verify_drat_proof(cnf, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_explicit_drat_binary_flag_writes_verifiable_binary_proof() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("drat_binary", "proofbin");

    let proof_bytes = run_unsat_cli("--drat-binary", &proof_path, &input_path);
    verify_drat_proof(cnf, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_explicit_lrat_flag_writes_verifiable_text_proof() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("lrat_text", "proof");

    let proof_bytes = run_unsat_cli("--lrat", &proof_path, &input_path);
    verify_lrat_text_proof(cnf, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_explicit_lrat_binary_flag_writes_verifiable_binary_proof() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("lrat_binary", "proofbin");

    let proof_bytes = run_unsat_cli("--lrat-binary", &proof_path, &input_path);
    verify_lrat_binary_proof(cnf, &proof_bytes);
}

/// A harder UNSAT instance: pigeonhole principle PHP(3,2) — 3 pigeons, 2 holes.
/// This requires non-trivial conflict-driven clause learning to solve.
const PHP_3_2_CNF: &str = "\
p cnf 6 9\n\
1 2 0\n\
3 4 0\n\
5 6 0\n\
-1 -3 0\n\
-1 -5 0\n\
-3 -5 0\n\
-2 -4 0\n\
-2 -6 0\n\
-4 -6 0\n";

#[test]
#[timeout(60_000)]
fn test_drat_proof_on_harder_unsat_instance() {
    let (input_path, _input_cleanup) = write_temp_cnf(PHP_3_2_CNF);
    let (proof_path, _proof_cleanup) = temp_path("php32_drat", "drat");

    let proof_bytes = run_unsat_cli("--drat", &proof_path, &input_path);
    assert!(!proof_bytes.is_empty(), "DRAT proof should be non-empty for PHP(3,2)");
    verify_drat_proof(PHP_3_2_CNF, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_lrat_proof_on_harder_unsat_instance() {
    let (input_path, _input_cleanup) = write_temp_cnf(PHP_3_2_CNF);
    let (proof_path, _proof_cleanup) = temp_path("php32_lrat", "lrat");

    let proof_bytes = run_unsat_cli("--lrat", &proof_path, &input_path);
    assert!(!proof_bytes.is_empty(), "LRAT proof should be non-empty for PHP(3,2)");
    verify_lrat_text_proof(PHP_3_2_CNF, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_proof_auto_detect_drat_extension() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("autodetect", "drat");

    // Use --proof (auto-detect) with .drat extension
    let proof_bytes = run_unsat_cli("--proof", &proof_path, &input_path);
    // Should produce a valid DRAT proof
    verify_drat_proof(cnf, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_proof_auto_detect_lrat_extension() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("autodetect", "lrat");

    let proof_bytes = run_unsat_cli("--proof", &proof_path, &input_path);
    verify_lrat_text_proof(cnf, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_proof_auto_detect_lratb_extension() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("autodetect", "lratb");

    let proof_bytes = run_unsat_cli("--proof", &proof_path, &input_path);
    verify_lrat_binary_proof(cnf, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_proof_auto_detect_dratb_extension() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_path("autodetect", "dratb");

    let proof_bytes = run_unsat_cli("--proof", &proof_path, &input_path);
    verify_drat_proof(cnf, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_proof_with_stats_no_corruption() {
    let (input_path, _input_cleanup) = write_temp_cnf(PHP_3_2_CNF);
    let (proof_path, _proof_cleanup) = temp_path("stats_proof", "drat");

    let z4_path = env!("CARGO_BIN_EXE_z4");
    let output = Command::new(z4_path)
        .arg("--drat")
        .arg(&proof_path)
        .arg("--stats")
        .arg(&input_path)
        .output()
        .expect("spawn z4");

    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT exit code 20 with --stats: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("UNSATISFIABLE"),
        "expected UNSAT on stdout, got: {stdout}"
    );

    // Verify stats were printed to stderr without corrupting stdout
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("propagations:") || stderr.contains("conflicts:"),
        "expected stats on stderr, got: {stderr}"
    );

    // Verify the proof file is still valid DRAT
    let proof_bytes = std::fs::read(&proof_path).expect("read proof file");
    assert!(!proof_bytes.is_empty(), "proof file should be non-empty");
    verify_drat_proof(PHP_3_2_CNF, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_lrat_binary_proof_on_harder_unsat_instance() {
    let (input_path, _input_cleanup) = write_temp_cnf(PHP_3_2_CNF);
    let (proof_path, _proof_cleanup) = temp_path("php32_lratb", "lratb");

    let proof_bytes = run_unsat_cli("--lrat-binary", &proof_path, &input_path);
    assert!(!proof_bytes.is_empty(), "LRAT binary proof should be non-empty for PHP(3,2)");
    verify_lrat_binary_proof(PHP_3_2_CNF, &proof_bytes);
}

#[test]
#[timeout(60_000)]
fn test_explicit_flag_overrides_proof_extension_inference() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let (input_path, _input_cleanup) = write_temp_cnf(cnf);
    let (inferred_path, _inferred_cleanup) = temp_path("inferred_drat", "drat");
    let (explicit_path, _explicit_cleanup) = temp_path("explicit_lrat_binary", "proofbin");
    let z4_path = env!("CARGO_BIN_EXE_z4");

    let output = Command::new(z4_path)
        .arg("--proof")
        .arg(&inferred_path)
        .arg("--lrat-binary")
        .arg(&explicit_path)
        .arg(&input_path)
        .output()
        .expect("spawn z4");

    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT exit code 20 for precedence test: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("UNSATISFIABLE"),
        "expected UNSAT output for precedence test, got {}",
        String::from_utf8_lossy(&output.stdout)
    );

    let proof_bytes = std::fs::read(&explicit_path).unwrap_or_else(|error| {
        panic!(
            "failed to read explicit proof file {}: {error}",
            explicit_path.display()
        )
    });
    verify_lrat_binary_proof(cnf, &proof_bytes);
    assert!(
        !inferred_path.exists(),
        "expected explicit flag to override --proof path {}",
        inferred_path.display()
    );
}
