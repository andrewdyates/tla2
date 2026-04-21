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

fn unique_temp_path(ext: &str) -> std::path::PathBuf {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "z4_stats_flag_output_{}_{}.{}",
        std::process::id(),
        file_id,
        ext
    ))
}

fn write_temp_smt2(contents: &str) -> (std::path::PathBuf, CleanupGuard) {
    let path = unique_temp_path("smt2");
    std::fs::write(&path, contents).expect("failed to write temp smt2");
    (path.clone(), CleanupGuard(path))
}

fn write_temp_cnf(contents: &str) -> (std::path::PathBuf, CleanupGuard) {
    let path = unique_temp_path("cnf");
    std::fs::write(&path, contents).expect("failed to write temp cnf");
    (path.clone(), CleanupGuard(path))
}

/// Assert the canonical RunStatistics envelope headers are present.
fn assert_common_stats_envelope(stderr: &str) {
    assert!(
        stderr.contains("z4.mode:"),
        "Expected z4.mode in stderr: {stderr}"
    );
    assert!(
        stderr.contains("z4.result:"),
        "Expected z4.result in stderr: {stderr}"
    );
    assert!(
        stderr.contains("z4.wall_time_ms:"),
        "Expected z4.wall_time_ms in stderr: {stderr}"
    );
}

/// Assert SAT-level counters are present in the envelope (SMT + DIMACS modes).
fn assert_sat_counters_in_envelope(stderr: &str) {
    assert!(
        stderr.contains("conflicts:"),
        "Expected conflicts counter in stderr: {stderr}"
    );
    assert!(
        stderr.contains("decisions:"),
        "Expected decisions counter in stderr: {stderr}"
    );
    assert!(
        stderr.contains("propagations:"),
        "Expected propagations counter in stderr: {stderr}"
    );
    assert!(
        stderr.contains("restarts:"),
        "Expected restarts counter in stderr: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_stats_flag_prints_statistics_after_check_sat() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let input = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 42))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(z4_path)
        .arg("--stats")
        .arg(&temp_path)
        .output()
        .expect("failed to spawn z4");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    let first_line = stdout.lines().next().unwrap_or("");
    assert_eq!(first_line, "sat", "Expected first line to be sat: {stdout}");
    // SMT-LIB statistics go to stderr (via safe_eprintln).
    assert!(
        stderr.contains(":conflicts"),
        "Expected SMT-LIB statistics in stderr: {stderr}"
    );
    assert!(
        stderr.contains(":num-assertions"),
        "Expected assertion count in stderr stats: {stderr}"
    );

    assert_common_stats_envelope(&stderr);
    assert_sat_counters_in_envelope(&stderr);
    assert!(
        !stderr.contains("dimacs-sat"),
        "SMT run should not be tagged dimacs-sat: {stderr}"
    );
    assert!(
        stderr.contains("smt.theory_conflicts:"),
        "Expected SMT theory conflicts key in stderr: {stderr}"
    );
    assert!(
        stderr.contains("smt.theory_propagations:"),
        "Expected SMT theory propagations key in stderr: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_without_stats_flag_omits_statistics_output() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let input = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 42))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(z4_path)
        .arg(&temp_path)
        .output()
        .expect("failed to spawn z4");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    let first_line = stdout.lines().next().unwrap_or("");
    assert_eq!(first_line, "sat", "Expected first line to be sat: {stdout}");
    assert!(
        !stdout.contains(":conflicts"),
        "Did not expect SMT-LIB statistics without --stats: {stdout}"
    );
    assert!(
        !stderr.contains("z4.mode:"),
        "Did not expect canonical stats envelope without --stats: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_stats_flag_prints_statistics_on_piped_stdin() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let input = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 42))
(check-sat)
"#;

    let mut child = Command::new(z4_path)
        .arg("--stats")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn z4");

    {
        use std::io::Write;
        let stdin = child.stdin.as_mut().expect("missing child stdin");
        stdin
            .write_all(input.as_bytes())
            .expect("failed to write SMT input to stdin");
    }

    let output = child.wait_with_output().expect("failed waiting for z4");
    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let first_line = stdout.lines().next().unwrap_or("");
    assert_eq!(first_line, "sat", "Expected first line to be sat: {stdout}");
    // SMT-LIB statistics go to stderr (via safe_eprintln).
    assert!(
        stderr.contains(":conflicts"),
        "Expected SMT-LIB statistics in stderr: {stderr}"
    );
    assert_common_stats_envelope(&stderr);
    assert_sat_counters_in_envelope(&stderr);
}

#[test]
#[timeout(30_000)]
fn test_cli_dimacs_stats_flag_prints_statistics_to_stderr() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let cnf = "p cnf 2 2\n1 0\n2 0\n";
    let (temp_path, _cleanup) = write_temp_cnf(cnf);

    let output = Command::new(z4_path)
        .arg("--stats")
        .arg(&temp_path)
        .output()
        .expect("failed to spawn z4");

    assert_eq!(
        output.status.code(),
        Some(10),
        "Expected SAT exit code 10, got {:?}",
        output.status
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stdout.contains("s SATISFIABLE"),
        "Expected SAT result on stdout: {stdout}"
    );
    assert_common_stats_envelope(&stderr);
    assert_sat_counters_in_envelope(&stderr);
    assert!(
        stderr.contains("dimacs-sat"),
        "Expected DIMACS mode tag in stderr: {stderr}"
    );
    assert!(
        stderr.contains("sat.learned_clauses:"),
        "Expected SAT-specific learned clauses key in stderr: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_chc_stats_flag_prints_wall_time_in_stderr() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let input = r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(z4_path)
        .arg("--chc")
        .arg("--stats")
        .arg(&temp_path)
        .output()
        .expect("failed to spawn z4");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_common_stats_envelope(&stderr);
    assert!(
        stderr.contains("portfolio"),
        "Expected portfolio mode tag for --chc in stderr: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_chc_without_stats_flag_omits_statistics_output() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let input = r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(z4_path)
        .arg("--chc")
        .arg(&temp_path)
        .output()
        .expect("failed to spawn z4");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("z4.mode:"),
        "Did not expect CHC statistics without --stats: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_portfolio_stats_flag_prints_wall_time_in_stderr() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let input = r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(z4_path)
        .arg("--portfolio")
        .arg("--stats")
        .arg(&temp_path)
        .output()
        .expect("failed to spawn z4");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_common_stats_envelope(&stderr);
    assert!(
        stderr.contains("portfolio"),
        "Expected portfolio mode tag in stderr: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_chc_stats_flag_prints_pdr_counters() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let input = r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(z4_path)
        .arg("--stats")
        .arg(&temp_path)
        .output()
        .expect("failed to spawn z4");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    // Auto-HORN detection routes to CHC solver; verify envelope has CHC mode.
    assert_common_stats_envelope(&stderr);
    assert!(
        stderr.contains("chc"),
        "Expected CHC mode tag for auto-HORN path in stderr: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_chc_stats_env_var_prints_wall_time_in_stderr() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let input = r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(z4_path)
        .arg("--chc")
        .arg(&temp_path)
        .env("Z4_STATS", "1")
        .output()
        .expect("failed to spawn z4");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_common_stats_envelope(&stderr);
    assert!(
        stderr.contains("portfolio"),
        "Expected portfolio mode tag with --chc + Z4_STATS in stderr: {stderr}"
    );
}
