// Copyright 2026 Andrew Yates.
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
// QF_LIA direct enumeration regression tests (#1911).

use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;

fn run_z4_with_timeout(smt_file: &str, timeout_ms: u32) -> String {
    run_z4_impl(smt_file, timeout_ms, true)
}

/// Like `run_z4_with_timeout` but allows non-zero exit (e.g. solver timeout).
fn run_z4_with_timeout_allow_unknown(smt_file: &str, timeout_ms: u32) -> String {
    run_z4_impl(smt_file, timeout_ms, false)
}

fn run_z4_impl(smt_file: &str, timeout_ms: u32, require_success: bool) -> String {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    // Benchmarks are at workspace root, not in crate directory.
    // CARGO_MANIFEST_DIR is crates/z4, so go up two levels to workspace root.
    let workspace_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let benchmark_path = workspace_root.join("benchmarks/smt/QF_LIA").join(smt_file);
    assert!(
        benchmark_path.is_file(),
        "Missing benchmark: {}",
        benchmark_path.display()
    );

    let output = Command::new(z4_path)
        .arg(format!("-t:{timeout_ms}"))
        .arg(benchmark_path.as_os_str())
        .output()
        .expect("Failed to spawn z4");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();

    if require_success {
        assert!(
            output.status.success(),
            "z4 exited with {:?}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            stdout,
            stderr
        );
    }

    // Normalize the output - take just the first word (sat, unsat, unknown)
    stdout.trim().lines().next().unwrap_or("").to_string()
}

fn run_z4(smt_file: &str) -> String {
    run_z4_with_timeout(smt_file, 5000)
}

/// Test system_05.smt2 - a 4-variable system with 3 equalities and 5 inequalities.
///
/// This benchmark triggered a severe regression (#1911) where Z4 was 44x slower
/// than Z3 because direct enumeration found multiple solutions but refused to
/// return SAT, instead falling back to expensive branch-and-bound.
///
/// The fix: When enumeration finds ANY satisfying integer solution, return it
/// as a SAT witness immediately instead of requiring the solution be unique.
#[test]
#[timeout(30_000)]
fn test_system_05_sat() {
    let result = run_z4("system_05.smt2");
    assert_eq!(result, "sat", "system_05.smt2 should be sat, got: {result}");
}

/// Test linear_00.smt2 - a 2-variable bounded linear Diophantine equation.
///
/// This is the simplest case: 4x + 3y = 70 with 0 <= x <= 41, y >= 0.
/// Should be solved instantly via direct enumeration.
#[test]
#[timeout(30_000)]
fn test_linear_00_sat() {
    let result = run_z4("linear_00.smt2");
    assert_eq!(result, "sat", "linear_00.smt2 should be sat, got: {result}");
}

/// Test system_11.smt2 - soundness regression (#2647).
///
/// Z3 returns SAT with verified model (v0=145, v1=-8, v2=69, v3=21).
/// Z4 previously generated invalid Gomory cuts from rows that were not in a
/// valid non-basic-at-bounds form, which could cut off real integer solutions
/// and lead to a spurious UNSAT result.
#[test]
#[timeout(30_000)]
fn test_system_11_sat() {
    let result = run_z4("system_11.smt2");
    assert_eq!(result, "sat", "system_11.smt2 should be sat, got: {result}");
}

/// Test false_unsat_20var_bb.smt2 - soundness regression (#2760).
///
/// Z4 must never return UNSAT on this benchmark. A bad Gomory row filter
/// change incorrectly treated all non-basic variables as integer in
/// integer_mode and generated invalid cuts that removed real SAT models.
/// In debug-mode tests the solver may still return UNKNOWN under limits, so
/// this regression guards the soundness property directly.
#[test]
#[timeout(45_000)]
fn test_false_unsat_20var_bb_sat() {
    let result = run_z4_with_timeout_allow_unknown("false_unsat_20var_bb.smt2", 30_000);
    assert_ne!(
        result, "unsat",
        "false_unsat_20var_bb.smt2 must not be unsat; got: {result}",
    );
}
