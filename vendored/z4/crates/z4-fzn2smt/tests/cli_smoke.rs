// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Smoke tests for the fzn2smt CLI binary.
//
// These tests invoke the compiled binary via std::process::Command to verify
// basic CLI functionality: translate, info, error handling, and flag parsing.
// They do NOT test the `solve` command (requires z4 binary).

use std::path::PathBuf;
use std::process::Command;

fn fzn2smt() -> Command {
    Command::new(env!("CARGO_BIN_EXE_fzn2smt"))
}

/// Path to the FlatZinc smoke test fixtures (shared with flatzinc-smt tests).
fn fixture_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("z4-flatzinc-smt/tests/fzn-smoke")
}

fn satisfy_fzn() -> PathBuf {
    fixture_dir().join("simple_satisfy.fzn")
}

fn minimize_fzn() -> PathBuf {
    fixture_dir().join("simple_minimize.fzn")
}

// --- translate command ---

#[test]
fn test_translate_satisfy_produces_smtlib() {
    let output = fzn2smt()
        .args(["translate", satisfy_fzn().to_str().unwrap()])
        .output()
        .expect("failed to run fzn2smt");

    assert!(output.status.success(), "translate should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    // SMT-LIB2 output must contain set-logic and check-sat
    assert!(
        stdout.contains("set-logic"),
        "SMT-LIB2 output must contain set-logic, got: {stdout}"
    );
    assert!(
        stdout.contains("check-sat"),
        "SMT-LIB2 output must contain check-sat, got: {stdout}"
    );
    // Must declare the output variables x and y
    assert!(
        stdout.contains("declare-const"),
        "SMT-LIB2 output must declare variables"
    );
}

#[test]
fn test_translate_minimize_has_objective() {
    let output = fzn2smt()
        .args(["translate", minimize_fzn().to_str().unwrap()])
        .output()
        .expect("failed to run fzn2smt");

    assert!(output.status.success(), "translate should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("set-logic"),
        "SMT-LIB2 output must contain set-logic"
    );
    assert!(
        stdout.contains("check-sat"),
        "SMT-LIB2 output must contain check-sat"
    );
}

// --- info command ---

#[test]
fn test_info_satisfy_shows_statistics() {
    let output = fzn2smt()
        .args(["info", satisfy_fzn().to_str().unwrap()])
        .output()
        .expect("failed to run fzn2smt");

    assert!(output.status.success(), "info should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Variables:"),
        "info must show variable count"
    );
    assert!(
        stdout.contains("Constraints:"),
        "info must show constraint count"
    );
    assert!(
        stdout.contains("satisfy"),
        "satisfaction problem must show 'satisfy' objective"
    );
    assert!(stdout.contains("SMT-LIB2:"), "info must show SMT-LIB2 size");
}

#[test]
fn test_info_minimize_shows_objective() {
    let output = fzn2smt()
        .args(["info", minimize_fzn().to_str().unwrap()])
        .output()
        .expect("failed to run fzn2smt");

    assert!(output.status.success(), "info should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("minimize"),
        "minimization problem must show 'minimize' objective"
    );
}

// --- error handling ---

#[test]
fn test_no_args_shows_usage_and_fails() {
    let output = fzn2smt().output().expect("failed to run fzn2smt");

    assert!(!output.status.success(), "no args should fail");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Usage:"),
        "no args should show usage, got: {stderr}"
    );
}

#[test]
fn test_missing_file_fails_with_error() {
    let output = fzn2smt()
        .args(["translate", "/nonexistent/path/model.fzn"])
        .output()
        .expect("failed to run fzn2smt");

    assert!(!output.status.success(), "missing file should fail");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("failed to read") || stderr.contains("No such file"),
        "should report file read error, got: {stderr}"
    );
}

#[test]
fn test_unknown_command_fails() {
    let output = fzn2smt()
        .args(["bogus", satisfy_fzn().to_str().unwrap()])
        .output()
        .expect("failed to run fzn2smt");

    assert!(!output.status.success(), "unknown command should fail");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("unknown command"),
        "should report unknown command, got: {stderr}"
    );
}

// --- flag parsing ---

#[test]
fn test_translate_ignores_unknown_flags() {
    let output = fzn2smt()
        .args([
            "translate",
            satisfy_fzn().to_str().unwrap(),
            "--unknown-flag",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "translate should succeed even with unknown flags"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("warning: unknown flag"),
        "should warn about unknown flag, got: {stderr}"
    );
}

#[test]
fn test_free_search_flag_accepted() {
    let output = fzn2smt()
        .args(["translate", satisfy_fzn().to_str().unwrap(), "-f"])
        .output()
        .expect("failed to run fzn2smt");

    assert!(output.status.success(), "translate with -f should succeed");
}

#[test]
fn test_parallel_flag_accepted() {
    let output = fzn2smt()
        .args(["translate", satisfy_fzn().to_str().unwrap(), "-p", "4"])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "translate with -p 4 should succeed"
    );
}

#[test]
fn test_timeout_equals_syntax() {
    let output = fzn2smt()
        .args([
            "translate",
            satisfy_fzn().to_str().unwrap(),
            "--timeout=5000",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "translate with --timeout=5000 should succeed"
    );
}

#[test]
fn test_timeout_space_syntax() {
    let output = fzn2smt()
        .args([
            "translate",
            satisfy_fzn().to_str().unwrap(),
            "--timeout",
            "5000",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "translate with --timeout 5000 should succeed"
    );
}

#[test]
fn test_timeout_short_flag() {
    let output = fzn2smt()
        .args(["translate", satisfy_fzn().to_str().unwrap(), "-t", "3000"])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "translate with -t 3000 should succeed"
    );
}

#[test]
fn test_fd_search_flag_accepted() {
    let output = fzn2smt()
        .args(["translate", satisfy_fzn().to_str().unwrap(), "--fd-search"])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "translate with --fd-search should succeed"
    );
}

#[test]
fn test_all_solutions_flag_accepted() {
    let output = fzn2smt()
        .args(["translate", satisfy_fzn().to_str().unwrap(), "-a"])
        .output()
        .expect("failed to run fzn2smt");

    assert!(output.status.success(), "translate with -a should succeed");
}

#[test]
fn test_combined_minizinc_flags() {
    // MiniZinc competition typically passes: -f -a -t <timeout> -p <threads>
    let output = fzn2smt()
        .args([
            "translate",
            satisfy_fzn().to_str().unwrap(),
            "-f",
            "-a",
            "-t",
            "5000",
            "-p",
            "1",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "translate with combined MiniZinc flags should succeed"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("set-logic"),
        "output should still be valid SMT-LIB2"
    );
}

// --- output content validation ---

#[test]
fn test_translate_satisfy_declares_output_vars() {
    let output = fzn2smt()
        .args(["translate", satisfy_fzn().to_str().unwrap()])
        .output()
        .expect("failed to run fzn2smt");

    let stdout = String::from_utf8_lossy(&output.stdout);
    // simple_satisfy.fzn declares x and y as output_var
    assert!(stdout.contains("x"), "must reference variable x");
    assert!(stdout.contains("y"), "must reference variable y");
}

#[test]
fn test_info_satisfy_shows_two_variables() {
    let output = fzn2smt()
        .args(["info", satisfy_fzn().to_str().unwrap()])
        .output()
        .expect("failed to run fzn2smt");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Variables:   2"),
        "simple_satisfy has exactly 2 variables, got: {stdout}"
    );
    assert!(
        stdout.contains("Constraints: 1"),
        "simple_satisfy has exactly 1 constraint (int_ne), got: {stdout}"
    );
    assert!(
        stdout.contains("Output vars: 2"),
        "simple_satisfy has 2 output vars, got: {stdout}"
    );
}

// --- search annotation auto-activation (#331) ---

fn satisfy_with_search_fzn() -> PathBuf {
    fixture_dir().join("satisfy_with_search.fzn")
}

#[test]
fn test_info_annotated_model_shows_fd_search_capable() {
    let output = fzn2smt()
        .args(["info", satisfy_with_search_fzn().to_str().unwrap()])
        .output()
        .expect("failed to run fzn2smt");

    assert!(output.status.success(), "info should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("FD Search capable"),
        "annotated model must show 'FD Search capable', got: {stdout}"
    );
    assert!(
        stdout.contains("1 annotation"),
        "annotated model must show 1 annotation, got: {stdout}"
    );
}

#[test]
fn test_info_plain_model_shows_free_search() {
    let output = fzn2smt()
        .args(["info", satisfy_fzn().to_str().unwrap()])
        .output()
        .expect("failed to run fzn2smt");

    assert!(output.status.success(), "info should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Free Search mode"),
        "plain model must show 'Free Search mode', got: {stdout}"
    );
}

#[test]
fn test_translate_annotated_model_succeeds() {
    let output = fzn2smt()
        .args(["translate", satisfy_with_search_fzn().to_str().unwrap()])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "translate of annotated model should succeed"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("set-logic"),
        "annotated model must produce valid SMT-LIB2"
    );
}

// --- solve-cp command ---

fn cp_fixture_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fzn-cp")
}

#[test]
fn test_solve_cp_nqueens4() {
    let output = fzn2smt()
        .args([
            "solve-cp",
            cp_fixture_dir().join("nqueens4.fzn").to_str().unwrap(),
            "--timeout",
            "5000",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(output.status.success(), "solve-cp nqueens4 should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("----------"),
        "nqueens4: should print solution separator"
    );
    assert!(
        stdout.contains("=========="),
        "nqueens4: should signal completion"
    );
    assert!(stdout.contains("q1 = "), "nqueens4: should print q1");
    assert!(stdout.contains("q2 = "), "nqueens4: should print q2");
    assert!(stdout.contains("q3 = "), "nqueens4: should print q3");
    assert!(stdout.contains("q4 = "), "nqueens4: should print q4");
}

#[test]
fn test_solve_cp_nqueens4_parallel_portfolio() {
    let output = fzn2smt()
        .args([
            "solve-cp",
            cp_fixture_dir().join("nqueens4.fzn").to_str().unwrap(),
            "--timeout",
            "5000",
            "-p",
            "2",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "solve-cp nqueens4 with -p 2 should succeed"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("----------"),
        "nqueens4 parallel: should print solution separator"
    );
    assert!(
        stdout.contains("=========="),
        "nqueens4 parallel: should signal completion"
    );
}

#[test]
fn test_solve_cp_circuit3() {
    let output = fzn2smt()
        .args([
            "solve-cp",
            cp_fixture_dir().join("circuit3.fzn").to_str().unwrap(),
            "--timeout",
            "5000",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(output.status.success(), "solve-cp circuit3 should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("----------"),
        "circuit3: should have solution"
    );
    // Parse and verify Hamiltonian cycle
    let vals: Vec<i64> = (1..=3)
        .filter_map(|i| {
            stdout
                .lines()
                .find(|l| l.starts_with(&format!("x{i} = ")))
                .and_then(|l| l.trim_end_matches(';').split(" = ").nth(1))
                .and_then(|s| s.parse().ok())
        })
        .collect();
    assert_eq!(vals.len(), 3, "circuit3: should have 3 values");
    let mut sorted = vals.clone();
    sorted.sort_unstable();
    assert_eq!(
        sorted,
        vec![1, 2, 3],
        "circuit3: values should be perm of 1..3"
    );
    for (i, &v) in vals.iter().enumerate() {
        assert_ne!(v, (i + 1) as i64, "circuit3: node {} has self-loop", i + 1);
    }
}

#[test]
fn test_solve_cp_minimize_sum() {
    let output = fzn2smt()
        .args([
            "solve-cp",
            cp_fixture_dir().join("minimize_sum.fzn").to_str().unwrap(),
            "--timeout",
            "5000",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "solve-cp minimize_sum should succeed"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("=========="),
        "minimize_sum: should signal optimality"
    );
    let last_obj = stdout
        .lines()
        .rev()
        .find(|l| l.starts_with("obj = "))
        .expect("should print obj");
    assert_eq!(
        last_obj, "obj = 7;",
        "minimize_sum: optimal obj should be 7"
    );
}

#[test]
fn test_solve_cp_minimize_sum_parallel_flag_falls_back_to_single_worker() {
    let output = fzn2smt()
        .args([
            "solve-cp",
            cp_fixture_dir().join("minimize_sum.fzn").to_str().unwrap(),
            "--timeout",
            "5000",
            "-p",
            "2",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "solve-cp minimize_sum with -p 2 should succeed"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("=========="),
        "minimize_sum with -p: should still signal optimality"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("parallelizes only satisfaction models"),
        "minimize_sum with -p should explain the single-worker fallback"
    );
}

#[test]
fn test_solve_cp_element_param_array() {
    let output = fzn2smt()
        .args([
            "solve-cp",
            cp_fixture_dir().join("element.fzn").to_str().unwrap(),
            "--timeout",
            "5000",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(output.status.success(), "solve-cp element should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("index = 3;"), "element: index should be 3");
    assert!(
        stdout.contains("result = 30;"),
        "element: arr[3] should be 30 (1-indexed)"
    );
}

#[test]
fn test_solve_cp_reified_with_const() {
    let output = fzn2smt()
        .args([
            "solve-cp",
            cp_fixture_dir().join("reified.fzn").to_str().unwrap(),
            "--timeout",
            "5000",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(output.status.success(), "solve-cp reified should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("x = 2;"), "reified: x should be 2");
    assert!(
        stdout.contains("b = true;"),
        "reified: b should be true (2 <= 3)"
    );
}

#[test]
fn test_solve_cp_abs_max_min() {
    let output = fzn2smt()
        .args([
            "solve-cp",
            cp_fixture_dir().join("abs_max_min.fzn").to_str().unwrap(),
            "--timeout",
            "5000",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "solve-cp abs_max_min should succeed"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("abs_a = 3;"), "abs(-3) should be 3");
    assert!(stdout.contains("mx = 4;"), "max(2,4) should be 4");
    assert!(stdout.contains("mn = 2;"), "min(2,4) should be 2");
}

#[test]
fn test_solve_cp_bool_2arg() {
    let output = fzn2smt()
        .args([
            "solve-cp",
            cp_fixture_dir().join("bool_2arg.fzn").to_str().unwrap(),
            "--timeout",
            "5000",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(output.status.success(), "solve-cp bool_2arg should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("----------"),
        "bool_2arg: should have solution"
    );
    // bool_and(a, b) => both true
    assert!(stdout.contains("a = true;"), "bool_and: a must be true");
    assert!(stdout.contains("b = true;"), "bool_and: b must be true");
    // bool_not(c, d) => c != d; bool_or(c, d) => c OR d
    // Combined: exactly one of c,d is true
    let c_true = stdout.contains("c = true;");
    let d_true = stdout.contains("d = true;");
    assert!(
        c_true || d_true,
        "bool_or: at least one of c,d must be true"
    );
    assert!(c_true != d_true, "bool_not: c and d must differ");
    // bool_xor(e, f) => e != f
    let e_true = stdout.contains("e = true;");
    let f_true = stdout.contains("f = true;");
    assert!(e_true != f_true, "bool_xor: e and f must differ");
}

#[test]
fn test_solve_cp_nqueens8() {
    let output = fzn2smt()
        .args([
            "solve-cp",
            cp_fixture_dir().join("nqueens8.fzn").to_str().unwrap(),
            "--timeout",
            "10000",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(output.status.success(), "solve-cp nqueens8 should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("----------"),
        "nqueens8: should find a solution"
    );
    // Verify all 8 queens placed
    for i in 1..=8 {
        assert!(
            stdout.contains(&format!("q{i} = ")),
            "nqueens8: should place queen {i}"
        );
    }
}

#[test]
fn test_solve_cp_graph_color3() {
    let output = fzn2smt()
        .args([
            "solve-cp",
            cp_fixture_dir().join("graph_color3.fzn").to_str().unwrap(),
            "--timeout",
            "5000",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "solve-cp graph_color3 should succeed"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("----------"),
        "graph_color3: should be satisfiable"
    );
}

#[test]
fn test_solve_cp_knapsack_optimal() {
    let output = fzn2smt()
        .args([
            "solve-cp",
            cp_fixture_dir().join("knapsack.fzn").to_str().unwrap(),
            "--timeout",
            "10000",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(output.status.success(), "solve-cp knapsack should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("=========="),
        "knapsack: should prove optimality"
    );
    // Last solution should have obj = 14 (items 1,3,4: w=3+2+5=10, v=4+3+7=14)
    let last_obj = stdout
        .lines()
        .rev()
        .find(|l| l.starts_with("obj = "))
        .expect("should print obj");
    assert_eq!(last_obj, "obj = 14;", "knapsack: optimal obj should be 14");
}

#[test]
fn test_solve_cp_magic_square3() {
    let output = fzn2smt()
        .args([
            "solve-cp",
            cp_fixture_dir().join("magic_square3.fzn").to_str().unwrap(),
            "--timeout",
            "10000",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "solve-cp magic_square3 should succeed"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("----------"),
        "magic_square3: should find a solution"
    );
    // Parse and verify: all values 1..9 and rows/cols/diags sum to 15
    let vals: Vec<i64> = [
        "x11", "x12", "x13", "x21", "x22", "x23", "x31", "x32", "x33",
    ]
    .iter()
    .map(|name| {
        stdout
            .lines()
            .find(|l| l.starts_with(&format!("{name} = ")))
            .and_then(|l| l.trim_end_matches(';').split(" = ").nth(1))
            .and_then(|s| s.parse().ok())
            .unwrap_or_else(|| panic!("magic_square3: missing {name}"))
    })
    .collect();
    // Check rows sum to 15
    assert_eq!(vals[0] + vals[1] + vals[2], 15, "row 1 sum");
    assert_eq!(vals[3] + vals[4] + vals[5], 15, "row 2 sum");
    assert_eq!(vals[6] + vals[7] + vals[8], 15, "row 3 sum");
}

#[test]
fn test_solve_cp_sudoku_easy() {
    let output = fzn2smt()
        .args([
            "solve-cp",
            cp_fixture_dir().join("sudoku_easy.fzn").to_str().unwrap(),
            "--timeout",
            "5000",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "solve-cp sudoku_easy should succeed"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("----------"),
        "sudoku: should find a solution"
    );
    // Check given values are respected
    assert!(stdout.contains("x11 = 1;"), "sudoku: given x11=1");
    assert!(stdout.contains("x24 = 3;"), "sudoku: given x24=3");
    assert!(stdout.contains("x32 = 4;"), "sudoku: given x32=4");
    assert!(stdout.contains("x43 = 2;"), "sudoku: given x43=2");
}

#[test]
fn test_solve_cp_jobshop_optimal() {
    let output = fzn2smt()
        .args([
            "solve-cp",
            cp_fixture_dir().join("jobshop2x3.fzn").to_str().unwrap(),
            "--timeout",
            "10000",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "solve-cp jobshop2x3 should succeed"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("=========="),
        "jobshop: should prove optimality"
    );
    // Optimal makespan should be 10
    let last_makespan = stdout
        .lines()
        .rev()
        .find(|l| l.starts_with("makespan = "))
        .expect("should print makespan");
    assert_eq!(
        last_makespan, "makespan = 10;",
        "jobshop: optimal makespan should be 10"
    );
}

// --- count_eq regression test (#6119) ---

/// Regression test for #6119: count_eq with non-overlapping asymmetric ranges.
/// x1 in [5..8], x2 in [6..9], y in [1..2] — ranges don't overlap, so
/// count(xi == y) = 0 is the only valid count. The bug was a sign error in
/// the difference variable constraint (d = y - xi with domain of xi - y),
/// causing immediate false UNSAT during root propagation.
#[test]
fn test_solve_cp_count_eq_asymmetric_ranges_6119() {
    let output = fzn2smt()
        .args([
            "solve-cp",
            cp_fixture_dir().join("count_eq_asym.fzn").to_str().unwrap(),
            "--timeout",
            "5000",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "solve-cp count_eq_asym should succeed, stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("----------"),
        "count_eq_asym: should find a solution (not false UNSAT), got: {stdout}"
    );
    assert!(
        !stdout.contains("UNSATISFIABLE"),
        "count_eq_asym: must NOT be UNSATISFIABLE (regression #6119)"
    );
    // cnt must be 0 since x ranges [5..9] don't overlap with y range [1..2]
    assert!(
        stdout.contains("cnt = 0;"),
        "count_eq_asym: cnt must be 0 (no xi can equal y), got: {stdout}"
    );
}

#[test]
fn test_solve_cp_table_sparse_hole_6591() {
    let output = fzn2smt()
        .args([
            "solve-cp",
            cp_fixture_dir()
                .join("table_sparse_hole_6591.fzn")
                .to_str()
                .unwrap(),
            "--timeout",
            "5000",
        ])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "solve-cp table_sparse_hole_6591 should succeed, stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("----------"),
        "table_sparse_hole_6591: should find a solution, got: {stdout}"
    );
    assert!(
        !stdout.contains("UNSATISFIABLE"),
        "table_sparse_hole_6591: must not be UNSATISFIABLE, got: {stdout}"
    );
    assert!(
        stdout.contains("x = 1;"),
        "table_sparse_hole_6591: x must use the only supported sparse-domain value, got: {stdout}"
    );
    assert!(
        stdout.contains("y = 1;"),
        "table_sparse_hole_6591: y must match the unique supported tuple, got: {stdout}"
    );
}

// --- solve command (Library backend via z4-library feature) ---
//
// The `solve` command is the FlatZinc portfolio entry point: it prefers the
// CP backend and falls back to the in-process SMT Library backend when the
// CP frontend cannot handle the model. These tests exercise the user-facing
// solve protocol regardless of which backend gets selected.

#[test]
fn test_solve_satisfy_library_backend() {
    let output = fzn2smt()
        .args(["solve", satisfy_fzn().to_str().unwrap()])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "solve satisfy should succeed, stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("----------"),
        "solve satisfy: should print solution separator, got: {stdout}"
    );
    assert!(stdout.contains("x = "), "solve satisfy: should print x");
    assert!(stdout.contains("y = "), "solve satisfy: should print y");
    // Verify the disequality constraint: x != y
    let x: Option<i64> = stdout
        .lines()
        .find(|l| l.starts_with("x = "))
        .and_then(|l| l.trim_end_matches(';').split(" = ").nth(1))
        .and_then(|s| s.parse().ok());
    let y: Option<i64> = stdout
        .lines()
        .find(|l| l.starts_with("y = "))
        .and_then(|l| l.trim_end_matches(';').split(" = ").nth(1))
        .and_then(|s| s.parse().ok());
    assert_ne!(x, y, "solve satisfy: x and y must differ");
}

#[test]
fn test_solve_minimize_library_backend() {
    let output = fzn2smt()
        .args(["solve", minimize_fzn().to_str().unwrap()])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "solve minimize should succeed, stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("----------"),
        "solve minimize: should print at least one solution"
    );
    assert!(
        stdout.contains("=========="),
        "solve minimize: should signal optimality"
    );
    // The problem is: minimize x, subject to x > 2, x in [1,10]
    // Optimal: x = 3
    let last_x = stdout
        .lines()
        .rev()
        .find(|l| l.starts_with("x = "))
        .expect("solve minimize: should print x");
    assert_eq!(last_x, "x = 3;", "solve minimize: optimal x should be 3");
}

#[test]
fn test_solve_minimize_with_timeout_flag() {
    // Timeout is handled natively by the Library backend's Solver::set_timeout()
    // in the incremental (optimization) path. The one-shot satisfaction path
    // falls back to subprocess when timeout is set.
    let output = fzn2smt()
        .args(["solve", minimize_fzn().to_str().unwrap(), "--timeout=5000"])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "solve minimize with timeout should succeed, stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("----------"),
        "solve minimize with timeout: should find solution"
    );
    assert!(
        stdout.contains("=========="),
        "solve minimize with timeout: should signal optimality"
    );
}

#[test]
fn test_solve_auto_selects_cp_for_cp_only_constraint() {
    let path = cp_fixture_dir().join("array_int_maximum_auto.fzn");
    let output = fzn2smt()
        .args(["solve", path.to_str().unwrap(), "--timeout", "5000"])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "solve should auto-select CP for array_int_maximum, stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("r = 7;"), "output: {stdout}");
    assert!(stdout.contains("=========="), "output: {stdout}");
}

#[test]
fn test_direct_fzn_invocation_prefers_cp_backend() {
    let path = cp_fixture_dir().join("array_int_maximum_auto.fzn");
    let output = fzn2smt()
        .args(["-t", "5000", path.to_str().unwrap()])
        .output()
        .expect("failed to run fzn2smt");

    assert!(
        output.status.success(),
        "direct .fzn invocation should solve via CP, stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("r = 7;"), "output: {stdout}");
    assert!(stdout.contains("=========="), "output: {stdout}");
}
