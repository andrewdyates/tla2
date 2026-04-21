// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end DRAT proof validation: z4 solver → z4-drat-check binary.
//!
//! Solves each UNSAT benchmark with z4, produces DRAT proofs, and validates
//! with z4-drat-check in both forward and backward modes. Also cross-validates
//! CaDiCaL-generated DRAT proofs against z4-drat-check.
//!
//! Closes the DRAT e2e coverage gap identified in #5264.

mod common;

use common::{PHP32_DIMACS, PHP43_DIMACS};
use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use z4_sat::{parse_dimacs, ProofOutput, SatResult, Solver};

static TEMP_SEQ: AtomicU64 = AtomicU64::new(0);

fn temp_paths(prefix: &str) -> (PathBuf, PathBuf) {
    let seq = TEMP_SEQ.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let cnf = std::env::temp_dir().join(format!("z4_drat_e2e_{prefix}_{pid}_{seq}.cnf"));
    let proof = std::env::temp_dir().join(format!("z4_drat_e2e_{prefix}_{pid}_{seq}.drat"));
    (cnf, proof)
}

/// Locate the z4-drat-check binary, returning `None` when absent.
///
/// CI panics immediately so missing binaries are caught. Local dev
/// environments skip gracefully (the binary may not be built yet).
fn find_z4_drat_check() -> Option<PathBuf> {
    if let Some(path) = common::find_binary("z4-drat-check") {
        return Some(path);
    }
    assert!(
        std::env::var_os("CI").is_none(),
        "z4-drat-check binary not found in CI. Build it first: \
         cargo build -p z4-drat-check"
    );
    eprintln!(
        "z4-drat-check binary not found, skipping DRAT e2e test. \
         Build it with: cargo build -p z4-drat-check"
    );
    None
}

fn find_cadical() -> Option<PathBuf> {
    let candidate = common::workspace_root().join("reference/cadical/build/cadical");
    candidate.is_file().then_some(candidate)
}

// ============================================================================
// z4 DRAT proof → z4-drat-check (forward + backward) on benchmark corpus
// ============================================================================

/// Solve a benchmark with z4, produce DRAT proof, validate with z4-drat-check.
///
/// Returns `false` (skipped) when z4-drat-check is not available in a local
/// dev environment. Panics in CI when the binary is missing.
fn solve_and_validate_drat(label: &str, dimacs: &str) -> bool {
    let formula = parse_dimacs(dimacs).expect("parse DIMACS");
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    let result = solver.solve().into_inner();
    assert_eq!(result, SatResult::Unsat, "{label} must be UNSAT");
    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("proof flush");

    let Some(checker) = find_z4_drat_check() else {
        return false;
    };

    // Forward mode
    {
        let (cnf_tmp, proof_tmp) = temp_paths(&format!("fwd_{label}"));
        std::fs::write(&cnf_tmp, &dimacs).expect("write CNF");
        std::fs::write(&proof_tmp, &proof_bytes).expect("write DRAT");
        let output = Command::new(&checker)
            .arg(&cnf_tmp)
            .arg(&proof_tmp)
            .output()
            .expect("run z4-drat-check forward");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let _ = std::fs::remove_file(&cnf_tmp);
        let _ = std::fs::remove_file(&proof_tmp);
        assert!(
            output.status.success() && stdout.contains("s VERIFIED"),
            "z4-drat-check forward FAILED on {label}:\nstdout: {stdout}\nstderr: {stderr}"
        );
        eprintln!("z4-drat-check forward VERIFIED ({label})");
    }

    // Backward mode
    {
        let (cnf_tmp, proof_tmp) = temp_paths(&format!("bwd_{label}"));
        std::fs::write(&cnf_tmp, &dimacs).expect("write CNF");
        std::fs::write(&proof_tmp, &proof_bytes).expect("write DRAT");
        let output = Command::new(&checker)
            .arg(&cnf_tmp)
            .arg(&proof_tmp)
            .arg("--backward")
            .output()
            .expect("run z4-drat-check backward");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let _ = std::fs::remove_file(&cnf_tmp);
        let _ = std::fs::remove_file(&proof_tmp);
        assert!(
            output.status.success() && stdout.contains("s VERIFIED"),
            "z4-drat-check backward FAILED on {label}:\nstdout: {stdout}\nstderr: {stderr}"
        );
        eprintln!("z4-drat-check backward VERIFIED ({label})");
    }
    true
}

fn solve_benchmark_drat(name: &str) {
    let cnf_path = common::workspace_root()
        .join("benchmarks/sat/unsat")
        .join(format!("{name}.cnf"));
    let dimacs =
        std::fs::read_to_string(&cnf_path).unwrap_or_else(|e| panic!("read {name}.cnf: {e}"));
    solve_and_validate_drat(name, &dimacs);
}

// All 12 UNSAT benchmarks — forward + backward DRAT checking (#5264).
#[test]
#[timeout(30_000)]
fn test_drat_benchmark_at_most_1_of_5() {
    solve_benchmark_drat("at_most_1_of_5");
}
#[test]
#[timeout(30_000)]
fn test_drat_benchmark_blocked_chain_8() {
    solve_benchmark_drat("blocked_chain_8");
}
#[test]
#[timeout(30_000)]
fn test_drat_benchmark_graph_coloring_k3_4clique() {
    solve_benchmark_drat("graph_coloring_k3_4clique");
}
#[test]
#[timeout(30_000)]
fn test_drat_benchmark_latin_square_2x2_conflict() {
    solve_benchmark_drat("latin_square_2x2_conflict");
}
#[test]
#[timeout(30_000)]
fn test_drat_benchmark_mutex_4proc() {
    solve_benchmark_drat("mutex_4proc");
}
#[test]
#[timeout(30_000)]
fn test_drat_benchmark_mutilated_chessboard_2x2() {
    solve_benchmark_drat("mutilated_chessboard_2x2");
}
#[test]
#[timeout(30_000)]
fn test_drat_benchmark_parity_6() {
    solve_benchmark_drat("parity_6");
}
#[test]
#[timeout(30_000)]
fn test_drat_benchmark_php_4_3() {
    solve_benchmark_drat("php_4_3");
}
#[test]
#[timeout(30_000)]
fn test_drat_benchmark_php_5_4() {
    solve_benchmark_drat("php_5_4");
}
#[test]
#[timeout(30_000)]
fn test_drat_benchmark_ramsey_r3_3_6() {
    solve_benchmark_drat("ramsey_r3_3_6");
}
#[test]
#[timeout(30_000)]
fn test_drat_benchmark_tseitin_grid_3x3() {
    solve_benchmark_drat("tseitin_grid_3x3");
}
#[test]
#[timeout(30_000)]
fn test_drat_benchmark_urquhart_3() {
    solve_benchmark_drat("urquhart_3");
}

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_drat_benchmark_eq_atree_braun_8() {
    let cnf_path =
        common::workspace_root().join("benchmarks/sat/eq_atree_braun/eq.atree.braun.8.unsat.cnf");
    let Some(dimacs) = common::load_benchmark_or_skip(&cnf_path) else {
        return;
    };
    solve_and_validate_drat("eq_atree_braun_8", &dimacs);
}

// ============================================================================
// Cross-validation: CaDiCaL DRAT → z4-drat-check (forward + backward)
// ============================================================================

/// Generate a DRAT proof with CaDiCaL and verify with z4-drat-check.
/// Returns false (skipped) if z4-drat-check or CaDiCaL is not available;
/// panics in CI.
fn cadical_drat_cross_validate(cnf_content: &str, label: &str) -> bool {
    let Some(checker) = find_z4_drat_check() else {
        return false;
    };
    let cadical = match find_cadical() {
        Some(p) => p,
        None => {
            assert!(
                std::env::var_os("CI").is_none(),
                "CaDiCaL is required in CI but not found at reference/cadical/build/cadical"
            );
            eprintln!("CaDiCaL not found, skipping cross-validation for {label}");
            return false;
        }
    };

    let (cnf_path, proof_path) = temp_paths(&format!("cadical_{label}"));
    std::fs::write(&cnf_path, cnf_content).expect("write CNF");

    let cadical_out = Command::new(&cadical)
        .arg(&cnf_path)
        .arg(&proof_path)
        .output()
        .unwrap_or_else(|e| panic!("failed to run CaDiCaL: {e}"));

    assert_eq!(
        cadical_out.status.code(),
        Some(20),
        "CaDiCaL did not return UNSAT for {label}"
    );
    let proof_size = std::fs::metadata(&proof_path).map(|m| m.len()).unwrap_or(0);
    assert!(proof_size > 0, "CaDiCaL produced empty proof for {label}");

    // Forward
    let output = Command::new(&checker)
        .arg(&cnf_path)
        .arg(&proof_path)
        .output()
        .expect("run z4-drat-check forward");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success() && stdout.contains("s VERIFIED"),
        "z4-drat-check forward FAILED on CaDiCaL proof for {label}\n\
         stdout: {stdout}\nstderr: {stderr}"
    );

    // Backward
    let output = Command::new(&checker)
        .arg(&cnf_path)
        .arg(&proof_path)
        .arg("--backward")
        .output()
        .expect("run z4-drat-check backward");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    let _ = std::fs::remove_file(&cnf_path);
    let _ = std::fs::remove_file(&proof_path);

    assert!(
        output.status.success() && stdout.contains("s VERIFIED"),
        "z4-drat-check backward FAILED on CaDiCaL proof for {label}\n\
         stdout: {stdout}\nstderr: {stderr}"
    );
    eprintln!("CaDiCaL DRAT cross-validation VERIFIED ({label})");
    true
}

#[test]
#[timeout(30_000)]
fn test_cadical_drat_php32() {
    cadical_drat_cross_validate(PHP32_DIMACS, "php32");
}

#[test]
#[timeout(30_000)]
fn test_cadical_drat_php43() {
    cadical_drat_cross_validate(PHP43_DIMACS, "php43");
}

#[test]
#[timeout(30_000)]
fn test_cadical_drat_benchmarks() {
    for name in [
        "ramsey_r3_3_6",
        "mutilated_chessboard_2x2",
        "at_most_1_of_5",
        "urquhart_3",
        "mutex_4proc",
    ] {
        let cnf_path = common::workspace_root()
            .join("benchmarks/sat/unsat")
            .join(format!("{name}.cnf"));
        assert!(cnf_path.exists(), "{name}.cnf not found");
        let cnf = std::fs::read_to_string(&cnf_path).expect("read CNF");
        cadical_drat_cross_validate(&cnf, name);
    }
}
