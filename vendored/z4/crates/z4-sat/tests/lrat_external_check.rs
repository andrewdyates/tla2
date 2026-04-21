// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]

//! External LRAT proof validation tests.
//!
//! Generates LRAT proofs from Z4 and validates them using `lrat-check`
//! (from drat-trim suite). This catches incomplete resolution chains
//! that structural-only tests miss.
//!
//! Reference: #4092 (shrink LRAT chain gap), #4380 (feature-isolated LRAT)

mod common;

use common::{read_barrel6, read_manol_pipe_c9, PHP43_DIMACS};
use ntest::timeout;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use z4_sat::{parse_dimacs, ProofOutput, SatResult, Solver};

static TEMP_FILE_SEQ: AtomicU64 = AtomicU64::new(0);

fn keep_lrat_artifacts() -> bool {
    matches!(
        std::env::var("Z4_KEEP_LRAT_ARTIFACTS").as_deref(),
        Ok("1") | Ok("true") | Ok("TRUE")
    )
}

fn require_lrat_check() -> PathBuf {
    if let Some(path) = common::find_lrat_check() {
        return path;
    }

    assert!(
        std::env::var_os("CI").is_none(),
        "lrat-check not found. Install drat-trim and ensure lrat-check is on PATH \
         or in /tmp/drat-trim, /usr/local/bin, or /opt/homebrew/bin."
    );

    if let Some(path) = find_z4_lrat_check() {
        eprintln!("lrat-check not found, falling back to bundled z4-lrat-check");
        return path;
    }

    panic!(
        "lrat-check not found, and bundled z4-lrat-check is unavailable. \
         Build: cargo build -p z4-lrat-check"
    );
}

/// PHP(3,2): 6 vars, 9 clauses.
const PHP32_DIMACS: &str = "\
p cnf 6 9
1 2 0
3 4 0
5 6 0
-1 -3 0
-1 -5 0
-3 -5 0
-2 -4 0
-2 -6 0
-4 -6 0
";

fn stress_formula_dimacs() -> String {
    if cfg!(debug_assertions) {
        PHP43_DIMACS.to_owned()
    } else {
        read_barrel6().unwrap_or_else(|| PHP43_DIMACS.to_owned())
    }
}

/// Small random 3-SAT formula (known UNSAT).
const RANDOM_3SAT_DIMACS: &str = "\
p cnf 8 34
1 2 3 0
-1 2 3 0
1 -2 3 0
1 2 -3 0
-1 -2 3 0
-1 2 -3 0
1 -2 -3 0
-1 -2 -3 0
4 5 6 0
-4 5 6 0
4 -5 6 0
4 5 -6 0
-4 -5 6 0
-4 5 -6 0
4 -5 -6 0
-4 -5 -6 0
1 4 7 0
-1 -4 7 0
2 5 8 0
-2 -5 8 0
3 6 7 0
-3 -6 8 0
1 5 8 0
-1 6 7 0
2 4 8 0
-2 -4 -8 0
3 -5 7 0
-3 5 -7 0
1 -6 8 0
-1 6 -8 0
2 -4 7 0
-2 4 -7 0
7 8 1 0
-7 -8 -1 0
";

/// PHP(4,2): 4 pigeons, 2 holes — guaranteed UNSAT.
const PHP42_MUTEX_DIMACS: &str = "\
p cnf 8 16
1 2 0
3 4 0
5 6 0
7 8 0
-1 -3 0
-1 -5 0
-1 -7 0
-3 -5 0
-3 -7 0
-5 -7 0
-2 -4 0
-2 -6 0
-2 -8 0
-4 -6 0
-4 -8 0
-6 -8 0
";

// ============================================================================
// External LRAT validation tests
// ============================================================================

/// PHP(3,2): 3 pigeons, 2 holes — simple UNSAT, no shrink
#[test]
#[timeout(10_000)]
fn test_lrat_external_php32_no_shrink() {
    let lrat_check = require_lrat_check();
    solve_and_validate_lrat_configured(
        PHP32_DIMACS,
        |s| s.set_shrink_enabled(false),
        &lrat_check,
        "php32_no_shrink",
    );
}

/// PHP(3,2) with shrink enabled — tests shrink LRAT chain (#4092)
#[test]
#[timeout(10_000)]
fn test_lrat_external_php32_with_shrink() {
    let lrat_check = require_lrat_check();
    solve_and_validate_lrat_configured(
        PHP32_DIMACS,
        |s| s.set_shrink_enabled(true),
        &lrat_check,
        "php32_with_shrink",
    );
}

/// PHP(4,3): larger pigeon-hole — more conflicts, more shrink opportunities
#[test]
#[timeout(10_000)]
fn test_lrat_external_php43_with_shrink() {
    let lrat_check = require_lrat_check();
    solve_and_validate_lrat_configured(
        PHP43_DIMACS,
        |s| s.set_shrink_enabled(true),
        &lrat_check,
        "php43_with_shrink",
    );
}

/// Random 3-SAT at threshold (4.26 clause/variable ratio) — stress test
#[test]
#[timeout(10_000)]
fn test_lrat_external_random_3sat_with_shrink() {
    let lrat_check = require_lrat_check();
    solve_and_validate_lrat_configured(
        RANDOM_3SAT_DIMACS,
        |s| s.set_shrink_enabled(true),
        &lrat_check,
        "random_3sat_with_shrink",
    );
}

/// Mutually exclusive pairs — generates many same-level conflicts (shrink target)
#[test]
#[timeout(10_000)]
fn test_lrat_external_mutex_pairs_with_shrink() {
    let lrat_check = require_lrat_check();
    solve_and_validate_lrat_configured(
        PHP42_MUTEX_DIMACS,
        |s| s.set_shrink_enabled(true),
        &lrat_check,
        "mutex_pairs_with_shrink",
    );
}

/// Exhaustive LRAT external verification for all UNSAT DIMACS benchmarks.
///
/// Mirrors DRAT corpus coverage in `integration.rs` but validates LRAT proof
/// artifacts with `lrat-check` for every formula in `benchmarks/sat/unsat`.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_external_unsat_corpus_verification() {
    let lrat_check = require_lrat_check();
    let corpus_dir = common::workspace_root().join("benchmarks/sat/unsat");
    let mut cnf_files: Vec<_> = std::fs::read_dir(&corpus_dir)
        .unwrap_or_else(|e| panic!("Cannot read corpus dir {}: {}", corpus_dir.display(), e))
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "cnf"))
        .collect();
    cnf_files.sort();

    assert!(
        !cnf_files.is_empty(),
        "No .cnf files found in {}. LRAT corpus verification requires at least one benchmark.",
        corpus_dir.display()
    );

    let total = cnf_files.len();
    let mut verified = 0usize;
    for cnf_path in &cnf_files {
        let dimacs = std::fs::read_to_string(cnf_path)
            .unwrap_or_else(|e| panic!("Failed to read {}: {}", cnf_path.display(), e));
        let label = cnf_path
            .file_stem()
            .and_then(|name| name.to_str())
            .unwrap_or("corpus_case");
        solve_and_validate_lrat_configured(
            &dimacs,
            common::disable_all_inprocessing,
            &lrat_check,
            &format!("lrat_corpus_{label}"),
        );
        verified += 1;
    }

    assert_eq!(
        verified, total,
        "All UNSAT corpus formulas must verify with lrat-check"
    );
    eprintln!("LRAT corpus: ALL {total}/{total} benchmarks externally verified by lrat-check");
}

/// Exhaustive LRAT external verification with ALL inprocessing enabled (#5103).
///
/// The base corpus test (`test_lrat_external_unsat_corpus_verification`) disables
/// all inprocessing, so it only validates LRAT proofs from the base CDCL engine.
/// This test runs the same corpus with default configuration (all inprocessing
/// enabled), catching LRAT hint generation bugs in BVE, vivification,
/// subsumption, conditioning, probe, transred, BCE, HTR, and decompose.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_external_unsat_corpus_all_features() {
    let lrat_check = require_lrat_check();
    let corpus_dir = common::workspace_root().join("benchmarks/sat/unsat");
    let mut cnf_files: Vec<_> = std::fs::read_dir(&corpus_dir)
        .unwrap_or_else(|e| panic!("Cannot read corpus dir {}: {}", corpus_dir.display(), e))
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "cnf"))
        .collect();
    cnf_files.sort();

    assert!(
        !cnf_files.is_empty(),
        "No .cnf files found in {}",
        corpus_dir.display()
    );

    let total = cnf_files.len();
    let mut verified = 0usize;
    for cnf_path in &cnf_files {
        let dimacs = std::fs::read_to_string(cnf_path)
            .unwrap_or_else(|e| panic!("Failed to read {}: {}", cnf_path.display(), e));
        let label = cnf_path
            .file_stem()
            .and_then(|name| name.to_str())
            .unwrap_or("corpus_case");
        solve_and_validate_lrat_configured(
            &dimacs,
            |_solver| {
                // Default config: all inprocessing features enabled.
            },
            &lrat_check,
            &format!("lrat_corpus_all_features_{label}"),
        );
        verified += 1;
    }

    assert_eq!(
        verified, total,
        "All UNSAT corpus formulas must verify with lrat-check (all features)"
    );
    eprintln!(
        "LRAT corpus (all features): ALL {total}/{total} benchmarks externally verified by lrat-check"
    );
}

// ============================================================================
// Feature-isolated LRAT external validation tests (#4380)
//
// Each test enables exactly one inprocessing feature (all others disabled)
// and validates the LRAT proof with lrat-check. Uses barrel6 (248 vars,
// 3729 clauses) which generates enough conflicts (>25000) to trigger all
// features at their default scheduling intervals.
//
// Mirrors the DRAT feature-isolation tests in drat_vivify_3481.rs.
// ============================================================================

/// Solve a formula with LRAT proof output and validate with lrat-check.
///
/// The `configure` closure sets up the solver (e.g., disable all inprocessing
/// then enable one feature) before clauses are added and solving begins.
fn solve_and_validate_lrat_configured(
    dimacs: &str,
    configure: impl FnOnce(&mut Solver),
    lrat_check_path: &Path,
    label: &str,
) -> String {
    let formula = parse_dimacs(dimacs).expect("Failed to parse DIMACS");
    let proof_writer = ProofOutput::lrat_text(Vec::new(), formula.clauses.len() as u64);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    configure(&mut solver);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert_eq!(result, SatResult::Unsat, "{label}: formula must be UNSAT");

    let writer = solver
        .take_proof_writer()
        .expect("Proof writer should exist");
    let proof = String::from_utf8(writer.into_vec().expect("proof flush")).expect("Valid UTF-8");
    assert!(!proof.is_empty(), "{label}: LRAT proof must not be empty");
    validate_lrat_proof_text(dimacs, &proof, lrat_check_path, label)
}

/// Solve a formula with binary LRAT proof output and validate with a checker.
///
/// Same as `solve_and_validate_lrat_configured` but uses binary LRAT format.
/// The `checker_path` must support binary LRAT (z4-lrat-check auto-detects;
/// external lrat-check may not support binary).
fn solve_and_validate_lrat_binary_configured(
    dimacs: &str,
    configure: impl FnOnce(&mut Solver),
    checker_path: &Path,
    label: &str,
) -> Vec<u8> {
    let formula = parse_dimacs(dimacs).expect("Failed to parse DIMACS");
    let proof_writer = ProofOutput::lrat_binary(Vec::new(), formula.clauses.len() as u64);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    configure(&mut solver);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert_eq!(result, SatResult::Unsat, "{label}: formula must be UNSAT");

    let writer = solver
        .take_proof_writer()
        .expect("Proof writer should exist");
    let proof_bytes = writer.into_vec().expect("proof flush");
    assert!(
        !proof_bytes.is_empty(),
        "{label}: binary LRAT proof must not be empty"
    );
    validate_lrat_proof_binary(dimacs, &proof_bytes, checker_path, label)
}

fn validate_lrat_proof_text(
    dimacs: &str,
    proof: &str,
    lrat_check_path: &Path,
    label: &str,
) -> String {
    let run_id = TEMP_FILE_SEQ.fetch_add(1, Ordering::Relaxed);
    let cnf_path = std::env::temp_dir().join(format!(
        "z4_lrat_test_{}_{}.cnf",
        std::process::id(),
        run_id
    ));
    let proof_path = std::env::temp_dir().join(format!(
        "z4_lrat_test_{}_{}.lrat",
        std::process::id(),
        run_id
    ));

    std::fs::write(&cnf_path, dimacs).expect("Write CNF");
    std::fs::write(&proof_path, &proof).expect("Write LRAT proof");

    let output = std::process::Command::new(lrat_check_path)
        .arg(&cnf_path)
        .arg(&proof_path)
        .output()
        .expect("Failed to run lrat-check");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    let has_warning = stdout.contains("WARNING") || stderr.contains("WARNING");
    let keep_artifacts = keep_lrat_artifacts() || has_warning;
    if keep_artifacts {
        eprintln!(
            "Preserving LRAT artifacts ({label}): cnf={} lrat={}",
            cnf_path.display(),
            proof_path.display()
        );
    } else {
        let _ = std::fs::remove_file(&cnf_path);
        let _ = std::fs::remove_file(&proof_path);
    }

    assert!(
        output.status.success() && !stdout.contains("FAILED") && !stderr.contains("FAILED"),
        "LRAT validation FAILED ({label})\n\
         cnf: {}\n\
         lrat: {}\n\
         lrat-check stdout: {}\n\
         lrat-check stderr: {}\n\
         exit code: {}\n\
         proof:\n{}",
        cnf_path.display(),
        proof_path.display(),
        stdout,
        stderr,
        output.status,
        proof
    );

    eprintln!("LRAT validation passed ({label}): {}", stdout.trim());

    proof.to_string()
}

/// Validate binary LRAT proof bytes using an external checker.
///
/// The checker must support binary LRAT auto-detection (e.g., z4-lrat-check).
fn validate_lrat_proof_binary(
    dimacs: &str,
    proof_bytes: &[u8],
    checker_path: &Path,
    label: &str,
) -> Vec<u8> {
    let run_id = TEMP_FILE_SEQ.fetch_add(1, Ordering::Relaxed);
    let cnf_path = std::env::temp_dir().join(format!(
        "z4_lrat_bin_test_{}_{}.cnf",
        std::process::id(),
        run_id
    ));
    let proof_path = std::env::temp_dir().join(format!(
        "z4_lrat_bin_test_{}_{}.lrat",
        std::process::id(),
        run_id
    ));

    std::fs::write(&cnf_path, dimacs).expect("Write CNF");
    std::fs::write(&proof_path, proof_bytes).expect("Write binary LRAT proof");

    let output = std::process::Command::new(checker_path)
        .arg(&cnf_path)
        .arg(&proof_path)
        .output()
        .expect("Failed to run checker on binary LRAT");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    let keep_artifacts = keep_lrat_artifacts();
    if keep_artifacts {
        eprintln!(
            "Preserving binary LRAT artifacts ({label}): cnf={} lrat={}",
            cnf_path.display(),
            proof_path.display()
        );
    } else {
        let _ = std::fs::remove_file(&cnf_path);
        let _ = std::fs::remove_file(&proof_path);
    }

    assert!(
        output.status.success() && (stdout.contains("s VERIFIED") || stdout.contains("VERIFIED")),
        "Binary LRAT validation FAILED ({label})\n\
         cnf: {}\n\
         lrat: {}\n\
         checker stdout: {}\n\
         checker stderr: {}\n\
         exit code: {}\n\
         proof size: {} bytes",
        cnf_path.display(),
        proof_path.display(),
        stdout,
        stderr,
        output.status,
        proof_bytes.len()
    );

    eprintln!(
        "Binary LRAT validation passed ({label}, {} bytes): {}",
        proof_bytes.len(),
        stdout.trim()
    );

    proof_bytes.to_vec()
}

/// Solve with one feature enabled (all others disabled) and validate LRAT proof.
/// Uses barrel6 in release mode; PHP43 in debug mode (LRAT overhead makes
/// barrel6 exceed 180s debug timeouts). Mirrors `verify_feature_drat`.
fn verify_feature_lrat(feature_name: &str, enable: fn(&mut Solver)) {
    let cnf = stress_formula_dimacs();
    verify_feature_lrat_on_dimacs(feature_name, &cnf, enable);
}

/// Solve a DIMACS formula with one feature enabled (all others disabled) and
/// validate the LRAT proof externally.
fn verify_feature_lrat_on_dimacs(feature_name: &str, cnf: &str, enable: fn(&mut Solver)) {
    let lrat_check = require_lrat_check();
    solve_and_validate_lrat_configured(
        cnf,
        |solver| {
            common::disable_all_inprocessing(solver);
            enable(solver);
        },
        &lrat_check,
        &format!("lrat_{feature_name}_barrel6"),
    );
}

/// Baseline: bare CDCL LRAT proof on barrel6 (no inprocessing).
/// Pure CDCL on barrel6 is slow in debug mode — requires extended timeout.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_lrat_external_baseline_barrel6() {
    let lrat_check = require_lrat_check();
    let cnf = stress_formula_dimacs();
    solve_and_validate_lrat_configured(
        &cnf,
        common::disable_all_inprocessing,
        &lrat_check,
        "lrat_baseline_barrel6",
    );
}

/// LRAT proof for probing in isolation on barrel6.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_lrat_external_probe_barrel6() {
    verify_feature_lrat("probe", |s| s.set_probe_enabled(true));
}

/// LRAT proof for BCE in isolation on barrel6.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_lrat_external_bce_barrel6() {
    verify_feature_lrat("bce", |s| s.set_bce_enabled(true));
}

/// LRAT proof for transitive reduction in isolation on barrel6.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_lrat_external_transred_barrel6() {
    verify_feature_lrat("transred", |s| s.set_transred_enabled(true));
}

/// LRAT proof for conditioning (GBCE) in isolation on barrel6.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_lrat_external_conditioning_barrel6() {
    verify_feature_lrat("conditioning", |s| s.set_condition_enabled(true));
}

/// LRAT proof for vivify in isolation on barrel6 (#4398: hint chain fix).
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_lrat_external_vivify_barrel6() {
    verify_feature_lrat("vivify", |s| s.set_vivify_enabled(true));
}

/// LRAT proof for subsumption in isolation on barrel6 (#4398: hint chain fix).
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_lrat_external_subsume_barrel6() {
    verify_feature_lrat("subsume", |s| s.set_subsume_enabled(true));
}

/// LRAT proof for HTR in isolation (#4398: antecedent clause ID hint fix).
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_lrat_external_htr_barrel6() {
    verify_feature_lrat("htr", |s| s.set_htr_enabled(true));
}

/// LRAT proof for BVE in isolation (#4398: antecedent clause ID hint fix).
/// Uses smaller PHP formula — BVE on barrel6 can be slow in debug mode.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_lrat_external_bve_barrel6() {
    verify_feature_lrat("bve", |s| s.set_bve_enabled(true));
}

/// LRAT proof for BVE in isolation on manol-pipe-c9 (946 vars, 12786 clauses).
/// Larger benchmark that stress-tests BVE clause ID tracking for LRAT hints.
///
/// BVE-only mode has known reconstruction bugs (#1464, #5044) that can cause
/// the solver to return Unknown on industrial benchmarks when the reduced
/// formula becomes unexpectedly SAT and model reconstruction fails. This test
/// validates the LRAT proof when BVE solves the formula, and accepts Unknown
/// as a known limitation. Sat is always rejected (manol-pipe-c9 is UNSAT).
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_external_bve_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };

    let formula = parse_dimacs(&cnf).expect("Failed to parse DIMACS");
    let proof_writer = ProofOutput::lrat_text(Vec::new(), formula.clauses.len() as u64);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    common::disable_all_inprocessing(&mut solver);
    solver.set_bve_enabled(true);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    match &result {
        SatResult::Unsat => {
            let writer = solver
                .take_proof_writer()
                .expect("Proof writer should exist");
            let proof =
                String::from_utf8(writer.into_vec().expect("proof flush")).expect("Valid UTF-8");
            assert!(
                !proof.is_empty(),
                "lrat_bve_manol_pipe_c9: LRAT proof must not be empty"
            );
            validate_lrat_proof_text(&cnf, &proof, &lrat_check, "lrat_bve_manol_pipe_c9");
        }
        SatResult::Unknown => {
            // BVE-only known incompleteness on industrial benchmarks (#1464, #5543).
            // The solver correctly detects invalid BVE reconstruction and returns
            // Unknown rather than a wrong Sat answer.
            eprintln!(
                "BVE-only returned Unknown on manol-pipe-c9 \
                 (known BVE reconstruction issue #1464, #5543)"
            );
        }
        SatResult::Sat(_) => {
            panic!("manol-pipe-c9 is UNSAT — BVE-only must not return Sat");
        }
        _ => unreachable!(),
    }
}

/// LRAT proof with all defaults on manol-pipe-c9.
/// Tests multi-technique LRAT interaction on industrial benchmark.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_external_all_features_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |_solver| {
            // Default config: all features enabled
        },
        &lrat_check,
        "lrat_all_features_manol_pipe_c9",
    );
}

/// LRAT proof with no inprocessing on manol-pipe-c9 (baseline).
/// Isolates whether LRAT failure is BVE-specific or general.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_external_baseline_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        common::disable_all_inprocessing,
        &lrat_check,
        "lrat_baseline_manol_pipe_c9",
    );
}

/// LRAT proof with decompose enabled on barrel6.
///
/// Decompose is enabled in LRAT mode (#4606) with constructive chain-based
/// hints from the SCC BFS traversal. This test validates that decompose
/// equivalence binaries and substituted clauses produce valid LRAT chains
/// verified by the external checker.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_lrat_external_decompose_barrel6() {
    verify_feature_lrat("decompose", |s| s.set_decompose_enabled(true));
}

/// LRAT proof with factorize enabled on barrel6 (#5020).
///
/// NOTE: Factorize is disabled at runtime in LRAT mode (lrat_override = true
/// in inproc_control.rs) because factorization requires RAT witness semantics
/// which LRAT does not support. This test is a regression guard confirming
/// that LRAT proofs remain valid with factor *requested* but not *executed*.
///
/// For factorize proof output verification, use DRAT mode tests
/// (test_factorize_drat_proof_emission in solver/tests.rs).
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_lrat_external_factorize_barrel6() {
    verify_feature_lrat("factorize", |s| s.set_factor_enabled(true));
}

/// LRAT proof with congruence enabled on barrel6 (#5020, #5419).
///
/// Congruence is enabled in LRAT mode (lrat_override = false) with probe-based
/// LRAT hints (#5419). This test validates that congruence-derived binary
/// clauses produce valid LRAT resolution chains verified by external checker.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_lrat_external_congruence_barrel6() {
    verify_feature_lrat("congruence", |s| s.set_congruence_enabled(true));
}

/// LRAT proof with sweep enabled on barrel6 (#5020, #5419).
///
/// Sweep is enabled in LRAT mode (lrat_override = false) with probe-based
/// unit LRAT hints (#5419). This test validates that sweep-derived unit
/// clauses produce valid LRAT resolution chains verified by external checker.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_lrat_external_sweep_barrel6() {
    verify_feature_lrat("sweep", |s| s.set_sweep_enabled(true));
}

/// DRAT proof for decompose on PHP(4,3) with embedded binary equivalences.
///
/// Decompose is disabled in LRAT mode (config.rs:173), so LRAT tests are
/// Tests DRAT mode where decompose fires and verifies the DRUP proof
/// with external drat-trim. Decompose is now also enabled in LRAT mode
/// (#4606) with constructive chain hints.
///
/// The formula embeds binary equivalence chains (x13↔x14↔x15↔x16) in
/// PHP(4,3) to guarantee decompose finds a non-trivial SCC to rewrite.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_drat_external_decompose_with_equivalences() {
    // PHP(4,3) + 4-variable equivalence chain: 16 vars, 28 clauses.
    let dimacs = "\
p cnf 16 28
1 2 3 0
4 5 6 0
7 8 9 0
10 11 12 0
-1 -4 0
-1 -7 0
-1 -10 0
-4 -7 0
-4 -10 0
-7 -10 0
-2 -5 0
-2 -8 0
-2 -11 0
-5 -8 0
-5 -11 0
-8 -11 0
-3 -6 0
-3 -9 0
-3 -12 0
-6 -9 0
-6 -12 0
-9 -12 0
-13 14 0
-14 13 0
-14 15 0
-15 14 0
-15 16 0
-16 15 0
";

    let drat_trim = common::find_drat_trim();
    let drat_trim = match drat_trim {
        Some(p) => p,
        None => {
            eprintln!("drat-trim not found, skipping external DRAT decompose test");
            return;
        }
    };

    let formula = parse_dimacs(dimacs).expect("Failed to parse DIMACS");
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    common::disable_all_inprocessing(&mut solver);
    solver.set_decompose_enabled(true);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert_eq!(result, SatResult::Unsat, "formula must be UNSAT");

    let decompose_rounds = solver.decompose_stats().rounds;
    eprintln!("decompose fired {decompose_rounds} round(s)");

    let writer = solver
        .take_proof_writer()
        .expect("Proof writer should exist");
    let proof = String::from_utf8(writer.into_vec().expect("proof flush")).expect("Valid UTF-8");
    assert!(!proof.is_empty(), "DRAT proof must not be empty");

    let run_id = TEMP_FILE_SEQ.fetch_add(1, Ordering::Relaxed);
    let cnf_path = std::env::temp_dir().join(format!(
        "z4_drat_decompose_equiv_{}_{}.cnf",
        std::process::id(),
        run_id
    ));
    let proof_path = std::env::temp_dir().join(format!(
        "z4_drat_decompose_equiv_{}_{}.drat",
        std::process::id(),
        run_id
    ));

    std::fs::write(&cnf_path, dimacs).expect("Write CNF");
    std::fs::write(&proof_path, &proof).expect("Write DRAT proof");

    let output = std::process::Command::new(&drat_trim)
        .arg(&cnf_path)
        .arg(&proof_path)
        .output()
        .expect("Failed to run drat-trim");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    eprintln!(
        "DRAT decompose artifacts: cnf={} drat={}",
        cnf_path.display(),
        proof_path.display()
    );
    eprintln!("drat-trim stdout: {stdout}");
    eprintln!("drat-trim stderr: {stderr}");
    eprintln!("decompose rounds: {decompose_rounds}");

    // drat-trim outputs "s VERIFIED" on success.
    assert!(
        stdout.contains("VERIFIED"),
        "DRAT proof validation FAILED (decompose-equivalences)\n\
         cnf: {}\n\
         drat: {}\n\
         drat-trim stdout: {}\n\
         drat-trim stderr: {}\n\
         exit code: {}\n\
         decompose rounds: {}\n\
         proof:\n{}",
        cnf_path.display(),
        proof_path.display(),
        stdout,
        stderr,
        output.status,
        decompose_rounds,
        proof
    );

    let _ = std::fs::remove_file(&cnf_path);
    let _ = std::fs::remove_file(&proof_path);
}

// find_drat_trim removed: use common::find_drat_trim() (#3927)

// ── PHP-based LRAT feature tests (fast, no external benchmark) ──

macro_rules! lrat_feature_test {
    ($test_name:ident, $feature_name:literal, $setter:ident) => {
        #[test]
        #[timeout(30_000)]
        fn $test_name() {
            let lrat_check = require_lrat_check();
            solve_and_validate_lrat_configured(
                PHP43_DIMACS,
                |solver| {
                    common::disable_all_inprocessing(solver);
                    solver.$setter(true);
                },
                &lrat_check,
                $feature_name,
            );
        }
    };
}

lrat_feature_test!(test_lrat_feature_vivify, "vivify", set_vivify_enabled);
lrat_feature_test!(test_lrat_feature_subsume, "subsume", set_subsume_enabled);
lrat_feature_test!(test_lrat_feature_probe, "probe", set_probe_enabled);
lrat_feature_test!(test_lrat_feature_bve, "bve", set_bve_enabled);
lrat_feature_test!(test_lrat_feature_bce, "bce", set_bce_enabled);
lrat_feature_test!(test_lrat_feature_transred, "transred", set_transred_enabled);
lrat_feature_test!(test_lrat_feature_htr, "htr", set_htr_enabled);
lrat_feature_test!(
    test_lrat_feature_decompose,
    "decompose",
    set_decompose_enabled
);
lrat_feature_test!(
    test_lrat_feature_conditioning,
    "conditioning",
    set_condition_enabled
);
lrat_feature_test!(test_lrat_feature_factorize, "factorize", set_factor_enabled);
lrat_feature_test!(
    test_lrat_feature_congruence,
    "congruence",
    set_congruence_enabled
);
lrat_feature_test!(test_lrat_feature_sweep, "sweep", set_sweep_enabled);
lrat_feature_test!(test_lrat_feature_backbone, "backbone", set_backbone_enabled);

/// BVE + vivify combination LRAT validation (#5014).
///
/// Verifies that LRAT proofs remain valid when both BVE and vivify are
/// enabled simultaneously. On PHP43, BVE may not eliminate variables (high
/// occurrence counts make elimination unprofitable), so this primarily
/// validates that the two techniques' proof streams compose correctly.
///
/// The specific ClearLevel0 → vivify interaction (where BVE clears reason
/// pointers and vivify encounters the victims) is covered by the unit test
/// test_vivify_probe_lrat_hints_include_level0_proof_id_after_clearlevel0
/// in tests.rs, which uses simulated ClearLevel0 state.
#[test]
#[timeout(30_000)]
fn test_lrat_feature_bve_plus_vivify() {
    let lrat_check = require_lrat_check();
    solve_and_validate_lrat_configured(
        PHP43_DIMACS,
        |solver| {
            common::disable_all_inprocessing(solver);
            solver.set_bve_enabled(true);
            solver.set_vivify_enabled(true);
        },
        &lrat_check,
        "bve_plus_vivify",
    );
}

// ============================================================================
// Technique-isolation tests on manol-pipe-c9 (#5222 bisection)
//
// The all_features test fails with "multiple literals unassigned in hint".
// These tests enable one LRAT-compatible technique at a time to identify
// which technique produces incomplete LRAT hint chains.
// ============================================================================

/// Vivify-only on manol-pipe-c9. Tests vivify probe LRAT hint chains.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_vivify_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            common::disable_all_inprocessing(s);
            s.set_vivify_enabled(true);
        },
        &lrat_check,
        "lrat_vivify_only_manol_pipe_c9",
    );
}

/// Subsumption-only on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_subsume_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            common::disable_all_inprocessing(s);
            s.set_subsume_enabled(true);
        },
        &lrat_check,
        "lrat_subsume_only_manol_pipe_c9",
    );
}

/// Probe-only on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_probe_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            common::disable_all_inprocessing(s);
            s.set_probe_enabled(true);
        },
        &lrat_check,
        "lrat_probe_only_manol_pipe_c9",
    );
}

/// HTR-only on manol-pipe-c9. Tests hidden ternary resolution LRAT hints.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_htr_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            common::disable_all_inprocessing(s);
            s.set_htr_enabled(true);
        },
        &lrat_check,
        "lrat_htr_only_manol_pipe_c9",
    );
}

/// Congruence-only on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_congruence_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            common::disable_all_inprocessing(s);
            s.set_congruence_enabled(true);
        },
        &lrat_check,
        "lrat_congruence_only_manol_pipe_c9",
    );
}

/// Transred-only on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_transred_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            common::disable_all_inprocessing(s);
            s.set_transred_enabled(true);
        },
        &lrat_check,
        "lrat_transred_only_manol_pipe_c9",
    );
}

/// BCE-only on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_bce_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            common::disable_all_inprocessing(s);
            s.set_bce_enabled(true);
        },
        &lrat_check,
        "lrat_bce_only_manol_pipe_c9",
    );
}

/// Vivify + subsume on manol-pipe-c9 (common pair interaction).
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_vivify_subsume_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            common::disable_all_inprocessing(s);
            s.set_vivify_enabled(true);
            s.set_subsume_enabled(true);
        },
        &lrat_check,
        "lrat_vivify_subsume_manol_pipe_c9",
    );
}

/// Vivify + HTR on manol-pipe-c9. Tests HTR binary → vivify reason interaction.
#[test]
#[cfg_attr(debug_assertions, timeout(900_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_vivify_htr_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            common::disable_all_inprocessing(s);
            s.set_vivify_enabled(true);
            s.set_htr_enabled(true);
        },
        &lrat_check,
        "lrat_vivify_htr_manol_pipe_c9",
    );
}

/// Group A: vivify + subsume + probe + transred (no HTR, no BCE, no gate).
#[test]
#[cfg_attr(debug_assertions, timeout(900_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_group_a_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            common::disable_all_inprocessing(s);
            s.set_vivify_enabled(true);
            s.set_subsume_enabled(true);
            s.set_probe_enabled(true);
            s.set_transred_enabled(true);
        },
        &lrat_check,
        "lrat_group_a_manol_pipe_c9",
    );
}

/// Group B: htr + bce + gate (no vivify, no subsume, no probe, no transred).
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_group_b_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            common::disable_all_inprocessing(s);
            s.set_htr_enabled(true);
            s.set_bce_enabled(true);
            s.set_gate_enabled(true);
        },
        &lrat_check,
        "lrat_group_b_manol_pipe_c9",
    );
}

/// Vivify + probe on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_vivify_probe_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            common::disable_all_inprocessing(s);
            s.set_vivify_enabled(true);
            s.set_probe_enabled(true);
        },
        &lrat_check,
        "lrat_vivify_probe_manol_pipe_c9",
    );
}

/// Vivify + transred on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_vivify_transred_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            common::disable_all_inprocessing(s);
            s.set_vivify_enabled(true);
            s.set_transred_enabled(true);
        },
        &lrat_check,
        "lrat_vivify_transred_manol_pipe_c9",
    );
}

/// Subsume + probe on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_subsume_probe_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            common::disable_all_inprocessing(s);
            s.set_subsume_enabled(true);
            s.set_probe_enabled(true);
        },
        &lrat_check,
        "lrat_subsume_probe_manol_pipe_c9",
    );
}

/// Subsume + transred on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_subsume_transred_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            common::disable_all_inprocessing(s);
            s.set_subsume_enabled(true);
            s.set_transred_enabled(true);
        },
        &lrat_check,
        "lrat_subsume_transred_manol_pipe_c9",
    );
}

/// Probe + transred on manol-pipe-c9.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_probe_transred_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            common::disable_all_inprocessing(s);
            s.set_probe_enabled(true);
            s.set_transred_enabled(true);
        },
        &lrat_check,
        "lrat_probe_transred_manol_pipe_c9",
    );
}

/// All LRAT-compatible except HTR.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_all_except_htr_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            // Start from defaults (all techniques enabled), only disable HTR.
            s.set_htr_enabled(false);
        },
        &lrat_check,
        "lrat_all_except_htr_manol_pipe_c9",
    );
}

/// All LRAT-compatible except BCE.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_all_except_bce_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            s.set_bce_enabled(false);
        },
        &lrat_check,
        "lrat_all_except_bce_manol_pipe_c9",
    );
}

/// All LRAT-compatible except gate.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_all_except_gate_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            s.set_gate_enabled(false);
        },
        &lrat_check,
        "lrat_all_except_gate_manol_pipe_c9",
    );
}

/// All LRAT-compatible except transred.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_all_except_transred_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            s.set_transred_enabled(false);
        },
        &lrat_check,
        "lrat_all_except_transred_manol_pipe_c9",
    );
}

/// All LRAT-compatible except probe.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_isolate_all_except_probe_manol_pipe_c9() {
    let lrat_check = require_lrat_check();
    let cnf = match read_manol_pipe_c9() {
        Some(cnf) => cnf,
        None => return,
    };
    solve_and_validate_lrat_configured(
        &cnf,
        |s| {
            s.set_probe_enabled(false);
        },
        &lrat_check,
        "lrat_all_except_probe_manol_pipe_c9",
    );
}

// ============================================================================
// Binary LRAT format validation tests (#5334)
//
// All previous tests use lrat_text format. These tests validate that z4's
// binary LRAT output (LEB128-encoded) is correctly formatted and externally
// verifiable. Binary LRAT is the format used by CaDiCaL and SAT Competition
// checkers; gaps here mean z4 cannot participate in proof-checked divisions.
//
// Uses z4-lrat-check (auto-detects binary) since external lrat-check from
// drat-trim may not support binary format.
// ============================================================================

/// Find z4-lrat-check binary. Returns None if not built yet.
fn find_z4_lrat_check() -> Option<PathBuf> {
    common::find_binary("z4-lrat-check")
}

fn require_z4_lrat_check() -> PathBuf {
    find_z4_lrat_check().unwrap_or_else(|| {
        panic!("z4-lrat-check binary not found. Build: cargo build -p z4-lrat-check")
    })
}

/// Binary LRAT: PHP(3,2), no inprocessing.
#[test]
#[timeout(10_000)]
fn test_lrat_binary_external_php32() {
    let checker = require_z4_lrat_check();
    solve_and_validate_lrat_binary_configured(
        PHP32_DIMACS,
        common::disable_all_inprocessing,
        &checker,
        "binary_php32",
    );
}

/// Binary LRAT: PHP(4,3), no inprocessing.
#[test]
#[timeout(30_000)]
fn test_lrat_binary_external_php43() {
    let checker = require_z4_lrat_check();
    solve_and_validate_lrat_binary_configured(
        PHP43_DIMACS,
        common::disable_all_inprocessing,
        &checker,
        "binary_php43",
    );
}

/// Binary LRAT: PHP(4,3) with all features enabled.
///
/// Validates binary LRAT proof completeness when inprocessing techniques
/// generate proof steps. This is the counterpart of the text-format
/// all-features tests.
#[test]
#[timeout(30_000)]
fn test_lrat_binary_external_php43_all_features() {
    let checker = require_z4_lrat_check();
    solve_and_validate_lrat_binary_configured(
        PHP43_DIMACS,
        |_solver| {},
        &checker,
        "binary_php43_all_features",
    );
}

/// Binary LRAT: random 3-SAT formula.
#[test]
#[timeout(10_000)]
fn test_lrat_binary_external_random_3sat() {
    let checker = require_z4_lrat_check();
    solve_and_validate_lrat_binary_configured(
        RANDOM_3SAT_DIMACS,
        common::disable_all_inprocessing,
        &checker,
        "binary_random_3sat",
    );
}

/// Binary LRAT: UNSAT corpus with no inprocessing.
///
/// Same benchmark set as text-format corpus test, but validates binary
/// encoding. A failure here (with text passing) indicates a binary
/// encoding bug in LratWriter, not a proof chain error.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_lrat_binary_external_unsat_corpus() {
    let checker = require_z4_lrat_check();
    let corpus_dir = common::workspace_root().join("benchmarks/sat/unsat");
    let mut cnf_files: Vec<_> = std::fs::read_dir(&corpus_dir)
        .unwrap_or_else(|e| panic!("Cannot read corpus dir {}: {}", corpus_dir.display(), e))
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "cnf"))
        .collect();
    cnf_files.sort();

    assert!(
        !cnf_files.is_empty(),
        "No .cnf files found in {}",
        corpus_dir.display()
    );

    let total = cnf_files.len();
    let mut verified = 0usize;
    for cnf_path in &cnf_files {
        let dimacs = std::fs::read_to_string(cnf_path)
            .unwrap_or_else(|e| panic!("Failed to read {}: {}", cnf_path.display(), e));
        let label = cnf_path
            .file_stem()
            .and_then(|name| name.to_str())
            .unwrap_or("corpus_case");
        solve_and_validate_lrat_binary_configured(
            &dimacs,
            common::disable_all_inprocessing,
            &checker,
            &format!("binary_corpus_{label}"),
        );
        verified += 1;
    }

    assert_eq!(verified, total);
    eprintln!("Binary LRAT corpus: ALL {total}/{total} benchmarks verified by z4-lrat-check");
}

/// Binary vs text LRAT cross-validation: both formats on the same formula
/// must produce proofs that independently validate.
///
/// This catches format-specific encoding bugs (e.g., LEB128 overflow,
/// wrong marker bytes) while confirming the proof chains are equivalent.
#[test]
#[timeout(30_000)]
fn test_lrat_binary_vs_text_cross_validate_php43() {
    let z4_checker = require_z4_lrat_check();
    let lrat_check = require_lrat_check();

    // Text format proof validated by external lrat-check.
    let text_proof = solve_and_validate_lrat_configured(
        PHP43_DIMACS,
        common::disable_all_inprocessing,
        &lrat_check,
        "cross_text_php43",
    );

    // Binary format proof validated by z4-lrat-check.
    let binary_proof = solve_and_validate_lrat_binary_configured(
        PHP43_DIMACS,
        common::disable_all_inprocessing,
        &z4_checker,
        "cross_binary_php43",
    );

    // Both proofs must be non-empty and different formats.
    assert!(!text_proof.is_empty());
    assert!(!binary_proof.is_empty());
    // Binary is typically smaller than text (LEB128 vs decimal ASCII).
    eprintln!(
        "Cross-validation: text={} bytes, binary={} bytes",
        text_proof.len(),
        binary_proof.len()
    );
}
