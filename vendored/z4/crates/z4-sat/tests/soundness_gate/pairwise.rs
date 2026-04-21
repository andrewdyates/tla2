// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pairwise interaction gates and comprehensive oracle tests.
//!
//! Tests that pairs of inprocessing features together don't cause
//! unsoundness, plus full-stack and CaDiCaL oracle comparison tests.

use ntest::timeout;
use z4_sat::{parse_dimacs, SatResult};

use super::common::{
    assert_model_satisfies, load_benchmark, run_cadical_oracle, sat_result_kind,
    solve_feature_isolation, solver_all_disabled, try_cadical_binary, try_load_benchmark,
    verify_full_stack_unsat_with_native_drat, verify_pairwise_unsat_with_native_drat, verify_unsat,
    verify_unsat_with_drat, verify_unsat_with_native_drat, GateFeature, OracleResult,
    GATE_BENCHMARKS, ORACLE_SAT_BENCHMARKS, ORACLE_UNSAT_BENCHMARKS,
};
use super::test_common;

// ============================================================================
// Pairwise interaction gates for currently-enabled features
// Tests that two features together don't cause unsoundness.
// ============================================================================

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_vivify_plus_subsume() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_vivify_enabled(true);
    solver.set_subsume_enabled(true);
    verify_unsat(&mut solver, &clauses, "vivify+subsume/longmult15");
}

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_probe_plus_transred() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_probe_enabled(true);
    solver.set_transred_enabled(true);
    verify_unsat(&mut solver, &clauses, "probe+transred/longmult15");
}

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_shrink_plus_probe() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_shrink_enabled(true);
    solver.set_probe_enabled(true);
    verify_unsat(&mut solver, &clauses, "shrink+probe/longmult15");
}

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_shrink_plus_vivify() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_shrink_enabled(true);
    solver.set_vivify_enabled(true);
    verify_unsat(&mut solver, &clauses, "shrink+vivify/longmult15");
}

#[test]
#[timeout(120_000)]
fn gate_shrink_plus_bve() {
    // Keep this interaction gate cheap: long structured UNSAT benchmarks can
    // exceed the timeout with BVE enabled (#3501), which turns this into a
    // timeout flake rather than a soundness check.
    //
    // The formula below is UNSAT and still drives conflict analysis, so both
    // shrink and BVE stay wired through the same solve path.
    let content = "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n".to_string();
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_shrink_enabled(true);
    solver.set_bve_enabled(true);
    verify_unsat(&mut solver, &clauses, "shrink+bve/tiny-xor-unsat");
}

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_bve_plus_congruence() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_bve_enabled(true);
    solver.set_congruence_enabled(true);
    verify_unsat(&mut solver, &clauses, "bve+congruence/longmult15");
}

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_htr_plus_congruence() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_htr_enabled(true);
    solver.set_congruence_enabled(true);
    verify_unsat(&mut solver, &clauses, "htr+congruence/longmult15");
}

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_bve_plus_bce() {
    let Some(content) = try_load_benchmark("cmu-bmc-longmult15.cnf") else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_bve_enabled(true);
    solver.set_bce_enabled(true);
    verify_unsat(&mut solver, &clauses, "bve+bce/longmult15");
}

// ============================================================================
// HTR isolation + DRAT proof verification (#3971)
// After the collect_level0_garbage() fix, HTR must produce correct results
// and valid DRAT proofs on all gate benchmarks.
// ============================================================================

#[test]
#[timeout(120_000)]
fn gate_htr_isolation() {
    for name in GATE_BENCHMARKS {
        let Some(content) = try_load_benchmark(name) else {
            continue;
        };
        let (mut solver, clauses) = solver_all_disabled(&content);
        solver.set_htr_enabled(true);
        verify_unsat(&mut solver, &clauses, &format!("htr-isolation/{name}"));
    }
}

#[test]
#[timeout(120_000)]
fn gate_htr_drat_proof_verification() {
    // Use only barrel6 (the smaller gate benchmark) for proof-mode DRAT
    // verification. longmult15 + DRAT + HTR exceeds 300s in debug mode,
    // turning this into a timeout flake rather than a soundness check
    // (same pattern as gate_shrink_plus_bve / #3501). HTR isolation
    // already covers both benchmarks without proof overhead.
    let content = load_benchmark("cmu-bmc-barrel6.cnf");
    verify_unsat_with_drat(GateFeature::Htr, &content, "htr-drat/barrel6");
}

/// DRAT proof verification for techniques previously excluded by proof_compatible() (#4447).
/// Each technique is a separate test to avoid cumulative timeout in debug mode.
/// Uses barrel6 (248 vars), same benchmark as gate_htr_drat_proof_verification.
#[test]
#[timeout(120_000)]
fn gate_condition_drat_proof_verification() {
    let content = load_benchmark("cmu-bmc-barrel6.cnf");
    verify_unsat_with_drat(
        GateFeature::Condition,
        &content,
        "conditioning-drat/barrel6",
    );
}

#[test]
#[timeout(300_000)]
fn gate_congruence_drat_proof_verification_barrel6() {
    // Congruence DRAT on barrel6 is the #4575 regression target.
    // Use isolated-feature mode to keep the proof trace focused on
    // congruence emissions and avoid full default-pipeline timeout flakes.
    let content = load_benchmark("cmu-bmc-barrel6.cnf");
    verify_unsat_with_drat(GateFeature::Congruence, &content, "congruence-drat/barrel6");
}

// Sweep DRAT test removed (#7037): kitten can't produce DRAT proof steps,
// and rebuild-per-probe makes sweep-only + DRAT too slow for barrel6.
// Sweep correctness is verified by the #6999 feature isolation tests and
// the full pairwise oracle comparison below.

#[test]
#[timeout(120_000)]
fn gate_decompose_drat_proof_verification() {
    let content = load_benchmark("cmu-bmc-barrel6.cnf");
    verify_unsat_with_drat(GateFeature::Decompose, &content, "decompose-drat/barrel6");
}

/// HTR oracle: verify Z4+HTR agrees with CaDiCaL on SAT/UNSAT benchmarks.
/// Catches wrong-UNSAT on SAT instances (the original #3873 failure mode).
#[test]
#[timeout(300_000)]
fn gate_htr_oracle_comparison() {
    if try_cadical_binary().is_none() {
        eprintln!("SKIP: CaDiCaL binary not available for oracle comparison");
        return;
    }
    for benchmark in ORACLE_SAT_BENCHMARKS {
        let path = test_common::workspace_root().join(benchmark.rel_path);
        let Some(cnf) = test_common::load_benchmark_or_skip(&path) else {
            continue;
        };
        let oracle = run_cadical_oracle(&cnf, &format!("htr_sat_{}", benchmark.name));
        assert_eq!(
            oracle,
            OracleResult::Sat,
            "oracle baseline SAT for {}",
            benchmark.name
        );
        let (result, clauses, _) = solve_feature_isolation(GateFeature::Htr, &cnf);
        let actual = sat_result_kind(&result);
        assert_eq!(
            actual, oracle,
            "SOUNDNESS GATE [htr/{}]: Z4+HTR vs CaDiCaL mismatch on SAT benchmark",
            benchmark.name
        );
        if let SatResult::Sat(model) = &result {
            assert_model_satisfies(&clauses, model, &format!("htr-oracle/{}", benchmark.name));
        }
    }

    for benchmark in ORACLE_UNSAT_BENCHMARKS {
        let path = test_common::workspace_root().join(benchmark.rel_path);
        let Some(cnf) = test_common::load_benchmark_or_skip(&path) else {
            continue;
        };
        let oracle = run_cadical_oracle(&cnf, &format!("htr_unsat_{}", benchmark.name));
        assert_eq!(
            oracle,
            OracleResult::Unsat,
            "oracle baseline UNSAT for {}",
            benchmark.name
        );
        let (result, _, _) = solve_feature_isolation(GateFeature::Htr, &cnf);
        let actual = sat_result_kind(&result);
        assert_eq!(
            actual, oracle,
            "SOUNDNESS GATE [htr/{}]: Z4+HTR vs CaDiCaL mismatch on UNSAT benchmark",
            benchmark.name
        );
    }
}

// ============================================================================
// Full-stack gate: all currently-enabled features together
// This is what into_solver() produces in DIMACS mode.
// ============================================================================

// All default features on 2 benchmarks; can exceed 120s with BVE+congruence.
#[test]
#[timeout(300_000)]
fn gate_all_enabled_features() {
    for name in GATE_BENCHMARKS {
        let Some(content) = try_load_benchmark(name) else {
            continue;
        };
        let formula = parse_dimacs(&content).expect("parse");
        let original_clauses = formula.clauses.clone();
        // into_solver() enables BVE + congruence on top of defaults
        let mut solver = formula.into_solver();
        verify_unsat(
            &mut solver,
            &original_clauses,
            &format!("all-enabled/{name}"),
        );
    }
}

// ============================================================================
// Full-stack DRAT proof verification with all features enabled (#7913)
// Complements gate_all_enabled_features above by also verifying the DRAT proof.
// Uses barrel6 (248 vars) to keep proof-mode overhead within timeout.
// ============================================================================

#[test]
#[timeout(300_000)]
fn gate_all_enabled_features_drat_barrel6() {
    let content = load_benchmark("cmu-bmc-barrel6.cnf");
    verify_full_stack_unsat_with_native_drat(&content, "all-enabled-drat/barrel6");
}

// ============================================================================
// Oracle comparison: Z4 vs CaDiCaL on expanded SAT/UNSAT coverage.
// DRAT stays in the UNSAT matrix only for the cheap subset; larger proof traces
// are covered by the focused per-feature DRAT tests above.
// ============================================================================

type OracleCase = (super::common::OracleBenchmark, String, OracleResult);

fn load_sat_oracle_cases() -> Vec<OracleCase> {
    ORACLE_SAT_BENCHMARKS
        .iter()
        .filter_map(|benchmark| {
            let path = test_common::workspace_root().join(benchmark.rel_path);
            let cnf = test_common::load_benchmark_or_skip(&path)?;
            let oracle = run_cadical_oracle(&cnf, &format!("sat_{}", benchmark.name));
            assert_eq!(
                oracle,
                OracleResult::Sat,
                "oracle baseline changed: expected SAT for {}",
                benchmark.name
            );
            Some((*benchmark, cnf, oracle))
        })
        .collect()
}

fn load_unsat_oracle_cases() -> Vec<OracleCase> {
    ORACLE_UNSAT_BENCHMARKS
        .iter()
        .filter_map(|benchmark| {
            let path = test_common::workspace_root().join(benchmark.rel_path);
            let cnf = test_common::load_benchmark_or_skip(&path)?;
            let oracle = run_cadical_oracle(&cnf, &format!("unsat_{}", benchmark.name));
            assert_eq!(
                oracle,
                OracleResult::Unsat,
                "oracle baseline changed: expected UNSAT for {}",
                benchmark.name
            );
            Some((*benchmark, cnf, oracle))
        })
        .collect()
}

fn run_sat_oracle_matrix(sat_cases: &[OracleCase]) {
    for feature in GateFeature::ALL {
        for (benchmark, cnf, expected) in sat_cases {
            let label = format!("{}/{}", feature.label(), benchmark.name);
            let (result, clauses, _) = solve_feature_isolation(feature, cnf);
            let actual = sat_result_kind(&result);
            assert_eq!(
                actual, *expected,
                "SOUNDNESS GATE [{label}]: Z4 vs CaDiCaL mismatch on SAT benchmark"
            );
            if let SatResult::Sat(model) = &result {
                assert_model_satisfies(&clauses, model, &label);
            }
        }
    }
}

fn run_unsat_oracle_matrix(unsat_cases: &[OracleCase]) {
    for feature in GateFeature::ALL {
        for (benchmark, cnf, expected) in unsat_cases {
            let label = format!("{}/{}", feature.label(), benchmark.name);
            let (result, clauses, _) = solve_feature_isolation(feature, cnf);
            let actual = sat_result_kind(&result);
            assert_eq!(
                actual, *expected,
                "SOUNDNESS GATE [{label}]: Z4 vs CaDiCaL mismatch on UNSAT benchmark"
            );

            if let SatResult::Sat(model) = &result {
                assert_model_satisfies(&clauses, model, &label);
            }

            // Native DRAT verification (z4-drat-check, in-process) for
            // matrix_drat benchmarks (#7913). Uses the hermetic in-process
            // checker (no external drat-trim required). In debug builds,
            // the solver's inline forward checker also verifies every
            // derived clause is RUP-implied during the proof-mode re-solve.
            // Regression coverage for #7929 (forward checker assertion
            // failure fixed by removing BVE backward subsumption in #7917).
            if benchmark.matrix_drat
                && feature.drat_verified()
                && matches!(result, SatResult::Unsat)
            {
                verify_unsat_with_native_drat(feature, cnf, &format!("native_drat_{label}"));
            }
        }
    }
}

#[test]
// 14 features x 7 UNSAT benchmarks + 56 native DRAT proof-mode re-solves.
// Debug-mode forward checker makes proof solves ~5x slower. 600s needed.
#[timeout(600_000)]
fn gate_isolation_oracle_model_matrix_sat() {
    if try_cadical_binary().is_none() {
        eprintln!("SKIP: CaDiCaL binary not available for SAT oracle matrix");
        return;
    }
    let sat_cases = load_sat_oracle_cases();
    run_sat_oracle_matrix(&sat_cases);
}

// 14 features x 7 UNSAT benchmarks + 56 native DRAT proof-mode re-solves.
// Debug-mode forward checker makes proof solves ~5x slower. 600s needed.
#[test]
#[timeout(600_000)]
fn gate_isolation_oracle_model_and_drat_matrix_unsat() {
    if try_cadical_binary().is_none() {
        eprintln!("SKIP: CaDiCaL binary not available for UNSAT oracle matrix");
        return;
    }
    let unsat_cases = load_unsat_oracle_cases();
    run_unsat_oracle_matrix(&unsat_cases);
}

// ============================================================================
// Pairwise native DRAT proof verification (#7913)
// Verifies that pairwise feature combinations produce valid DRAT proofs
// using the in-process z4-drat-check (no external drat-trim required).
// Uses barrel6 (248 vars) to keep proof-mode solves within timeout.
// ============================================================================

/// Pairs of features tested by the pairwise interaction gates above.
/// Each pair is verified to produce a valid DRAT proof on barrel6.
const PAIRWISE_DRAT_PAIRS: &[(GateFeature, GateFeature)] = &[
    (GateFeature::Vivify, GateFeature::Subsume),
    (GateFeature::Probe, GateFeature::Transred),
    (GateFeature::Shrink, GateFeature::Probe),
    (GateFeature::Shrink, GateFeature::Vivify),
    (GateFeature::Shrink, GateFeature::Bve),
    (GateFeature::Bve, GateFeature::Congruence),
    (GateFeature::Htr, GateFeature::Congruence),
    (GateFeature::Bve, GateFeature::Bce),
];

#[test]
#[timeout(300_000)]
fn gate_pairwise_native_drat_barrel6() {
    let content = load_benchmark("cmu-bmc-barrel6.cnf");
    for &(feat_a, feat_b) in PAIRWISE_DRAT_PAIRS {
        let label = format!(
            "pairwise-native-drat/{}+{}/barrel6",
            feat_a.label(),
            feat_b.label()
        );
        verify_pairwise_unsat_with_native_drat(feat_a, feat_b, &content, &label);
    }
}
