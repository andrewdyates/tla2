// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::dimacs::parse_str;
use crate::features::SatFeatures;
use crate::literal::{Literal, Variable};

#[test]
fn test_portfolio_sat_simple() {
    let cnf = "p cnf 3 2\n1 2 0\n-1 3 0\n";
    let formula = parse_str(cnf).expect("valid DIMACS");

    let portfolio = PortfolioSolver::new(2);
    let result = portfolio.solve(&formula);

    assert!(matches!(result, SatResult::Sat(_)));
}

#[test]
fn test_portfolio_unsat_simple() {
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let formula = parse_str(cnf).expect("valid DIMACS");

    let portfolio = PortfolioSolver::new(2);
    let result = portfolio.solve(&formula);

    assert_eq!(result, SatResult::Unsat);
}

#[test]
fn test_portfolio_strategies() {
    let strategies = Strategy::all();
    assert_eq!(strategies.len(), 6);

    // BVE enabled in general-purpose and BVE-focused strategies
    assert!(Strategy::VsidsLuby.to_config().bve_enabled);
    assert!(Strategy::VsidsGlucose.to_config().bve_enabled);
    assert!(Strategy::AggressiveInprocessing.to_config().bve_enabled);
    assert!(Strategy::BveFocused.to_config().bve_enabled);
    // BVE disabled in conservative and probe-focused strategies
    assert!(!Strategy::Conservative.to_config().bve_enabled);
    assert!(!Strategy::ProbeFocused.to_config().bve_enabled);

    // Factorization enabled in general-purpose strategies (reconstruction removed, #3373 fixed)
    assert!(Strategy::VsidsLuby.to_config().factor_enabled);
    assert!(Strategy::VsidsGlucose.to_config().factor_enabled);
    assert!(Strategy::AggressiveInprocessing.to_config().factor_enabled);
    assert!(Strategy::BveFocused.to_config().factor_enabled);

    // #3900: conditioning and congruence disabled in Conservative
    let conservative = Strategy::Conservative.to_config();
    assert!(!conservative.condition_enabled);
    assert!(!conservative.congruence_enabled);
    assert!(!conservative.transred_enabled);
    assert!(!conservative.decompose_enabled);
    assert!(!conservative.hbr_enabled);
    // Conditioning and congruence enabled in general-purpose strategies
    assert!(Strategy::VsidsLuby.to_config().condition_enabled);
    assert!(Strategy::VsidsGlucose.to_config().congruence_enabled);
    assert!(Strategy::VsidsLuby.to_config().transred_enabled);
    assert!(Strategy::VsidsGlucose.to_config().decompose_enabled);
    assert!(
        Strategy::AggressiveInprocessing
            .to_config()
            .condition_enabled
    );
    assert!(
        Strategy::AggressiveInprocessing
            .to_config()
            .congruence_enabled
    );

    let probe_focused = Strategy::ProbeFocused.to_config();
    assert!(probe_focused.probe_enabled);
    assert!(probe_focused.subsume_enabled);
    assert!(probe_focused.hbr_enabled);
    assert!(!probe_focused.transred_enabled);
    assert!(!probe_focused.decompose_enabled);

    let bve_focused = Strategy::BveFocused.to_config();
    assert!(bve_focused.bve_enabled);
    assert!(bve_focused.gate_enabled);
    assert!(bve_focused.condition_enabled);
    assert!(!bve_focused.transred_enabled);
    assert!(!bve_focused.decompose_enabled);
}

#[test]
fn test_portfolio_recommended_threads() {
    // 1 thread should give 1 strategy
    let s1 = Strategy::recommended(1);
    assert_eq!(s1.len(), 1);

    // 4 threads should give 4 strategies
    let s4 = Strategy::recommended(4);
    assert_eq!(s4.len(), 4);

    // 8 threads should give 8 strategies (with duplicates)
    let s8 = Strategy::recommended(8);
    assert_eq!(s8.len(), 8);
}

#[test]
fn test_portfolio_single_thread_fallback() {
    let cnf = "p cnf 3 3\n1 2 0\n-1 2 0\n-2 3 0\n";
    let formula = parse_str(cnf).expect("valid DIMACS");

    // Single thread should work
    let portfolio = PortfolioSolver::new(1);
    let result = portfolio.solve(&formula);

    assert!(matches!(result, SatResult::Sat(_)));
}

#[test]
fn test_portfolio_with_custom_config() {
    let cnf = "p cnf 2 2\n1 2 0\n-1 -2 0\n";
    let formula = parse_str(cnf).expect("valid DIMACS");

    let config = SolverConfig {
        glucose_restarts: false,
        chrono_enabled: false,
        vivify_enabled: false,
        subsume_enabled: false,
        probe_enabled: false,
        bve_enabled: false,
        bce_enabled: false,
        htr_enabled: false,
        gate_enabled: false,
        sweep_enabled: false,
        transred_enabled: false,
        factor_enabled: false,
        condition_enabled: false,
        congruence_enabled: false,
        decompose_enabled: false,
        hbr_enabled: false,
        initial_phase: Some(true),
        branch_selector_ucb1: false,
        seed: 42,
    };

    let portfolio = PortfolioSolver::new(1).with_configs(vec![config]);
    let result = portfolio.solve(&formula);

    assert!(matches!(result, SatResult::Sat(_)));
}

// --- Instance-aware algorithm selection tests ---

fn pos(v: u32) -> Literal {
    Literal::positive(Variable(v))
}

fn neg(v: u32) -> Literal {
    Literal::negative(Variable(v))
}

#[test]
fn test_algo_select_random3sat_prioritizes_bve() {
    // Build a random-3-SAT-like feature profile.
    let num_vars = 2000;
    let clauses: Vec<Vec<Literal>> = (0..8000)
        .map(|i| {
            let v0 = (i * 3) as u32 % num_vars as u32;
            let v1 = (i * 3 + 1) as u32 % num_vars as u32;
            let v2 = (i * 3 + 2) as u32 % num_vars as u32;
            vec![pos(v0), neg(v1), pos(v2)]
        })
        .collect();
    let features = SatFeatures::extract(num_vars, &clauses);
    let strategies = Strategy::recommended_for_instance(1, &features);
    assert_eq!(strategies[0], Strategy::BveFocused);
}

#[test]
fn test_algo_select_structured_prioritizes_aggressive() {
    // Mostly binary clauses -> structured instance.
    let num_vars = 2000;
    let clauses: Vec<Vec<Literal>> = (0..4000)
        .map(|i| {
            let v0 = (i * 2) as u32 % num_vars as u32;
            let v1 = (i * 2 + 1) as u32 % num_vars as u32;
            vec![pos(v0), neg(v1)]
        })
        .collect();
    let features = SatFeatures::extract(num_vars, &clauses);
    let strategies = Strategy::recommended_for_instance(1, &features);
    assert_eq!(strategies[0], Strategy::AggressiveInprocessing);
}

#[test]
fn test_algo_select_industrial_prioritizes_glucose() {
    // Very large formula with heterogeneous clause sizes -> industrial classification.
    let num_vars = 100_000;
    let clauses: Vec<Vec<Literal>> = (0..300_000)
        .map(|i| {
            let base_v = (i * 5) as u32 % num_vars as u32;
            // Vary clause length: 2-8 based on index for structural heterogeneity.
            let len = 2 + (i % 7);
            (0..len)
                .map(|j| {
                    let v = (base_v + j as u32) % num_vars as u32;
                    if j % 2 == 0 { pos(v) } else { neg(v) }
                })
                .collect()
        })
        .collect();
    let features = SatFeatures::extract(num_vars, &clauses);
    let strategies = Strategy::recommended_for_instance(1, &features);
    assert_eq!(strategies[0], Strategy::VsidsGlucose);
}

#[test]
fn test_algo_select_small_prioritizes_glucose() {
    // Small formula -> VsidsGlucose (fast default).
    let clauses = vec![vec![pos(0), neg(1)], vec![pos(1), neg(2)]];
    let features = SatFeatures::extract(3, &clauses);
    let strategies = Strategy::recommended_for_instance(1, &features);
    assert_eq!(strategies[0], Strategy::VsidsGlucose);
}

#[test]
fn test_algo_select_thread_count_respected() {
    // Any features, verify thread count is respected.
    let clauses = vec![vec![pos(0), neg(1)]];
    let features = SatFeatures::extract(2, &clauses);

    let s1 = Strategy::recommended_for_instance(1, &features);
    assert_eq!(s1.len(), 1);

    let s4 = Strategy::recommended_for_instance(4, &features);
    assert_eq!(s4.len(), 4);

    let s8 = Strategy::recommended_for_instance(8, &features);
    assert_eq!(s8.len(), 8);
}

#[test]
fn test_algo_select_adaptive_portfolio_sat() {
    // Verify adaptive portfolio produces correct SAT result.
    let cnf = "p cnf 3 2\n1 2 0\n-1 3 0\n";
    let formula = parse_str(cnf).expect("valid DIMACS");
    let portfolio = PortfolioSolver::new_adaptive(2, &formula);
    let result = portfolio.solve(&formula);
    assert!(matches!(result, SatResult::Sat(_)));
}

#[test]
fn test_algo_select_adaptive_portfolio_unsat() {
    // Verify adaptive portfolio produces correct UNSAT result.
    let cnf = "p cnf 1 2\n1 0\n-1 0\n";
    let formula = parse_str(cnf).expect("valid DIMACS");
    let portfolio = PortfolioSolver::new_adaptive(2, &formula);
    let result = portfolio.solve(&formula);
    assert_eq!(result, SatResult::Unsat);
}
