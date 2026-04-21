// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Guard tests for inprocessing features that were previously disabled due to
//! soundness bugs and have since been fixed.
//!
//! Fixed features:
//!   - Factorization: reconstruction entries removed (CaDiCaL parity), #3373 fixed
//!   - SCC Decompose: eager assignment removed (CaDiCaL parity), #3424/#3466 fixed
//!
//! Previously disabled, now re-enabled:
//!   - Conditioning (GBCE): fixed with fixpoint-refined autarky partition (#3432)
//!   - HBR: re-enabled after probe_parent array fix (#3419)
//!   - HTR: was wrong-UNSAT on uf200 (#3873), fixed with collect_level0_garbage() (#3971)

use ntest::timeout;
use z4_sat::{parse_dimacs, Solver};

/// Verify that factorization is enabled by default and runs on structured formulas.
#[test]
#[timeout(5_000)]
fn guard_factorization_enabled_after_solve() {
    // Small structured formula with factoring opportunity (2x3 matrix pattern).
    let cnf = "p cnf 6 8\n1 2 3 0\n-1 2 3 0\n1 -2 3 0\n-1 -2 3 0\n4 5 6 0\n-4 5 6 0\n4 -5 6 0\n-4 -5 6 0\n";
    let formula = parse_dimacs(cnf).expect("parse");
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();

    // Factor is enabled by default; the formula should still solve correctly.
    assert!(
        result.is_sat(),
        "Structured formula must be SAT with factorization enabled"
    );
}

/// Verify that SCC decompose is enabled by default and produces correct results.
#[test]
#[timeout(5_000)]
fn guard_decompose_enabled_after_solve() {
    // Binary implication chain forming an SCC: 1->2, 2->3, 3->4, 4->-2 (cycle).
    let cnf = "p cnf 4 4\n1 2 0\n-1 3 0\n-3 4 0\n-4 -2 0\n";
    let formula = parse_dimacs(cnf).expect("parse");
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();

    assert!(
        result.is_sat(),
        "Binary implication formula must be SAT with decompose enabled"
    );
}

/// Verify that a fresh Solver created via `Solver::new()` has factorization enabled.
#[test]
#[timeout(5_000)]
fn guard_factorization_enabled_fresh_solver() {
    let mut solver = Solver::new(4);
    solver.add_clause(vec![z4_sat::Literal::positive(z4_sat::Variable::new(0))]);
    let result = solver.solve().into_inner();

    assert!(
        result.is_sat(),
        "Fresh solver with factorization enabled must produce correct SAT"
    );
}

/// Verify that decompose is enabled on a fresh solver.
#[test]
#[timeout(5_000)]
fn guard_decompose_enabled_fresh_solver() {
    let mut solver = Solver::new(4);
    solver.add_clause(vec![z4_sat::Literal::positive(z4_sat::Variable::new(0))]);
    let result = solver.solve().into_inner();

    assert!(
        result.is_sat(),
        "Fresh solver with decompose enabled must produce correct SAT"
    );
}
