// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for `check_sat_assuming` and `get_unsat_assumptions`.

use crate::api::*;

#[test]
fn test_check_sat_assuming_basic() {
    // Basic check_sat_assuming: assumptions are temporary
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);

    // Assert x >= 0 permanently
    let x_ge_0 = solver.ge(x, zero);
    solver.assert_term(x_ge_0);

    // SAT without assumptions
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    // Check with assumption x < 0 - should be UNSAT
    let x_lt_0 = solver.lt(x, zero);
    assert_eq!(solver.check_sat_assuming(&[x_lt_0]), SolveResult::Unsat);

    // SAT again - assumption was temporary
    let x_eq_1 = solver.eq(x, one);
    solver.assert_term(x_eq_1);
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_check_sat_assuming_multiple() {
    // Multiple assumptions at once
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);

    // No permanent assertions
    // Check with assumptions: x = 1, y = 0
    let x_eq_1 = solver.eq(x, one);
    let y_eq_0 = solver.eq(y, zero);

    assert_eq!(
        solver.check_sat_assuming(&[x_eq_1, y_eq_0]),
        SolveResult::Sat
    );

    // Now check with conflicting assumptions: x > 0, x < 0
    let x_gt_0 = solver.gt(x, zero);
    let x_lt_0 = solver.lt(x, zero);

    assert_eq!(
        solver.check_sat_assuming(&[x_gt_0, x_lt_0]),
        SolveResult::Unsat
    );
}

#[test]
fn test_get_unsat_assumptions() {
    // get_unsat_assumptions returns assumptions after UNSAT
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);

    // Assert x = 0 permanently
    let x_eq_0 = solver.eq(x, zero);
    solver.assert_term(x_eq_0);

    // Check with assumption x = 1 - should be UNSAT
    let x_eq_1 = solver.eq(x, one);
    let result = solver.check_sat_assuming(&[x_eq_1]);
    assert_eq!(result, SolveResult::Unsat);

    // get_unsat_assumptions should return the conflicting assumptions
    let unsat_assumptions = solver.get_unsat_assumptions();
    assert!(unsat_assumptions.is_some());
    // Current implementation returns all assumptions
    assert_eq!(unsat_assumptions.unwrap().len(), 1);
}

#[test]
fn test_get_unsat_assumptions_none_when_sat() {
    // get_unsat_assumptions returns None when last result was SAT
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);

    // Check with assumption x >= 0 - should be SAT
    let x_ge_0 = solver.ge(x, zero);
    let result = solver.check_sat_assuming(&[x_ge_0]);
    assert_eq!(result, SolveResult::Sat);

    // get_unsat_assumptions should return None
    assert!(solver.get_unsat_assumptions().is_none());
}

#[test]
fn test_check_sat_assuming_preserves_permanent() {
    // Assumptions don't affect permanent assertions
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let ten = solver.int_const(10);

    // Assert 0 <= x <= 10 permanently
    let x_ge_0 = solver.ge(x, zero);
    let x_le_10 = solver.le(x, ten);
    solver.assert_term(x_ge_0);
    solver.assert_term(x_le_10);

    // Make check-sat-assuming with conflicting assumption
    let minus_one = solver.int_const(-1);
    let x_lt_minus = solver.lt(x, minus_one);
    assert_eq!(solver.check_sat_assuming(&[x_lt_minus]), SolveResult::Unsat);

    // Original constraints still hold
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    // Model should be in [0, 10]
    let model = solver.get_model().expect("Expected model").into_inner();
    let x_val = model.get_int_i64("x").expect("x should be in model");
    assert!((0..=10).contains(&x_val));
}

#[test]
fn test_check_sat_assuming_empty_assumptions() {
    // check_sat_assuming with empty assumptions behaves like check_sat
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);

    // x >= 0 AND x <= 1 is SAT
    let x_ge_0 = solver.ge(x, zero);
    let x_le_1 = solver.le(x, one);
    solver.assert_term(x_ge_0);
    solver.assert_term(x_le_1);

    // Empty assumptions should return SAT like check_sat
    assert_eq!(solver.check_sat_assuming(&[]), SolveResult::Sat);
}

#[test]
fn test_check_sat_assuming_auflia_integer_split_cleanup_6689() {
    // AUFLIA check_sat_assuming must isolate split clauses and temporary theory
    // state so an UNSAT assumption-only split does not leak into the next solve.
    let mut solver = Solver::new(Logic::QfAuflia);

    let arr = solver.declare_const("arr", Sort::array(Sort::Int, Sort::Int));
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let forty_two = solver.int_const(42);

    let read0 = solver.select(arr, zero);
    let base_eq = solver.eq(read0, forty_two);
    solver.assert_term(base_eq);

    let two_x = solver.mul(two, x);
    let split_trigger = solver.eq(two_x, one);
    assert_eq!(
        solver.check_sat_assuming(&[split_trigger]),
        SolveResult::Unsat,
        "assumption-only AUFLIA integer split should be UNSAT"
    );

    assert_eq!(
        solver.check_sat_assuming(&[]),
        SolveResult::Sat,
        "empty AUFLIA assumptions after UNSAT should remain SAT"
    );
}

#[test]
fn test_get_unsat_assumptions_cleared_by_check_sat() {
    // get_unsat_assumptions is cleared when check_sat() is called
    // (to prevent returning stale assumptions)
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let neg_one = solver.int_const(-1);

    // First: check_sat_assuming with UNSAT result
    let x_gt_0 = solver.gt(x, zero);
    let x_lt_0 = solver.lt(x, zero);
    assert_eq!(
        solver.check_sat_assuming(&[x_gt_0, x_lt_0]),
        SolveResult::Unsat
    );
    // Assumptions are available
    assert!(solver.get_unsat_assumptions().is_some());

    // Now call regular check_sat with different constraints
    let x_gt_neg = solver.gt(x, neg_one);
    solver.assert_term(x_gt_neg);
    let x_lt_one = solver.lt(x, one);
    solver.assert_term(x_lt_one);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    // Assumptions should be cleared - get_unsat_assumptions returns None
    // (even if we made it UNSAT, the assumptions from before shouldn't be returned)
    assert!(
        solver.get_unsat_assumptions().is_none(),
        "get_unsat_assumptions should return None after check_sat()"
    );
}
