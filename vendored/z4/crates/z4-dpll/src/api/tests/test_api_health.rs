// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! API-health regressions for error visibility and fallible comparison parity.

use crate::api::*;

#[test]
#[should_panic(
    expected = "sort mismatch in lt: expected same arithmetic sort (Int,Int) or (Real,Real), got Bool, Bool"
)]
fn test_lt_panics_on_non_arithmetic_sort() {
    let mut solver = Solver::new(Logic::QfLia);
    let p = solver.declare_const("p", Sort::Bool);
    let q = solver.declare_const("q", Sort::Bool);

    let _ = solver.lt(p, q);
}

#[test]
#[should_panic(
    expected = "sort mismatch in ge: expected same arithmetic sort (Int,Int) or (Real,Real), got Int, Real"
)]
fn test_ge_panics_on_mixed_int_real() {
    let mut solver = Solver::new(Logic::QfLira);
    let i = solver.declare_const("i", Sort::Int);
    let r = solver.declare_const("r", Sort::Real);

    let _ = solver.ge(i, r);
}

#[test]
fn test_check_sat_assuming_records_internal_error_for_non_bool_assumption() {
    use crate::UnknownReason;

    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);

    let result = solver.check_sat_assuming(&[x]);
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(
        solver.get_unknown_reason(),
        Some(UnknownReason::InternalError)
    );
    assert_eq!(
        solver.get_reason_unknown().as_deref(),
        Some("internal-error")
    );
    // The executor error detail is preserved (#4663)
    assert!(solver.get_executor_error().is_some());
}

#[test]
fn test_unknown_reason_clears_after_successful_solve_and_reset() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);

    let first = solver.check_sat_assuming(&[x]);
    assert_eq!(first, SolveResult::Unknown);
    assert!(solver.get_unknown_reason().is_some());

    let zero = solver.int_const(0);
    let x_ge_0 = solver.ge(x, zero);
    let second = solver.check_sat_assuming(&[x_ge_0]);
    assert_eq!(second, SolveResult::Sat);
    assert!(solver.get_unknown_reason().is_none());

    let _ = solver.check_sat_assuming(&[x]);
    assert!(solver.get_unknown_reason().is_some());
    solver.reset();
    assert!(solver.get_unknown_reason().is_none());
}
