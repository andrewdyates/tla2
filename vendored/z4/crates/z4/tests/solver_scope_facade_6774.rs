// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(deprecated)]

//! Stable facade regression tests for `SolverScope` (#6774).
//!
//! Verifies that `SolverScope` is reachable from all three stable import
//! surfaces (`z4::SolverScope`, `z4::api::SolverScope`, `z4::prelude::*`)
//! and that scoped assertions are automatically popped on guard drop.

/// Test that `SolverScope` is accessible through `z4::api` and works
/// as an RAII scope guard for temporary assertions.
#[test]
fn test_solver_scope_via_api_module() {
    use z4::api::{Logic, Solver, SolverScope, Sort};

    let mut solver = Solver::try_new(Logic::QfLia).expect("solver creation");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);

    // Base assertion: x > 0
    let x_gt_zero = solver.gt(x, zero);
    solver.assert_term(x_gt_zero);
    assert!(solver.check_sat().is_sat(), "base should be SAT");

    // Scoped assertion: x < 0 (contradicts base -> UNSAT inside scope)
    {
        let mut scope = SolverScope::new(&mut solver).expect("push");
        let x_lt_zero = scope.lt(x, zero);
        scope.assert_term(x_lt_zero);
        assert!(
            scope.check_sat().is_unsat(),
            "scoped contradiction should be UNSAT"
        );
        // guard drops here -> automatic pop
    }

    // After scope drop, base is restored
    assert!(
        solver.check_sat().is_sat(),
        "base should still be SAT after scope drop"
    );
}

/// Test that `SolverScope` is accessible through `z4::prelude::*`.
#[test]
fn test_solver_scope_via_prelude() {
    use z4::prelude::*;

    let mut solver = Solver::try_new(Logic::QfLia).expect("solver creation");
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let ten = solver.int_const(10);

    // Base: x > 5
    let x_gt_five = solver.gt(x, five);
    solver.assert_term(x_gt_five);

    // Scoped: x < 10 -> SAT inside scope (5 < x < 10)
    {
        let mut scope = SolverScope::new(&mut solver).expect("push");
        let x_lt_ten = scope.lt(x, ten);
        scope.assert_term(x_lt_ten);
        assert!(scope.check_sat().is_sat(), "5 < x < 10 should be SAT");
    }

    // After scope: only x > 5 remains
    assert!(
        solver.check_sat().is_sat(),
        "x > 5 should still be SAT after scope drop"
    );
}

/// Test that `SolverScope` is accessible through the root `z4` crate.
#[test]
fn test_solver_scope_via_root() {
    // Verify the type is accessible at z4::SolverScope (root re-export)
    // by constructing one through the root import path
    let mut solver = z4::Solver::try_new(z4::Logic::QfLia).expect("solver creation");
    {
        let _scope = z4::SolverScope::new(&mut solver).expect("push via root import");
        // scope drops here -> automatic pop
    }
    // Solver still usable after scope drop
    assert!(solver.check_sat().is_sat(), "empty solver should be SAT");
}
