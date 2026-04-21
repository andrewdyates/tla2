// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use z4_sat::{
    ExtCheckResult, ExtPropagateResult, Extension, Solver, SolverContext, TheoryPropResult,
};

struct NoopExtension;

impl Extension for NoopExtension {
    fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
        ExtPropagateResult::none()
    }

    fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
        ExtCheckResult::Sat
    }

    fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
        false
    }
}

/// solve_with_theory now supports scoped solving via assumption-based loop (#3343).
/// Verify it returns a result instead of panicking.
#[test]
fn test_solve_with_theory_works_when_scoped_solving_is_active() {
    let mut solver: Solver = Solver::new(1);
    solver.push();
    let result = solver
        .solve_with_theory(|_| TheoryPropResult::Continue)
        .into_inner();
    // Should return SAT or UNSAT, not panic.
    assert!(
        matches!(result, z4_sat::SatResult::Sat(_) | z4_sat::SatResult::Unsat),
        "solve_with_theory under scope should produce a definite result, got: {result:?}",
    );
}

/// In debug builds, solve_with_extension panics when scoped solving is active.
/// In release builds, it returns Unknown (fail-closed).
#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "solve_with_extension() with non-empty scope_selectors is not supported")]
fn test_solve_with_extension_panics_when_scoped_solving_is_active() {
    let mut solver: Solver = Solver::new(1);
    solver.push();
    let mut ext = NoopExtension;
    let _ = solver.solve_with_extension(&mut ext).into_inner();
}

/// In release builds, solve_with_extension returns Unknown for scoped solving.
#[test]
#[cfg(not(debug_assertions))]
fn test_solve_with_extension_returns_unknown_when_scoped_solving_is_active() {
    let mut solver: Solver = Solver::new(1);
    solver.push();
    let mut ext = NoopExtension;
    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert!(
        matches!(result, z4_sat::SatResult::Unknown),
        "solve_with_extension under scope should return Unknown in release, got: {result:?}",
    );
}
