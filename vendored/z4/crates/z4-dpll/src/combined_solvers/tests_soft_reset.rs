// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #3510: soft_reset must delegate to sub-solver
//! soft_reset() (not reset()) in combined solvers.

use super::combiner::TheoryCombiner;
use super::*;
use num_bigint::BigInt;
use z4_core::{Sort, TermStore, TheoryResult, TheorySolver};

fn setup_term_store() -> TermStore {
    TermStore::new()
}

/// Regression test: TheoryCombiner::uf_lia soft_reset clears conflict state (#3510).
///
/// Before the fix, combined solvers used the default TheorySolver::soft_reset
/// which calls reset(). After the fix, soft_reset delegates to each sub-solver's
/// soft_reset, which preserves learned state while clearing assertion state.
#[test]
fn test_uf_lia_solver_soft_reset_clears_conflict_state() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let neg1 = terms.mk_int(BigInt::from(-1));
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_neg1 = terms.mk_le(x, neg1);
    let x_eq_1 = terms.mk_eq(x, one);

    let mut solver = TheoryCombiner::uf_lia(&terms);
    solver.register_atom(x_ge_0);
    solver.register_atom(x_le_neg1);
    solver.register_atom(x_eq_1);

    // Round 1: assert contradiction (x >= 0 AND x <= -1)
    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(x_le_neg1, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "expected contradiction before soft_reset, got {result:?}"
    );

    // soft_reset should clear the contradiction
    solver.soft_reset();

    // Round 2: assert a consistent formula (x = 1)
    solver.assert_literal(x_eq_1, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "soft_reset should clear TheoryCombiner(UFLIA) assertion state, got {result:?}"
    );
}

/// Regression test: TheoryCombiner::auf_lia soft_reset clears conflict state (#3510).
#[test]
fn test_auf_lia_solver_soft_reset_clears_conflict_state() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let neg1 = terms.mk_int(BigInt::from(-1));
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_neg1 = terms.mk_le(x, neg1);
    let x_eq_1 = terms.mk_eq(x, one);

    let mut solver = TheoryCombiner::auf_lia(&terms);
    solver.register_atom(x_ge_0);
    solver.register_atom(x_le_neg1);
    solver.register_atom(x_eq_1);

    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(x_le_neg1, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "expected contradiction before soft_reset, got {result:?}"
    );

    solver.soft_reset();

    solver.assert_literal(x_eq_1, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "soft_reset should clear TheoryCombiner(AUFLIA) assertion state, got {result:?}"
    );
}

/// Regression test: LiraSolver::soft_reset clears conflict state (#3510).
#[test]
fn test_lira_solver_soft_reset_clears_conflict_state() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let neg1 = terms.mk_int(BigInt::from(-1));
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_neg1 = terms.mk_le(x, neg1);
    let x_eq_1 = terms.mk_eq(x, one);

    let mut solver = LiraSolver::new(&terms);
    solver.register_atom(x_ge_0);
    solver.register_atom(x_le_neg1);
    solver.register_atom(x_eq_1);

    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(x_le_neg1, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "expected contradiction before soft_reset, got {result:?}"
    );

    solver.soft_reset();

    solver.assert_literal(x_eq_1, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "soft_reset should clear LiraSolver assertion state, got {result:?}"
    );
}

/// Regression test: StringsLiaSolver::soft_reset clears conflict state (#3510).
#[test]
fn test_strings_lia_solver_soft_reset_clears_conflict_state() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let neg1 = terms.mk_int(BigInt::from(-1));
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_neg1 = terms.mk_le(x, neg1);
    let x_eq_1 = terms.mk_eq(x, one);

    let mut solver = StringsLiaSolver::new(&terms);
    solver.register_atom(x_ge_0);
    solver.register_atom(x_le_neg1);
    solver.register_atom(x_eq_1);

    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(x_le_neg1, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "expected contradiction before soft_reset, got {result:?}"
    );

    solver.soft_reset();

    solver.assert_literal(x_eq_1, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "soft_reset should clear StringsLiaSolver assertion state, got {result:?}"
    );
}
