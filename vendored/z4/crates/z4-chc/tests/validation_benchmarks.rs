// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Validation tests for CHC results (#429)
//!
//! This module ensures that Z4 validates every SAT/UNSAT result against the
//! original clauses. Validation failures return Unknown instead of wrong answers.
//!
//! Done criteria for #429:
//! 1. Z4 validates every SAT/UNSAT result in extra-small-lia benchmark set
//! 2. Any validation failure returns Unknown instead of wrong answer
//! 3. #421 soundness bug would have been caught by validation

use ntest::timeout;
use z4_chc::{testing, PdrConfig};

// NOTE: test_validation_extra_small_lia deleted - required benchmark files (#596)
// To run validation tests, set up benchmarks/chc-comp/2025/extra-small-lia/

/// Test that validation catches the #421 soundness bug pattern
///
/// Issue #421: PDKIND returned Unsafe on a Safe benchmark (dillig01.c_000.smt2).
/// The portfolio validation now catches such bugs by validating counterexamples.
///
/// This test creates a mock scenario where an engine produces an invalid result
/// and verifies that validation rejects it.
///
/// Timeout: 1s (measured <10ms)
#[test]
#[timeout(1_000)]
fn test_validation_catches_invalid_counterexample() {
    use z4_chc::{CexVerificationResult, Counterexample, CounterexampleStep};
    use z4_chc::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

    // Build a simple safe problem: x >= 0 => Inv(x), Inv(x) => Inv(x+1), Inv(x) AND x < 0 => false
    // This is SAFE because x starts >= 0 and only increases.
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    // Init: x >= 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Transition: Inv(x) AND x_next = x + 1 => Inv(x_next)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(x_next.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x_next)]),
    ));

    // Query: Inv(x) AND x < 0 => false (unreachable!)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    // Create a PDR solver for verification
    let mut solver = testing::new_pdr_solver(problem.clone(), PdrConfig::default());

    // Create a FAKE counterexample claiming x = -1 reaches the bad state
    // This is INVALID because x starts >= 0 and only increases
    let fake_cex = Counterexample::new(vec![CounterexampleStep::new(
        inv,
        [("x".to_string(), -1)].into_iter().collect(),
    )]);

    // Verification should REJECT this fake counterexample
    let result = solver.verify_counterexample(&fake_cex);
    assert!(
        matches!(result, CexVerificationResult::Spurious),
        "Validation should reject fake counterexample with x = -1 \
         (not reachable from init where x >= 0), got {result:?}"
    );
}

/// Test that valid models pass verification
///
/// Timeout: 1s (measured <10ms)
#[test]
#[timeout(1_000)]
fn test_validation_accepts_valid_model() {
    use z4_chc::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
    use z4_chc::{InvariantModel, PdrConfig, PredicateInterpretation};

    // Same safe problem as above
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    // Init: x >= 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Transition: Inv(x) AND x_next = x + 1 => Inv(x_next)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(x_next.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x_next)]),
    ));

    // Query: Inv(x) AND x < 0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let mut solver = testing::new_pdr_solver(problem.clone(), PdrConfig::default());

    // Create a VALID model: Inv(x) iff x >= 0
    // This is inductive and blocks the bad state (x < 0)
    let mut model = InvariantModel::new();
    let inv_var = ChcVar::new(format!("__p{}_a0", inv.index()), ChcSort::Int);
    model.set(
        inv,
        PredicateInterpretation::new(
            vec![inv_var.clone()],
            ChcExpr::ge(ChcExpr::var(inv_var), ChcExpr::int(0)),
        ),
    );

    // Verification should ACCEPT this valid model
    let is_valid = solver.verify_model(&model);
    assert!(
        is_valid,
        "Validation should accept valid model Inv(x) = (x >= 0)"
    );
}

/// Test that invalid models are rejected
///
/// Timeout: 1s (measured <10ms)
#[test]
#[timeout(1_000)]
fn test_validation_rejects_invalid_model() {
    use z4_chc::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
    use z4_chc::{InvariantModel, PdrConfig, PredicateInterpretation};

    // Build a problem where x grows unboundedly
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    // Init: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Transition: Inv(x) AND x_next = x + 1 => Inv(x_next)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(x_next.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x_next)]),
    ));

    // Query: Inv(x) AND x >= 10 => false (reachable after 10 steps!)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    let mut solver = testing::new_pdr_solver(problem.clone(), PdrConfig::default());

    // Create an INVALID model: Inv(x) iff x >= 0
    // This is inductive but DOES NOT block the bad state (x >= 10 is reachable)
    let mut model = InvariantModel::new();
    let inv_var = ChcVar::new(format!("__p{}_a0", inv.index()), ChcSort::Int);
    model.set(
        inv,
        PredicateInterpretation::new(
            vec![inv_var.clone()],
            ChcExpr::ge(ChcExpr::var(inv_var), ChcExpr::int(0)),
        ),
    );

    // Verification should REJECT this model (doesn't block bad states)
    let is_valid = solver.verify_model(&model);
    assert!(
        !is_valid,
        "Validation should reject model Inv(x) = (x >= 0) that doesn't block x >= 10"
    );
}
