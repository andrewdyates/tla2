// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]

use super::*;
use crate::{ChcOp, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

fn make_high_arity_transition_problem(arity: usize) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int; arity]);

    let fact_args: Vec<ChcExpr> = (0..arity)
        .map(|i| ChcExpr::add(ChcExpr::int(i as i64), ChcExpr::int(1)))
        .collect();
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(inv, fact_args),
    ));

    let body_vars: Vec<ChcVar> = (0..arity)
        .map(|i| ChcVar::new(format!("x{i}"), ChcSort::Int))
        .collect();
    let body_args: Vec<ChcExpr> = body_vars.iter().cloned().map(ChcExpr::var).collect();
    let head_args: Vec<ChcExpr> = body_vars
        .iter()
        .map(|v| ChcExpr::add(ChcExpr::var(v.clone()), ChcExpr::int(1)))
        .collect();
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, body_args)]),
        ClauseHead::Predicate(inv, head_args),
    ));

    let query_args: Vec<ChcExpr> = (0..arity)
        .map(|i| ChcExpr::add(ChcExpr::int(i as i64), ChcExpr::int(2)))
        .collect();
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        inv, query_args,
    )])));

    problem
}

fn assert_flat_and_arity(expr: &ChcExpr, expected_arity: usize, label: &str) {
    let args = match expr {
        ChcExpr::Op(ChcOp::And, args) => args,
        other => panic!("{label} should be an n-ary And, got {other:?}"),
    };

    assert_eq!(
        args.len(),
        expected_arity,
        "{label} conjunction arity mismatch"
    );
    assert!(
        args.iter()
            .all(|arg| !matches!(arg.as_ref(), ChcExpr::Op(ChcOp::And, _))),
        "{label} should not contain nested And nodes"
    );
}

#[test]
fn test_simple_counter() {
    // Counter from 0 to 5:
    // x = 0 => Inv(x)
    // Inv(x) ∧ x < 5 => Inv(x+1)
    // Inv(x) ∧ x > 5 => false
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) ∧ x < 5 => Inv(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) ∧ x > 5 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    let config = KindConfig::with_engine_config(
        10,
        std::time::Duration::from_secs(1),
        std::time::Duration::from_secs(10),
        false,
        None,
    );
    let mut solver = KindSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, KindResult::Safe(_)),
        "Expected Safe for bounded safe counter (x in [0,5], query x > 5), got {result:?}"
    );
}

#[test]
fn test_unsafe_counter() {
    // Counter that can reach x > 5:
    // x = 0 => Inv(x)
    // Inv(x) => Inv(x+1)  (no guard!)
    // Inv(x) ∧ x > 5 => false
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) => Inv(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) ∧ x > 5 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    let config = KindConfig::with_engine_config(
        10,
        std::time::Duration::from_secs(1),
        std::time::Duration::from_secs(10),
        false,
        None,
    );
    let mut solver = KindSolver::new(problem, config);
    let result = solver.solve();

    match result {
        KindResult::Unsafe(cex) => {
            let k = cex.steps.len().saturating_sub(1);
            println!("Unsafe at k = {k}");
            assert!(k <= 6, "Should find counterexample at k <= 6");
        }
        other => {
            panic!("Expected Unsafe, got {other:?}");
        }
    }
}

/// Regression test for #3022: k-induction must not accept an induction step
/// as proof of safety when any base case returned Unknown (timeout).
/// The safe counter is provable at k=0, but with a near-zero query timeout
/// the base case returns Unknown, so the guard must suppress the Safe result.
#[test]
fn test_kind_guard_suppresses_safe_on_unknown_base_case() {
    // Same safe counter problem as test_simple_counter
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) ∧ x < 5 => Inv(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) ∧ x > 5 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    // Use a near-zero query timeout to force base case Unknown
    let config = KindConfig::with_engine_config(
        10,
        std::time::Duration::from_nanos(1), // Force Unknown on base case
        std::time::Duration::from_secs(10),
        false,
        None,
    );
    let mut solver = KindSolver::new(problem, config);
    let result = solver.solve();

    // The guard must prevent Safe — result should be Unknown or NotApplicable
    assert!(
        !matches!(result, KindResult::Safe(_)),
        "Kind must not return Safe when base cases are Unknown (#3022). Got: {result:?}"
    );
}

#[test]
fn test_extract_transition_system_high_arity_conjunctions_flat_and_drop_safe() {
    // #2508: extraction should build flat conjunctions even for large predicate arity.
    const ARITY: usize = 4_096;

    let problem = make_high_arity_transition_problem(ARITY);
    let ts = TransitionSystem::from_chc_problem(&problem)
        .expect("high-arity transition system should extract");

    assert_flat_and_arity(&ts.init, ARITY, "init");
    assert_flat_and_arity(&ts.transition, ARITY, "transition");

    // Exercise ownership teardown without mem::forget to guard against drop regressions.
    drop(ts);
}

#[test]
fn test_verify_invariant_init_query_rejects_bad_invariant() {
    // Counter from 0 to 5, query: x > 5.
    // A correct invariant (e.g., x <= 5) should pass init+query.
    // A bad invariant (e.g., x > 10) should FAIL init+query because
    // init (x = 0) does not imply (x > 10).
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    let config = KindConfig::with_engine_config(
        10,
        std::time::Duration::from_secs(1),
        std::time::Duration::from_secs(10),
        false,
        None,
    );
    let solver = KindSolver::new(problem.clone(), config);
    let ts = TransitionSystem::from_chc_problem(&problem).unwrap();

    // Bad invariant: x > 10 — init (x=0) does not imply x > 10
    let bad_inv = ChcExpr::gt(
        ChcExpr::var(ChcVar::new("v0", ChcSort::Int)),
        ChcExpr::int(10),
    );
    assert!(
        !solver.verify_invariant_init_query(&ts, &bad_inv),
        "verify_invariant_init_query should reject invariant 'x > 10' (init x=0 =/=> x > 10)"
    );

    // Good invariant: x <= 5 — init (x=0) implies x <= 5, and x <= 5 implies NOT(x > 5)
    let good_inv = ChcExpr::le(
        ChcExpr::var(ChcVar::new("v0", ChcSort::Int)),
        ChcExpr::int(5),
    );
    assert!(
        solver.verify_invariant_init_query(&ts, &good_inv),
        "verify_invariant_init_query should accept invariant 'x <= 5'"
    );
}

#[test]
fn test_fresh_cross_check_timeout_default_budget() {
    let problem = ChcProblem::new();
    let config = KindConfig::default();
    let solver = KindSolver::new(problem, config);
    let run_start = std::time::Instant::now();

    assert_eq!(
        solver.fresh_cross_check_timeout(run_start),
        std::time::Duration::from_secs(10)
    );
}

#[test]
fn test_fresh_cross_check_timeout_adaptive_budget() {
    let problem = ChcProblem::new();
    let config = KindConfig {
        query_timeout: std::time::Duration::from_secs(1),
        total_timeout: std::time::Duration::from_secs(3),
        ..KindConfig::default()
    };
    let solver = KindSolver::new(problem, config);
    let run_start = std::time::Instant::now();

    assert_eq!(
        solver.fresh_cross_check_timeout(run_start),
        std::time::Duration::from_secs(2)
    );
}

#[test]
fn test_fresh_cross_check_timeout_remaining_caps() {
    let problem = ChcProblem::new();
    let config = KindConfig {
        query_timeout: std::time::Duration::from_secs(1),
        total_timeout: std::time::Duration::from_secs(3),
        ..KindConfig::default()
    };
    let solver = KindSolver::new(problem, config);

    assert_eq!(
        solver.fresh_cross_check_timeout_for_remaining(std::time::Duration::from_millis(500)),
        std::time::Duration::from_millis(500)
    );
}

#[test]
fn test_fresh_cross_check_timeout_exhausted_budget_is_zero() {
    let problem = ChcProblem::new();
    let config = KindConfig {
        query_timeout: std::time::Duration::from_secs(1),
        total_timeout: std::time::Duration::from_secs(3),
        ..KindConfig::default()
    };
    let solver = KindSolver::new(problem, config);

    assert_eq!(
        solver.fresh_cross_check_timeout_for_remaining(std::time::Duration::ZERO),
        std::time::Duration::ZERO
    );
}

#[test]
fn test_fresh_check_outcome_enum() {
    let timeout = std::time::Duration::from_secs(5);

    assert_eq!(
        FreshCheckOutcome::from_smt_result(&crate::smt::SmtResult::Unsat, timeout),
        FreshCheckOutcome::ConfirmedUnsat
    );
    assert_eq!(
        FreshCheckOutcome::from_smt_result(&crate::smt::SmtResult::Unknown, timeout),
        FreshCheckOutcome::BudgetUnknown { timeout }
    );
}
