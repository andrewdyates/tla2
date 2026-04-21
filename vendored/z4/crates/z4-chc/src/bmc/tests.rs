// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]
use super::*;
use crate::{ClauseBody, ClauseHead, HornClause};
use ntest::timeout;
fn create_simple_unsafe_problem() -> ChcProblem {
    // A simple unsafe problem:
    // x = 0 => Inv(x)
    // Inv(x) => Inv(x + 1)
    // Inv(x) ∧ x >= 5 => false
    //
    // This is unsafe because starting from x=0, we reach x=5 in 5 steps
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) => Inv(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) ∧ x >= 5 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_safe_problem() -> ChcProblem {
    // A safe problem:
    // x = 0 => Inv(x)
    // Inv(x) ∧ x < 3 => Inv(x + 1)
    // Inv(x) ∧ x >= 10 => false
    //
    // This is safe because x never exceeds 3
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) ∧ x < 3 => Inv(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(3))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) ∧ x >= 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

/// Test BMC finds counterexample in unsafe problem with body predicate
///
/// With the level-based encoding (#108), BMC correctly handles body predicates.
/// This problem has:
/// - x = 0 => Inv(x)
/// - Inv(x) => Inv(x + 1)
/// - Inv(x) ∧ x >= 5 => false
///
/// BMC should find counterexample at depth 5 (5 transitions from x=0 to x=5)
#[test]
fn test_bmc_finds_unsafe_with_body_predicate() {
    let problem = create_simple_unsafe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    match result {
        ChcEngineResult::Unsafe(cex) => {
            // BMC correctly finds counterexample
            // Level-based encoding finds counterexample at depth 6:
            // - Level 0: fact establishes Inv(0)
            // - Levels 1-5: transitions Inv(k) => Inv(k+1)
            // - Level 6: query Inv(x) ∧ x >= 5 checked (first level where x=5 is reachable)
            assert!(
                cex.steps.len() <= 11,
                "Expected depth <= 10, got {}",
                cex.steps.len()
            );
        }
        _ => {
            panic!("BMC should find counterexample with level-based encoding (#108)");
        }
    }
}

/// Test BMC returns Unknown for safe problem
///
/// This problem is safe because x never exceeds 3, but BMC returns Unknown
/// (no counterexample found within bounds).
#[test]
fn test_bmc_unknown_for_safe_problem() {
    let problem = create_safe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    match result {
        ChcEngineResult::Unknown => {
            // Expected - no counterexample within bounds for safe problem
        }
        ChcEngineResult::Unsafe(cex) => {
            panic!(
                "BMC incorrectly reported unsafe at depth {} for safe problem",
                cex.steps.len()
            );
        }
        _ => {
            panic!("BMC returned unexpected result: {result:?}");
        }
    }
}

/// Test BMC finds counterexample at depth 0
///
/// When the initial state immediately violates the query, BMC should find it.
#[test]
fn test_bmc_finds_depth_0_counterexample() {
    // x = 5 => Inv(x)
    // Inv(x) ∧ x >= 5 => false
    //
    // Initial state x=5 immediately satisfies the query constraint.
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 5,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    match result {
        ChcEngineResult::Unsafe(cex) => {
            // BMC finds counterexample at depth 0 (1 step in trace)
            assert!(
                cex.steps.len() <= 1,
                "Expected counterexample at depth 0, got {} steps",
                cex.steps.len()
            );
        }
        _ => {
            panic!("BMC should find counterexample at depth 0");
        }
    }
}

/// Test BMC on a problem where query has NO body predicate.
#[test]
fn test_bmc_finds_unsafe_no_body_predicate() {
    // Query: x >= 5 => false (NO body predicate)
    // This is a degenerate case - query constraint can be satisfied without predicates
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) => Inv(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: x >= 5 => false (NO Inv(x) in body!)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ClauseHead::False,
    ));

    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    match result {
        ChcEngineResult::Unsafe(cex) => {
            // BMC correctly finds counterexample for query without body predicate
            // This happens at depth 0 since constraint alone is satisfiable
            assert!(
                cex.steps.len() <= 1,
                "Expected depth 0, got {} steps",
                cex.steps.len()
            );
        }
        _ => {
            panic!("BMC should find counterexample for query without body predicate");
        }
    }
}

/// Regression test for #2805: query body args that are expressions
/// must be linked to level args via equalities (not silently dropped).
#[test]
fn test_bmc_query_expression_arg_no_spurious_counterexample() {
    // Fact: x = 0 => P(x)
    // Query: P(x + 1) /\ x >= 5 => false
    //
    // Real semantics: safe for all bounded depths (P(0) only, so P(6) unreachable).
    // Buggy semantics (dropping non-var arg equalities) gives spurious Unsafe:
    // P#k_0 unconstrained by x+1, with free x >= 5.
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                p,
                vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
            )],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 5,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, ChcEngineResult::Unknown),
        "expected Unknown (no bounded CEX), got {result:?}"
    );
}

/// Create two-phase unsafe problem: inc x 0→10, switch pc 0→1, dec x forever.
/// Query: Inv(x,pc) ∧ x<0 => false (unsafe at depth ~22).
fn create_two_phase_unsafe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let pc = ChcVar::new("pc", ChcSort::Int);
    let x1 = ChcVar::new("x1", ChcSort::Int);
    let pc1 = ChcVar::new("pc1", ChcSort::Int);

    // Fact: x=0 ∧ pc=0 => Inv(x, pc)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())]),
    ));

    // Transition 1: Inv(x,pc) ∧ pc=0 ∧ x<2 => Inv(x+1, 0)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())])],
            Some(ChcExpr::and_all(
                [
                    ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(0)),
                    ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(2)),
                    ChcExpr::eq(
                        ChcExpr::var(x1.clone()),
                        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                    ),
                    ChcExpr::eq(ChcExpr::var(pc1.clone()), ChcExpr::int(0)),
                ]
                .iter()
                .cloned(),
            )),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(x1.clone()), ChcExpr::var(pc1.clone())],
        ),
    ));

    // Transition 2: Inv(x,pc) ∧ pc=0 ∧ x>=2 => Inv(x, 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())])],
            Some(ChcExpr::and_all(
                [
                    ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(0)),
                    ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(2)),
                    ChcExpr::eq(ChcExpr::var(x1.clone()), ChcExpr::var(x.clone())),
                    ChcExpr::eq(ChcExpr::var(pc1.clone()), ChcExpr::int(1)),
                ]
                .iter()
                .cloned(),
            )),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(x1.clone()), ChcExpr::var(pc1.clone())],
        ),
    ));

    // Transition 3: Inv(x,pc) ∧ pc=1 => Inv(x-1, 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())])],
            Some(ChcExpr::and_all(
                [
                    ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(1)),
                    ChcExpr::eq(
                        ChcExpr::var(x1.clone()),
                        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(-1)),
                    ),
                    ChcExpr::eq(ChcExpr::var(pc1.clone()), ChcExpr::int(1)),
                ]
                .iter()
                .cloned(),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x1), ChcExpr::var(pc1)]),
    ));

    // Query: Inv(x,pc) ∧ x<0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc)])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    problem
}

/// Regression test for a two-phase unsafe system.
///
/// The original deep instance of this benchmark behaved more like a
/// performance benchmark than a unit test and was unstable across debug
/// environments. This compact instance preserves the two-phase structure
/// (count up in phase 0, then count down in phase 1 until x < 0) while
/// keeping the required BMC depth small enough for the lib test suite.
#[test]
#[timeout(20_000)]
fn test_bmc_two_phase_unsafe() {
    let problem = create_two_phase_unsafe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig {
            verbose: true,
            ..ChcEngineConfig::default()
        },
        max_depth: 8,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    match result {
        ChcEngineResult::Unsafe(cex) => {
            assert!(
                cex.steps.len() <= 9,
                "Expected depth <= 8, got {}",
                cex.steps.len()
            );
        }
        _ => {
            panic!("BMC should find counterexample for two_phase_unsafe, got {result:?}");
        }
    }
}

/// Test acyclic_safe: BMC returns Safe when all depths exhausted.
///
/// The safe problem (x bounded by 3, query at x >= 10) has no counterexample
/// within any depth. With acyclic_safe=true, BMC should return Safe.
#[test]
fn test_bmc_acyclic_safe_returns_safe() {
    let problem = create_safe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        acyclic_safe: true,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, ChcEngineResult::Safe(_)),
        "Expected Safe for acyclic_safe with bounded safe problem, got {result:?}"
    );
}

/// Test acyclic_safe: BMC still returns Unsafe when counterexample exists.
///
/// Even with acyclic_safe=true, if a counterexample is found within the
/// depth bound, BMC should return Unsafe (not Safe).
#[test]
fn test_bmc_acyclic_safe_still_returns_unsafe() {
    let problem = create_simple_unsafe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        acyclic_safe: true,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, ChcEngineResult::Unsafe(_)),
        "Expected Unsafe for reachable counterexample even with acyclic_safe, got {result:?}"
    );
}

/// Create a deep two-phase problem requiring depth ~22.
fn create_deep_two_phase_unsafe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let pc = ChcVar::new("pc", ChcSort::Int);
    let x1 = ChcVar::new("x1", ChcSort::Int);
    let pc1 = ChcVar::new("pc1", ChcSort::Int);

    // Fact: x=0, pc=0 => Inv(x, pc)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())]),
    ));

    // T1: Inv(x,pc), pc=0, x<10 => Inv(x+1, 0)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())])],
            Some(ChcExpr::and_all(
                [
                    ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(0)),
                    ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10)),
                    ChcExpr::eq(
                        ChcExpr::var(x1.clone()),
                        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                    ),
                    ChcExpr::eq(ChcExpr::var(pc1.clone()), ChcExpr::int(0)),
                ]
                .iter()
                .cloned(),
            )),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(x1.clone()), ChcExpr::var(pc1.clone())],
        ),
    ));

    // T2: Inv(x,pc), pc=0, x>=10 => Inv(x, 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())])],
            Some(ChcExpr::and_all(
                [
                    ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(0)),
                    ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10)),
                    ChcExpr::eq(ChcExpr::var(x1.clone()), ChcExpr::var(x.clone())),
                    ChcExpr::eq(ChcExpr::var(pc1.clone()), ChcExpr::int(1)),
                ]
                .iter()
                .cloned(),
            )),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(x1.clone()), ChcExpr::var(pc1.clone())],
        ),
    ));

    // T3: Inv(x,pc), pc=1 => Inv(x-1, 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())])],
            Some(ChcExpr::and_all(
                [
                    ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(1)),
                    ChcExpr::eq(
                        ChcExpr::var(x1.clone()),
                        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(-1)),
                    ),
                    ChcExpr::eq(ChcExpr::var(pc1.clone()), ChcExpr::int(1)),
                ]
                .iter()
                .cloned(),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x1), ChcExpr::var(pc1)]),
    ));

    // Query: Inv(x,pc), x<0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc)])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    problem
}

/// Deep two-phase benchmark: requires depth ~22 (#7983).
#[test]
#[timeout(30_000)]
fn test_bmc_deep_two_phase_unsafe() {
    let problem = create_deep_two_phase_unsafe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig {
            verbose: true,
            ..ChcEngineConfig::default()
        },
        max_depth: 25,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    match result {
        ChcEngineResult::Unsafe(cex) => {
            assert!(
                cex.steps.len() >= 20,
                "Expected depth >= 20, got {}",
                cex.steps.len()
            );
        }
        _ => {
            panic!("BMC should find counterexample for deep_two_phase_unsafe, got {result:?}");
        }
    }
}

/// Test that acyclic_safe=false still returns Unknown (not Safe).
#[test]
fn test_bmc_non_acyclic_returns_unknown() {
    let problem = create_safe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        acyclic_safe: false,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, ChcEngineResult::Unknown),
        "Expected Unknown for non-acyclic BMC with safe problem, got {result:?}"
    );
}
