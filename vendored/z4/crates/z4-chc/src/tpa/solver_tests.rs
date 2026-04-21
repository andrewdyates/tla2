// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{CancellationToken, ChcSort, ClauseBody, ClauseHead, HornClause};
use ntest::timeout;

fn make_reachability_test_solver(cancellation_token: Option<CancellationToken>) -> TpaSolver {
    use crate::transition_system::TransitionSystem;

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let mut config = TpaConfig::default();
    config.base.cancellation_token = cancellation_token;
    let mut solver = TpaSolver::new(problem, config);

    let x_next = ChcVar::new("x_1", ChcSort::Int);
    let transition = ChcExpr::eq(
        ChcExpr::var(x_next),
        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
    );
    solver.transition_system = Some(TransitionSystem::new(
        inv,
        vec![x.clone()],
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        transition,
        ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0)),
    ));
    solver
}

#[test]
fn test_tpa_simple_safe() {
    // Simple system: x starts at 0, increments, query is x < 0
    // Should be safe since x is always >= 0
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Init: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Trans: Inv(x) => Inv(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: Inv(x) ∧ x < 0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let config = TpaConfig {
        max_power: 10,
        timeout_per_power: Duration::from_millis(200),
        ..Default::default()
    };
    let mut solver = TpaSolver::new(problem, config);
    let result = solver.solve();

    // TPA without MBP/QE will not detect fixed points for this simple example,
    // so it will return Unknown at max_power. The important check is that it
    // does NOT return Unsafe (which would be a spurious counterexample).
    //
    // The transition variable substitution bug (fixed in this commit) was
    // causing spurious Unsafe results because the transition used the
    // original variable name instead of canonical names.
    assert!(
        !matches!(result, TpaResult::Unsafe { .. }),
        "TPA should not report safe system as unsafe"
    );
}

#[test]
fn test_tpa_simple_unsafe() {
    // Simple system: x starts at 0, increments, query is x >= 5
    // Should be unsafe since x eventually reaches 5
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Init: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Trans: Inv(x) => Inv(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: Inv(x) ∧ x >= 5 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    let config = TpaConfig {
        max_power: 10,
        timeout_per_power: Duration::from_millis(200),
        verbose_level: 2,
        ..Default::default()
    };
    let mut solver = TpaSolver::new(problem, config);
    let result = solver.solve();

    // TPA should either find unsafe or return unknown (not safe)
    assert!(
        !matches!(result, TpaResult::Safe { .. }),
        "TPA should not report unsafe system as safe"
    );

    // If unsafe, verify the counterexample steps are present
    if let TpaResult::Unsafe { steps, .. } = &result {
        assert!(*steps > 0, "Counterexample should have at least one step");
    }
}

// =========================================================================
// Regression tests for recursive decomposition (#1146)
//
// These tests verify that TPA's recursive decomposition:
// 1. Does not report spurious Unsafe on known-safe systems
// 2. Correctly handles refinement when recursive verification fails
// =========================================================================

/// Regression test: Two-variable safe system.
///
/// This test exercises the recursive decomposition on a two-variable system
/// where the midpoint extraction is non-trivial. The system tracks both
/// a counter (x) and a sum (y = sum of all x values). The query y < 0 is
/// never satisfiable since x and y are always >= 0.
///
/// Historical bug: Variable naming mismatch in midpoint extraction could
/// cause spurious counterexamples.
///
/// Part of #1146
#[test]
fn test_tpa_two_var_safe_no_spurious_unsafe() {
    // System: x starts at 0, y starts at 0
    // Transition: x' = x + 1, y' = y + x
    // Query: y < 0 (should never be reachable)
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Init: x = 0 ∧ y = 0 => Inv(x, y)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())]),
    ));

    // Trans: Inv(x, y) => Inv(x + 1, y + x)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            inv,
            vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())],
        )]),
        ClauseHead::Predicate(
            inv,
            vec![
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                ChcExpr::add(ChcExpr::var(y.clone()), ChcExpr::var(x.clone())),
            ],
        ),
    ));

    // Query: Inv(x, y) ∧ y < 0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x), ChcExpr::var(y.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(y), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let config = TpaConfig {
        max_power: 8,
        timeout_per_power: Duration::from_millis(500),
        ..Default::default()
    };
    let mut solver = TpaSolver::new(problem, config);
    let result = solver.solve();

    // Critical assertion: Must NOT return spurious Unsafe
    assert!(
        !matches!(result, TpaResult::Unsafe { .. }),
        "TPA should not report safe two-variable system as unsafe (spurious CEX)"
    );
}

/// Regression test: Bounded counter with unreachable query.
///
/// Tests TPA on a system where x is bounded (0 <= x <= 10) and the query
/// asks for x > 20. This should be safe but requires TPA to correctly
/// handle the transition bounds during recursive decomposition.
///
/// Historical bug: Power abstraction without proper strengthening could
/// produce spurious paths that overapproximate the reachable states.
///
/// Part of #1146
#[test]
fn test_tpa_bounded_counter_no_spurious_unsafe() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Init: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Trans: Inv(x) ∧ x < 10 => Inv(x + 1)
    // This bounds x to [0, 10]
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: Inv(x) ∧ x > 20 => false
    // Never reachable since x is bounded at 10
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(20))),
        ),
        ClauseHead::False,
    ));

    let config = TpaConfig {
        max_power: 8,
        timeout_per_power: Duration::from_millis(500),
        ..Default::default()
    };
    let mut solver = TpaSolver::new(problem, config);
    let result = solver.solve();

    // Critical assertion: Must NOT return spurious Unsafe
    // Safe is ideal, Unknown is acceptable, Unsafe is a bug
    assert!(
        !matches!(result, TpaResult::Unsafe { .. }),
        "TPA should not report bounded safe system as unsafe"
    );
}

/// Regression test: Multi-step unsafe system.
///
/// Tests that TPA correctly identifies an unsafe system that requires
/// multiple steps (more than 2) to reach the bad state. This exercises
/// the recursive decomposition at power > 0.
///
/// Part of #1146
#[test]
fn test_tpa_multi_step_unsafe() {
    // System: x starts at 0, increments, query is x = 8
    // Requires 8 steps to reach. TPA power k covers 2^(k+1) steps,
    // so power 2 (covering 8 steps) should find it.
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Init: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Trans: Inv(x) => Inv(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: Inv(x) ∧ x = 8 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(8))),
        ),
        ClauseHead::False,
    ));

    let config = TpaConfig {
        max_power: 5, // Up to 2^5 = 32 steps, should find 8
        timeout_per_power: Duration::from_millis(500),
        ..Default::default()
    };
    let mut solver = TpaSolver::new(problem, config);
    let result = solver.solve();

    // Should find the unsafe state at x=8
    // Accept Unknown if TPA doesn't find it (not a bug, just incomplete)
    assert!(
        !matches!(result, TpaResult::Safe { .. }),
        "TPA should not report reachable state as safe"
    );
}

/// Regression test: Refinement on spurious model.
///
/// This test creates a scenario where the power abstraction may initially
/// suggest a path exists, but recursive verification should refine it away.
/// The system has a "mode" variable that constrains which transitions are
/// valid.
///
/// Part of #1146
#[test]
#[timeout(30_000)]
fn test_tpa_mode_constrained_safe() {
    // System with mode variable:
    // - mode=0: x increments
    // - mode stays 0 (never changes)
    // Query: mode=1 (unreachable since mode starts at 0 and never changes)
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let mode = ChcVar::new("mode", ChcSort::Int);

    // Init: x = 0 ∧ mode = 0 => Inv(x, mode)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(mode.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(x.clone()), ChcExpr::var(mode.clone())],
        ),
    ));

    // Trans: Inv(x, mode) => Inv(x + 1, mode)
    // Mode never changes!
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            inv,
            vec![ChcExpr::var(x.clone()), ChcExpr::var(mode.clone())],
        )]),
        ClauseHead::Predicate(
            inv,
            vec![
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                ChcExpr::var(mode.clone()), // mode unchanged
            ],
        ),
    ));

    // Query: Inv(x, mode) ∧ mode = 1 => false
    // Never reachable since mode stays 0
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x), ChcExpr::var(mode.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(mode), ChcExpr::int(1))),
        ),
        ClauseHead::False,
    ));

    // This test checks soundness (no spurious `Unsafe`) in the mode-constrained
    // setup, not deep completeness. A shallow bounded search is sufficient and
    // keeps runtime stable under full-suite load.
    let config = TpaConfig {
        max_power: 1,
        timeout_per_power: Duration::from_millis(50),
        ..Default::default()
    };
    let mut solver = TpaSolver::new(problem, config);
    let result = solver.solve();

    // Critical assertion: Must NOT return spurious Unsafe
    // The power abstraction might suggest mode=1 is reachable, but
    // recursive verification should refine this away.
    assert!(
        !matches!(result, TpaResult::Unsafe { .. }),
        "TPA should not report mode-constrained safe system as unsafe"
    );
}

#[test]
fn test_reachability_exact_cancelled_returns_unknown() {
    let token = CancellationToken::new();
    token.cancel();
    let mut solver = make_reachability_test_solver(Some(token));
    let ts = solver.transition_system.take().unwrap();

    let result = solver.reachability_exact(&ChcExpr::Bool(true), &ChcExpr::Bool(true), 1, &ts);

    assert!(
        matches!(result, ReachResult::Unknown),
        "reachability_exact must return Unknown on cancellation"
    );
}

#[test]
fn test_reachability_less_than_cancelled_returns_unknown() {
    let token = CancellationToken::new();
    token.cancel();
    let mut solver = make_reachability_test_solver(Some(token));
    let ts = solver.transition_system.take().unwrap();

    // Use different from/to to avoid the from==to early-return path
    let result = solver.reachability_less_than(&ChcExpr::Bool(true), &ChcExpr::Bool(false), 1, &ts);

    assert!(
        matches!(result, ReachResult::Unknown),
        "reachability_less_than must return Unknown on cancellation"
    );
}

#[test]
fn test_reachability_exact_caches_verified_queries() {
    let mut solver = make_reachability_test_solver(None);
    let ts = solver.transition_system.take().unwrap();
    solver.init_powers(&ts);

    let x = ChcVar::new("x", ChcSort::Int);
    let from = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let to = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(2));

    let first = solver.reachability_exact(&from, &to, 0, &ts);
    assert!(
        matches!(first, ReachResult::Reachable { steps: 2, .. }),
        "base exact query should be concretely reachable"
    );
    assert_eq!(
        solver.exact_query_cache.len(),
        1,
        "power-0 exact query should allocate a single cache level"
    );
    assert!(
        solver.exact_query_cache[0].contains_key(&(from.clone(), to.clone())),
        "verified exact query should be stored in the cache"
    );

    let second = solver.reachability_exact(&from, &to, 0, &ts);
    assert!(
        matches!(second, ReachResult::Reachable { steps: 2, .. }),
        "cached exact query should preserve the verified reachability answer"
    );
    assert_eq!(
        solver.exact_query_cache[0].len(),
        1,
        "repeating the same query should reuse the cached entry"
    );
}

#[test]
fn test_check_power_cancelled_returns_unknown_not_safe() {
    let token = CancellationToken::new();
    token.cancel();
    let mut solver = make_reachability_test_solver(Some(token));

    let result = solver.check_power(0);

    assert!(
        matches!(result, PowerResult::Unknown),
        "check_power must stay Unknown when reachability is cancelled"
    );
}

/// Regression test for D8 exact-power purity (Part of #1306).
///
/// Verifies that learned exact powers are pure transition summaries:
/// they mention only time-0 and time-1 state variables, never an extra
/// midpoint time layer (e.g. x_2, x_3). Before D8, z4 built higher
/// exact powers by explicit conjunction which retained midpoint variables
/// and caused geometric formula blowup.
#[test]
fn test_exact_power_purity_no_midpoint_vars() {
    use crate::expr_vars::expr_var_names;
    use crate::transition_system::TransitionSystem;
    use rustc_hash::FxHashSet;

    // Build a simple bounded counter: x starts at 0, increments,
    // query is x > 20 (safe, triggers UNSAT → interpolant learning).
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
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(20))),
        ),
        ClauseHead::False,
    ));

    let config = TpaConfig {
        max_power: 4,
        timeout_per_power: Duration::from_millis(500),
        verbose_level: 0,
        ..Default::default()
    };
    let mut solver = TpaSolver::new(problem, config);

    let x_next = ChcVar::new("x_1", ChcSort::Int);
    let transition = ChcExpr::and(
        ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10)),
        ChcExpr::eq(
            ChcExpr::var(x_next),
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ),
    );
    solver.transition_system = Some(TransitionSystem::new(
        inv,
        vec![x.clone()],
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        transition,
        ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(20)),
    ));

    // Run the solver to trigger interpolant learning across power levels
    let _result = solver.solve();

    // Collect allowed variable names: time-0 ("x") and time-1 ("x_1")
    let ts = solver.transition_system.as_ref().unwrap();
    let time_0_vars = ts.state_var_names();
    let time_1_vars = ts.state_var_names_at(1);
    let allowed: FxHashSet<String> = time_0_vars.union(&time_1_vars).cloned().collect();

    // Check all learned exact powers (skip index 0 = base transition)
    for (idx, power_opt) in solver.exact_powers.iter().enumerate().skip(1) {
        if let Some(power) = power_opt {
            let vars = expr_var_names(power);
            for var_name in &vars {
                assert!(
                    allowed.contains(var_name),
                    "exact_powers[{idx}] contains midpoint variable '{var_name}' — \
                     learned exact powers must be pure transition summaries \
                     (only time-0 and time-1 vars). All vars: {vars:?}"
                );
            }
        }
    }

    // Same check for less-than powers
    for (idx, power_opt) in solver.less_than_powers.iter().enumerate().skip(1) {
        if let Some(power) = power_opt {
            let vars = expr_var_names(power);
            for var_name in &vars {
                assert!(
                    allowed.contains(var_name),
                    "less_than_powers[{idx}] contains midpoint variable '{var_name}' — \
                     learned less-than powers must be pure transition summaries \
                     (only time-0 and time-1 vars). All vars: {vars:?}"
                );
            }
        }
    }
}

// =========================================================================
// Portfolio integration tests (moved from solver_houdini_tests.rs)
// =========================================================================

fn solve_with_tpa(input: &str) -> crate::portfolio::PortfolioResult {
    use crate::parser::ChcParser;
    use crate::portfolio::{PortfolioConfig, PortfolioSolver};
    let problem = ChcParser::parse(input).expect("valid SMT-LIB input");
    let tpa_config = TpaConfig::with_max_power(10);
    let config = PortfolioConfig::tpa_only(tpa_config);
    let solver = PortfolioSolver::new(problem, config);
    solver.solve()
}

/// TPA on dillig12_m_e1: 2-predicate problem requiring case-splitting (#1306).
/// TPA cannot solve it; verifies termination with Unknown. A 30s portfolio-level
/// timeout provides the cancellation token that bounds total wall-clock time.
/// Without it, tpa_only() has no cancellation and each power level can issue
/// many recursive reachability queries (up to 100 iterations each at 5s/query),
/// exceeding any reasonable ntest timeout (#5011).
#[test]
#[timeout(60_000)]
fn test_tpa_dillig12_m_e1() {
    use crate::parser::ChcParser;
    use crate::portfolio::{PortfolioConfig, PortfolioResult, PortfolioSolver};
    let input = r#"
(set-logic HORN)
(declare-fun |SAD| ( Int Int ) Bool)
(declare-fun |FUN| ( Int Int Int Int Int ) Bool)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and (and (= C 0) (= B 0) (= A 0) (= D 0) (= E 1)))
      (FUN A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) )
    (=>
      (and
        (FUN A B C D J)
        (and (= I (ite (= J 1) (+ E F) E))
     (= H (+ C F))
     (= G (+ 1 B))
     (= F (+ 1 A))
     (= E (+ D G)))
      )
      (FUN F G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (FUN A B E D C)
        (let ((a!1 (= F (ite (= C 1) (+ 2 D (* (- 2) E)) 1))))
  (and a!1 (= G 0)))
      )
      (SAD F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (SAD B A)
        (and (or (= C (+ 1 A)) (= C (+ 2 A))) (<= A B))
      )
      (SAD B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and (SAD A B) (> B A))
      false
    )
  )
)
(check-sat)
"#;

    // Portfolio-level 30s timeout sets a cancellation token so TPA terminates
    // predictably. Without it, tpa_only() runs inline with no cancellation,
    // and recursive reachability queries can far exceed per-query timeouts.
    use std::time::Duration;
    let problem = ChcParser::parse(input).expect("valid SMT-LIB input");
    let tpa_config = TpaConfig {
        max_power: 2,
        timeout_per_power: Duration::from_secs(5),
        ..TpaConfig::default()
    };
    let config = PortfolioConfig::tpa_only(tpa_config).timeout(Some(Duration::from_secs(30)));
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();
    assert!(
        matches!(result, PortfolioResult::Safe(_) | PortfolioResult::Unknown),
        "Expected Safe or Unknown, got {result:?}"
    );
}

/// Simple test to verify TPA basic functionality.
#[test]
#[timeout(10_000)]
fn test_tpa_simple_counter() {
    use crate::portfolio::PortfolioResult;
    let input = r#"
(set-logic HORN)
(declare-fun |inv| ( Int ) Bool)
(assert
  (forall ( (x Int) )
    (=>
      (= x 0)
      (inv x)
    )
  )
)
(assert
  (forall ( (x Int) (xp Int) )
    (=>
      (and (inv x) (= xp (+ x 1)) (<= x 10))
      (inv xp)
    )
  )
)
(assert
  (forall ( (x Int) )
    (=>
      (and (inv x) (< x 0))
      false
    )
  )
)
(check-sat)
"#;

    let result = solve_with_tpa(input);
    assert!(
        matches!(result, PortfolioResult::Safe(_) | PortfolioResult::Unknown),
        "Expected Safe or Unknown for simple counter, got {result:?}"
    );
}
