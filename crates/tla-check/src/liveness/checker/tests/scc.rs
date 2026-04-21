// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SCC detection, AE state/action satisfaction, promise tracking
//!
//! Split from liveness/checker/tests.rs — Part of #2779

use super::helpers::{action_pred_xprime_eq_x, action_pred_xprime_eq_x_plus_1, state_pred_x_eq};
use super::*;
use crate::liveness::test_helpers::{
    constraints_to_grouped_plan, empty_successors, make_checker, make_checker_with_constraints,
};
use crate::liveness::LiveExpr;
use crate::Value;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_find_sccs() {
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    let mut get_successors = empty_successors;

    // Create a cycle: s0 -> s1 -> s0
    let state0 = State::from_pairs([("x", Value::int(0))]);
    let state1 = State::from_pairs([("x", Value::int(1))]);

    let added0 = checker
        .add_initial_state(&state0, &mut get_successors, None)
        .unwrap();
    assert!(
        !added0.is_empty(),
        "add_initial_state must return at least one node for the SCC test to be meaningful"
    );
    let added1 = checker
        .add_successors(
            added0[0],
            std::slice::from_ref(&state1),
            &mut get_successors,
            None,
        )
        .unwrap();
    let n1 = added1[0];
    let _ = checker
        .add_successors(n1, std::slice::from_ref(&state0), &mut get_successors, None)
        .unwrap();

    // Should find SCCs in the graph
    let cycles = checker.find_cycles();
    assert!(
        cycles.errors.is_empty(),
        "Tarjan errors: {:?}",
        cycles.errors
    );
    // We added states and created a cycle, so the graph must have nodes
    assert!(
        checker.graph().len() >= 2,
        "graph should have at least 2 nodes after adding s0->s1->s0 cycle"
    );
    // With []TRUE and a two-state cycle, Tarjan should find at least one
    // non-trivial SCC containing both states
    assert!(
        !cycles.sccs.is_empty(),
        "find_cycles should detect the s0->s1->s0 cycle as a non-trivial SCC"
    );
    // Verify the SCC actually contains both state fingerprints — the old test
    // only checked `scc.len() >= 2` which would pass with any two nodes,
    // even if they were the wrong ones.
    let fp0 = state0.fingerprint();
    let fp1 = state1.fingerprint();
    let big_scc = cycles
        .sccs
        .iter()
        .find(|scc| scc.len() >= 2)
        .expect("should have at least one SCC with 2+ nodes");
    let scc_fps: std::collections::HashSet<_> =
        big_scc.nodes().iter().map(|n| n.state_fp).collect();
    assert!(
        scc_fps.contains(&fp0),
        "SCC should contain state0 (x=0), fps: {:?}",
        scc_fps
    );
    assert!(
        scc_fps.contains(&fp1),
        "SCC should contain state1 (x=1), fps: {:?}",
        scc_fps
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_promise_tracking_eventually() {
    // tf == <>P; system never satisfies P. Promise tracking should prevent
    // reporting a counterexample.
    let p = state_pred_x_eq(1, 1);
    let mut checker = make_checker(LiveExpr::eventually(p));
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .unwrap();
    assert_eq!(init_nodes.len(), 1);

    // Self-loop on the single state.
    let _ = checker
        .add_successors(
            init_nodes[0],
            std::slice::from_ref(&s0),
            &mut get_successors,
            None,
        )
        .unwrap();

    let plan = constraints_to_grouped_plan(checker.constraints());
    let result = checker.check_liveness_grouped(&plan, 0);
    assert!(matches!(result, LivenessResult::Satisfied));
    // Verify the checker actually explored the graph (a trivially-returning
    // checker that always returns Satisfied would fail this).
    assert!(
        checker.stats().graph_nodes >= 1,
        "checker must have at least 1 graph node for promise tracking test, got {}",
        checker.stats().graph_nodes
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_liveness_violation_cycle_no_promises() {
    // tf == []~P (negation of <>P). With a cycle where P never holds, this is satisfiable.
    let p = state_pred_x_eq(1, 1);
    let mut checker = make_checker(LiveExpr::always(LiveExpr::not(p)));
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .unwrap();
    assert!(!init_nodes.is_empty());
    let _ = checker
        .add_successors(
            init_nodes[0],
            std::slice::from_ref(&s0),
            &mut get_successors,
            None,
        )
        .unwrap();

    let plan = constraints_to_grouped_plan(checker.constraints());
    let result = checker.check_liveness_grouped(&plan, 0);
    // Verify both the verdict AND the counterexample trace — the old
    // `matches!(_, Violated { .. })` check would pass even if the trace
    // was empty or contained wrong states.
    match &result {
        LivenessResult::Violated { prefix, cycle } => {
            assert!(
                !cycle.is_empty(),
                "violation must include a non-empty cycle"
            );
            // The cycle should contain state s0 (x=0), which is the only
            // state in the self-loop.
            let cycle_has_s0 = cycle
                .iter()
                .any(|(s, _)| s.get("x") == Some(&Value::int(0)));
            assert!(
                cycle_has_s0,
                "cycle should contain s0 (x=0), got: {:?}",
                cycle.iter().map(|(s, _)| s.clone()).collect::<Vec<_>>()
            );
            // Prefix may be empty if the cycle starts from an initial state,
            // but verify it's structurally valid (all states have "x").
            for (s, _) in prefix {
                assert!(
                    s.get("x").is_some(),
                    "prefix state should contain variable x"
                );
            }
        }
        other => panic!("expected Violated, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ae_action_requires_witness_edge() {
    // Require []<>A where A is action-level.
    // A = (x' = x + 1) is false on a self-loop, thus no counterexample should be found.
    let mut checker = make_checker_with_constraints(
        LiveExpr::always(LiveExpr::Bool(true)),
        LivenessConstraints {
            ae_action: vec![action_pred_xprime_eq_x_plus_1(1)],
            ..Default::default()
        },
    );
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .unwrap();
    let _ = checker
        .add_successors(
            init_nodes[0],
            std::slice::from_ref(&s0),
            &mut get_successors,
            None,
        )
        .unwrap();

    let plan = constraints_to_grouped_plan(checker.constraints());
    let result = checker.check_liveness_grouped(&plan, 0);
    assert!(matches!(result, LivenessResult::Satisfied));

    // If we require []<>(x' = x) instead, the self-loop witnesses it.
    let mut checker = make_checker_with_constraints(
        LiveExpr::always(LiveExpr::Bool(true)),
        LivenessConstraints {
            ae_action: vec![action_pred_xprime_eq_x(2)],
            ..Default::default()
        },
    );

    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .unwrap();
    let _ = checker
        .add_successors(
            init_nodes[0],
            std::slice::from_ref(&s0),
            &mut get_successors,
            None,
        )
        .unwrap();

    let plan = constraints_to_grouped_plan(checker.constraints());
    let result = checker.check_liveness_grouped(&plan, 0);
    // Verify the trace, not just the verdict — `matches!(_, Violated { .. })`
    // would pass even with an empty or wrong-state counterexample.
    match &result {
        LivenessResult::Violated { cycle, .. } => {
            assert!(!cycle.is_empty(), "violation cycle must be non-empty");
            let cycle_has_s0 = cycle
                .iter()
                .any(|(s, _)| s.get("x") == Some(&Value::int(0)));
            assert!(
                cycle_has_s0,
                "cycle should contain s0 (x=0), got: {:?}",
                cycle.iter().map(|(s, _)| s.clone()).collect::<Vec<_>>()
            );
        }
        other => panic!(
            "expected Violated for []<>(x'=x) on self-loop, got {:?}",
            other
        ),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ea_state_filters_scc_edges() {
    // EA check <>[]S where S is state-level (x = 0).
    // On a 2-state cycle (0 <-> 1), there is no sub-SCC where x=0 holds always.
    let mut checker = make_checker_with_constraints(
        LiveExpr::always(LiveExpr::Bool(true)),
        LivenessConstraints {
            ea_state: vec![state_pred_x_eq(0, 1)],
            ..Default::default()
        },
    );
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .unwrap();
    let added = checker
        .add_successors(
            init_nodes[0],
            std::slice::from_ref(&s1),
            &mut get_successors,
            None,
        )
        .unwrap();

    let n1 = added[0];
    let _ = checker
        .add_successors(n1, std::slice::from_ref(&s0), &mut get_successors, None)
        .unwrap();

    // Close the cycle by adding s0->s1 edge from init_nodes[0]
    let _ = checker
        .add_successors(
            init_nodes[0],
            std::slice::from_ref(&s1),
            &mut get_successors,
            None,
        )
        .unwrap();

    let plan = constraints_to_grouped_plan(checker.constraints());
    let result = checker.check_liveness_grouped(&plan, 0);
    assert!(matches!(result, LivenessResult::Satisfied));
}

/// Test with two disjoint SCCs: SCC-A cycles {x=0, x=1}, SCC-B cycles {x=10, x=11}.
///
/// **Polarity note:** The AE constraint in `LivenessConstraints` comes from the
/// *negated* temporal formula. An SCC that *satisfies* the AE constraint represents
/// a *violation* of the original user property (it satisfies the negation).
///
/// AE constraint `[]<>(x=0)`: SCC-A contains x=0 → satisfies the negation → VIOLATION.
/// SCC-B lacks x=0 → does not satisfy the negation → skipped (not a violation).
/// The counterexample cycle should contain only SCC-A states.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_multi_scc_violation_isolates_correct_scc() {
    // AE constraint from the NEGATED formula: []<>(x=0).
    // SCC-A {x=0, x=1} contains x=0 → satisfies constraint → violation.
    // SCC-B {x=10, x=11} lacks x=0 → fails constraint → skipped.
    let mut checker = make_checker_with_constraints(
        LiveExpr::always(LiveExpr::Bool(true)),
        LivenessConstraints {
            ae_state: vec![state_pred_x_eq(0, 700)],
            ..Default::default()
        },
    );
    let mut get_successors = empty_successors;

    // SCC-A: s0(x=0) <-> s1(x=1) — satisfies []<>(x=0)
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .unwrap();
    assert!(!init_nodes.is_empty(), "s0 should be added to graph");
    let from_s0 = checker
        .add_successors(
            init_nodes[0],
            std::slice::from_ref(&s1),
            &mut get_successors,
            None,
        )
        .unwrap();
    assert!(!from_s0.is_empty(), "s1 should be added as successor of s0");
    let _ = checker
        .add_successors(
            from_s0[0],
            std::slice::from_ref(&s0),
            &mut get_successors,
            None,
        )
        .unwrap();

    // SCC-B: s10(x=10) <-> s11(x=11) — does NOT satisfy []<>(x=0)
    let s10 = State::from_pairs([("x", Value::int(10))]);
    let s11 = State::from_pairs([("x", Value::int(11))]);
    let init_b = checker
        .add_initial_state(&s10, &mut get_successors, None)
        .unwrap();
    assert!(
        !init_b.is_empty(),
        "s10 should be added to graph — SCC-B must exist for multi-SCC isolation test"
    );
    let from_s10 = checker
        .add_successors(
            init_b[0],
            std::slice::from_ref(&s11),
            &mut get_successors,
            None,
        )
        .unwrap();
    assert!(
        !from_s10.is_empty(),
        "s11 should be added as successor of s10 — SCC-B must be fully constructed"
    );
    let _ = checker
        .add_successors(
            from_s10[0],
            std::slice::from_ref(&s10),
            &mut get_successors,
            None,
        )
        .unwrap();

    let plan = constraints_to_grouped_plan(checker.constraints());
    let result = checker.check_liveness_grouped(&plan, 0);
    match &result {
        LivenessResult::Violated { cycle, .. } => {
            // Violation should come from SCC-A (satisfies the negated formula).
            let x_vals: Vec<i64> = cycle
                .iter()
                .filter_map(|(s, _)| s.get("x").and_then(tla_value::Value::as_i64))
                .collect();
            assert!(!x_vals.is_empty(), "violation cycle must not be empty");
            // Cycle should contain SCC-A states (x=0 or x=1) only.
            for &x in &x_vals {
                assert!(
                    x == 0 || x == 1,
                    "violation cycle should contain only SCC-A states (x=0 or x=1), but found x={} — \
                     this suggests the checker reported a violation from the wrong SCC. All x values: {:?}",
                    x, x_vals
                );
            }
            // SCC-B states should never appear in the cycle.
            assert!(
                !x_vals.contains(&10) && !x_vals.contains(&11),
                "cycle should not contain SCC-B states (x=10 or x=11), got: {:?}",
                x_vals
            );
        }
        other => panic!(
            "expected Violated for SCC-A satisfying []<>(x=0), got: {:?}",
            other
        ),
    }
}

/// Regression test for #1932: build_scc_edges must return an error (not silently
/// drop) when an SCC contains a node that is missing from the behavior graph.
///
/// Before the fix, filter_map silently dropped missing nodes, which could hide
/// graph construction bugs and cause the liveness checker to incorrectly report
/// a property holds.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_build_scc_edges_missing_node_returns_error() {
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    let mut get_successors = empty_successors;

    // Add one real state to the graph
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .expect("add_initial_state must succeed for test setup");
    assert!(!init_nodes.is_empty());

    // Create an SCC that includes the real node AND a fabricated node
    // that was never added to the graph.
    let missing = BehaviorGraphNode::new(crate::state::Fingerprint(0xDEAD_BEEF_u64), 0);
    let scc = crate::liveness::tarjan::Scc::new(vec![init_nodes[0], missing]);

    // build_scc_edges should return an error, not silently drop the missing node
    let result = checker.build_scc_edges(&scc, None);
    let err = result.expect_err("build_scc_edges must error on missing SCC node");
    assert!(
        matches!(err, EvalError::Internal { .. }),
        "expected internal invariant error, got {err:?}"
    );
    assert!(
        err.to_string()
            .contains("behavior graph invariant violated"),
        "error message should mention invariant violation, got: {}",
        err
    );
}

/// Regression test for #1932: is_trivial_scc_with_ea_check must return an
/// error when the single SCC node is missing from the graph.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_trivial_scc_missing_node_returns_error() {
    let checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));

    let missing = BehaviorGraphNode::new(crate::state::Fingerprint(0xCAFE_FACE_u64), 0);
    let scc = crate::liveness::tarjan::Scc::new(vec![missing]);

    let result = checker.is_trivial_scc_with_ea_check(&scc, None);
    let err = result.expect_err("is_trivial_scc must error on missing node");
    assert!(
        matches!(err, EvalError::Internal { .. }),
        "expected internal invariant error, got {err:?}"
    );
}

/// Regression test for #1932: find_path_within_scc must return an error when
/// the start node is missing from the graph.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_find_path_within_scc_missing_node_returns_error() {
    let checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));

    let missing_a = BehaviorGraphNode::new(crate::state::Fingerprint(0xBAAD_F00D_u64), 0);
    let missing_b = BehaviorGraphNode::new(crate::state::Fingerprint(0xFEED_FACE_u64), 0);
    let scc_set = rustc_hash::FxHashSet::from_iter([missing_a, missing_b]);

    let result = checker.find_path_within_scc(missing_a, missing_b, &scc_set, None);
    let err = result.expect_err("find_path_within_scc must error on missing start node");
    assert!(
        matches!(err, EvalError::Internal { .. }),
        "expected internal invariant error, got {err:?}"
    );
}

/// Regression test for #1953: scc_fulfills_promises must return an error when
/// an SCC references a missing tableau node.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scc_fulfills_promises_missing_tableau_node_returns_error() {
    let checker = make_checker(LiveExpr::eventually(state_pred_x_eq(1, 1001)));

    let missing = BehaviorGraphNode::new(crate::state::Fingerprint(0xFACE_FEED_u64), usize::MAX);
    let scc = crate::liveness::tarjan::Scc::new(vec![missing]);

    let result = checker.scc_fulfills_promises(&scc);
    let err = result.expect_err("scc_fulfills_promises must error on missing tableau node");
    assert!(
        matches!(err, EvalError::Internal { .. }),
        "expected internal invariant error, got {err:?}"
    );
    assert!(
        err.to_string().contains("tableau invariant violated"),
        "error message should mention tableau invariant violation, got: {}",
        err
    );
}
