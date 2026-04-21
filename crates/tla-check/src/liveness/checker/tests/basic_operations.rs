// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checker creation, add_initial/successors, check_liveness basics, error edge cases
//!
//! Split from liveness/checker/tests.rs — Part of #2779

use super::helpers::state_pred_x_eq;
use super::*;
use crate::liveness::test_helpers::{constraints_to_grouped_plan, empty_successors, make_checker};
use crate::liveness::LiveExpr;
use crate::Value;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_liveness_checker_new() {
    // Create a simple tableau for []P
    let checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    assert_eq!(checker.stats().graph_nodes, 0);
    assert_eq!(checker.stats().states_explored, 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_add_initial_state() {
    // Create a tableau where []TRUE (always true) - all states should be consistent
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    let mut get_successors = empty_successors;

    let state = State::from_pairs([("x", Value::int(0))]);
    let added = checker
        .add_initial_state(&state, &mut get_successors, None)
        .unwrap();

    // Should have added at least one node
    assert!(!added.is_empty());
    assert_eq!(checker.graph().len(), added.len());
    // Verify the added nodes reference the correct state — a bug that inserted
    // a default/empty state would pass the count-only checks above.
    for node in &added {
        assert_eq!(
            node.state_fp,
            state.fingerprint(),
            "added node should reference the input state's fingerprint"
        );
        let stored = checker
            .graph()
            .get_state(node)
            .expect("node should exist in graph");
        assert_eq!(
            stored.get("x"),
            Some(&Value::int(0)),
            "stored state should preserve x=0"
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_add_successors() {
    // Create a simple tableau
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    let mut get_successors = empty_successors;

    // Add initial state
    let state0 = State::from_pairs([("x", Value::int(0))]);
    let added0 = checker
        .add_initial_state(&state0, &mut get_successors, None)
        .unwrap();
    assert!(!added0.is_empty());

    // Add successors
    let state1 = State::from_pairs([("x", Value::int(1))]);
    let added1 = checker
        .add_successors(
            added0[0],
            std::slice::from_ref(&state1),
            &mut get_successors,
            None,
        )
        .unwrap();

    // Verify successor nodes were actually created and connected — the old test
    // discarded `added1` with `let _ =` and only checked `graph().len() > 1`.
    assert!(
        !added1.is_empty(),
        "add_successors should have created new nodes for state1"
    );
    assert!(
        checker.graph().len() > 1,
        "graph should contain both initial and successor nodes"
    );
    assert!(
        checker.stats().graph_edges > 0,
        "edge count should be non-zero after adding successors"
    );
    // Verify the successor node stores the correct state value
    for node in &added1 {
        let stored = checker
            .graph()
            .get_state(node)
            .expect("successor node should exist in graph");
        assert_eq!(
            stored.get("x"),
            Some(&Value::int(1)),
            "successor stored state should have x=1"
        );
    }
    // Verify the initial node's adjacency list contains the actual successor node(s).
    // A non-emptiness-only check would miss a bug that creates edges pointing to the
    // wrong target (e.g., a self-loop on the initial node instead of an edge to state1).
    let init_info = checker
        .graph()
        .get_node_info(&added0[0])
        .expect("initial node should have info");
    assert!(
        !init_info.successors.is_empty(),
        "initial node should have at least one successor"
    );
    for succ_node in &added1 {
        assert!(
            init_info.successors.contains(succ_node),
            "initial node's adjacency list should contain successor {:?}",
            succ_node
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_liveness_no_cycle() {
    // Create a tableau where []TRUE - always satisfied
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    let mut get_successors = empty_successors;

    // Add a linear chain of states (no cycle)
    let state0 = State::from_pairs([("x", Value::int(0))]);
    let state1 = State::from_pairs([("x", Value::int(1))]);
    let state2 = State::from_pairs([("x", Value::int(2))]);

    let added0 = checker
        .add_initial_state(&state0, &mut get_successors, None)
        .unwrap();
    assert!(
        !added0.is_empty(),
        "add_initial_state must return at least one node for the no-cycle test to be meaningful"
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
        .add_successors(n1, std::slice::from_ref(&state2), &mut get_successors, None)
        .unwrap();

    // Should be satisfied (no accepting cycle)
    assert!(
        checker.stats().graph_nodes >= 3,
        "checker must have explored all 3 states, got {} graph nodes",
        checker.stats().graph_nodes
    );
    let plan = constraints_to_grouped_plan(checker.constraints());
    let result = checker.check_liveness_grouped(&plan, 0);
    assert!(matches!(result, LivenessResult::Satisfied));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_liveness_single_state_without_self_loop_is_satisfied() {
    // A singleton SCC without a self-loop is not an accepting cycle.
    // Ensure we don't report a violation when the graph has no cycle.
    let p = state_pred_x_eq(1, 1);
    let mut checker = make_checker(LiveExpr::always(LiveExpr::not(p)));
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .unwrap();
    assert_eq!(init_nodes.len(), 1);

    assert_eq!(
        checker.stats().graph_nodes,
        1,
        "single-state graph must have exactly 1 node"
    );
    let plan = constraints_to_grouped_plan(checker.constraints());
    let result = checker.check_liveness_grouped(&plan, 0);
    assert!(matches!(result, LivenessResult::Satisfied));
}

// ======== ERROR PATH TESTS ========

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_clone_state_for_bfs_missing_node_errors() {
    let checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    let missing = BehaviorGraphNode::new(crate::state::Fingerprint(0xBADC0FFE_u64), 0);

    let err = checker
        .clone_state_for_bfs(missing)
        .expect_err("missing BFS node must be an invariant error");
    assert!(
        matches!(err, EvalError::Internal { .. }),
        "expected internal invariant error, got {err:?}"
    );
    assert!(err.to_string().contains("BFS queue contains node"));
}

/// Test liveness on an empty graph (zero states). The checker should report
/// Satisfied since there are no SCCs (and hence no counterexample cycles).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_liveness_empty_graph() {
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));

    assert_eq!(
        checker.graph().len(),
        0,
        "graph should be empty before any states added"
    );
    let plan = constraints_to_grouped_plan(checker.constraints());
    let result = checker.check_liveness_grouped(&plan, 0);
    assert!(
        matches!(result, LivenessResult::Satisfied),
        "empty graph should be Satisfied (no SCC, no cycle), got: {:?}",
        result
    );
}

/// Regression test for #1953: grouped liveness checking must surface missing
/// tableau-node invariants as RuntimeFailure via the SCC promise path.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_liveness_grouped_missing_tableau_node_returns_runtime_failure() {
    let mut checker = make_checker(LiveExpr::eventually(state_pred_x_eq(1, 1004)));

    // Same malformed graph setup as non-grouped path test.
    let s0 = State::from_pairs([("x", Value::int(0))]);
    assert!(
        checker.graph.add_init_node(&s0, usize::MAX),
        "malformed initial node should be inserted"
    );
    let malformed = BehaviorGraphNode::from_state(&s0, usize::MAX);
    let _ = checker
        .graph
        .add_successor(malformed, &s0, usize::MAX)
        .expect("self-loop insertion on malformed node should succeed");

    let plan = GroupedLivenessPlan {
        tf: LiveExpr::Bool(true),
        check_state: Vec::new(),
        check_action: Vec::new(),
        pems: vec![PemPlan {
            ae_state_idx: Vec::new(),
            ae_action_idx: Vec::new(),
            ea_state_idx: Vec::new(),
            ea_action_idx: Vec::new(),
        }],
    };

    let result = checker.check_liveness_grouped(&plan, 0);
    match result {
        LivenessResult::RuntimeFailure { reason } => {
            assert!(
                reason.contains("error checking SCC promises"),
                "grouped path should report SCC promise errors, got: {}",
                reason
            );
            assert!(
                reason.contains("tableau invariant violated"),
                "error should preserve tableau invariant context, got: {}",
                reason
            );
        }
        other => panic!(
            "check_liveness_grouped must return RuntimeFailure for missing tableau node, got {:?}",
            other
        ),
    }
}

/// Part of #2236: add_successors must return an error (not silently return
/// empty) when the source node's tableau index is invalid.
///
/// Before the fix, an invalid tableau index in add_successors returned
/// `Ok(added)` (empty vec), silently truncating the behavior graph at that
/// node. This could cause false negatives in liveness checking.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_add_successors_invalid_tableau_idx_returns_error() {
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    // Fabricate a BehaviorGraphNode with a tableau index that doesn't exist
    // in the tableau (the tableau for []TRUE has only 2 nodes: 0 and 1).
    let bad_node = BehaviorGraphNode::new(s0.fingerprint(), usize::MAX);

    let result = checker.add_successors(
        bad_node,
        std::slice::from_ref(&s1),
        &mut get_successors,
        None,
    );
    let err = result.expect_err(
        "add_successors must return error for invalid tableau index, not silently return empty",
    );
    assert!(
        matches!(err, EvalError::Internal { .. }),
        "expected Internal error for missing tableau node, got {err:?}"
    );
    assert!(
        err.to_string().contains("missing tableau node"),
        "error should mention missing tableau node, got: {}",
        err
    );
    assert!(
        err.to_string().contains("add_successors"),
        "error should identify the call site (add_successors), got: {}",
        err
    );
}

/// Regression for DNF overflow handling:
/// checker planning must fail with an explicit error instead of silently
/// returning zero clauses (which could mask liveness violations).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_from_formula_grouped_dnf_overflow_returns_error() {
    // 20 binary disjunctions crossed by conjunction produce 2^20 clauses
    // (1,048,576), which exceeds LiveExpr::MAX_DNF_CLAUSES (500,000).
    let fairness_like_terms: Vec<LiveExpr> = (0u32..20)
        .map(|i| {
            LiveExpr::or(vec![
                state_pred_x_eq(i as i64, 5000 + i * 2),
                state_pred_x_eq(i as i64 + 100, 5000 + i * 2 + 1),
            ])
        })
        .collect();
    let formula = LiveExpr::and(fairness_like_terms);

    let result = LivenessChecker::from_formula_grouped(&formula);
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("DNF overflow must return an explicit error"),
    };
    let err_msg = err.to_string();
    assert!(
        err_msg.contains("DNF clause count exceeded limit"),
        "error should report DNF overflow, got: {err_msg}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_from_formula_dnf_overflow_returns_error() {
    let fairness_like_terms: Vec<LiveExpr> = (0u32..20)
        .map(|i| {
            LiveExpr::or(vec![
                state_pred_x_eq(i as i64, 6000 + i * 2),
                state_pred_x_eq(i as i64 + 100, 6000 + i * 2 + 1),
            ])
        })
        .collect();
    let formula = LiveExpr::and(fairness_like_terms);

    let result = LivenessChecker::from_formula(&formula, crate::eval::EvalCtx::new());
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("DNF overflow must return an explicit error"),
    };
    let err_msg = err.to_string();
    assert!(
        err_msg.contains("DNF clause count exceeded limit"),
        "error should report DNF overflow, got: {err_msg}"
    );
}
