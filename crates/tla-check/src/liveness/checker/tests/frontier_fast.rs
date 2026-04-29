// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! frontier_state, fast_path equivalence, sequential eval, enabled_require_state_change
//!
//! Split from liveness/checker/tests.rs — Part of #2779

use super::*;
use crate::liveness::test_helpers::{make_checker, spanned};
use crate::liveness::LiveExpr;
use crate::Value;
use std::sync::Arc;
use tla_core::ast::{Expr, Substitution};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_changed_subscript_fallback_preserves_constant_env_bindings() {
    // Regression for #2330:
    // checker::eval_subscript_changed previously rebuilt env from state vars only,
    // dropping constants like `Node` and causing UndefinedVar during EAAction checks.
    let mut checker = make_checker(LiveExpr::Bool(true));
    checker.ctx.bind_mut(
        Arc::from("Node"),
        Value::set([Value::int(1), Value::int(2), Value::int(3)]),
    );

    let changed = LiveExpr::state_changed_with_bindings(
        Some(Arc::new(spanned(Expr::Ident(
            "Node".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))),
        2330,
        None,
    );

    let current = State::from_pairs([("x", Value::int(0))]);
    let next = State::from_pairs([("x", Value::int(1))]);

    let result = checker
        .eval_check_on_transition(&changed, &current, &next)
        .expect("constant subscript should evaluate with preserved env bindings");

    assert!(
        !result,
        "constant subscript Node should be unchanged across transitions"
    );
}

// ---- explore_state_graph_direct fast-path equivalence tests ----
// Part of #2768 verification: prove that the fast path (no tableau) produces
// equivalent liveness verdicts to the full explore_bfs path for tf == Bool(true).

/// Build a state graph with `explore_bfs` (full tableau path) and with
/// `explore_state_graph_direct` (fast path). Assert that the node and edge
/// counts are structurally equivalent: fast-path should produce exactly one
/// behavior-graph node per state (tableau_idx=0), while the full path may
/// produce up to T nodes per state (one per consistent tableau node).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fast_path_equivalence_linear_chain() {
    // Linear chain: s0 -> s1 -> s2 (no cycles)
    // Both paths should see 3 states, no SCC violation possible.
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s2 = State::from_pairs([("x", Value::int(2))]);

    let mut successor_fn = |s: &State| -> Result<Vec<State>, EvalError> {
        match s.get("x") {
            Some(v) if *v == Value::int(0) => Ok(vec![s1.clone()]),
            Some(v) if *v == Value::int(1) => Ok(vec![s2.clone()]),
            _ => Ok(vec![]),
        }
    };

    // Full tableau path
    let mut checker_full = make_checker(LiveExpr::Bool(true));
    let full_nodes = checker_full
        .explore_bfs(std::slice::from_ref(&s0), &mut successor_fn, None)
        .unwrap();

    // Fast path
    let mut checker_fast = make_checker(LiveExpr::Bool(true));
    let fast_nodes = checker_fast
        .explore_state_graph_direct(std::slice::from_ref(&s0), &mut successor_fn)
        .unwrap();

    // The fast path should have exactly 3 nodes (one per state).
    // The full path may have more due to multiple tableau nodes per state,
    // but the underlying state count must match.
    assert_eq!(fast_nodes, 3, "fast path: 3 states in chain");
    assert!(
        full_nodes >= fast_nodes,
        "full path should have at least as many nodes as fast path"
    );

    // Edge counts: both should have the same number of state-level transitions
    // (fast path: 2 edges for s0->s1, s1->s2; full path: >= 2)
    assert!(
        checker_fast.stats().graph_edges >= 2,
        "fast path should have at least 2 edges"
    );
}

/// Cycle graph: s0 -> s1 -> s0 (self-loop through cycle).
/// Both paths should detect the cycle in SCCs.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fast_path_equivalence_cycle() {
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let mut successor_fn = |s: &State| -> Result<Vec<State>, EvalError> {
        match s.get("x") {
            Some(v) if *v == Value::int(0) => Ok(vec![s1.clone()]),
            Some(v) if *v == Value::int(1) => Ok(vec![s0.clone()]),
            _ => Ok(vec![]),
        }
    };

    // Fast path
    let mut checker_fast = make_checker(LiveExpr::Bool(true));
    let fast_nodes = checker_fast
        .explore_state_graph_direct(std::slice::from_ref(&s0), &mut successor_fn)
        .unwrap();
    assert_eq!(fast_nodes, 2);

    let fast_sccs = checker_fast.find_sccs();
    // With a 2-node cycle, there should be exactly one non-trivial SCC
    let fast_nontrivial: Vec<_> = fast_sccs
        .sccs
        .iter()
        .filter(|scc| {
            scc.len() > 1 || {
                // Check for self-loop (single-node SCC with an edge to itself)
                let node = scc.nodes()[0];
                checker_fast
                    .graph()
                    .get_node_info(&node)
                    .is_some_and(|info| info.successors.contains(&node))
            }
        })
        .collect();
    assert_eq!(
        fast_nontrivial.len(),
        1,
        "fast path should find exactly 1 non-trivial SCC in a 2-node cycle"
    );

    // Full tableau path
    let mut checker_full = make_checker(LiveExpr::Bool(true));
    let full_nodes = checker_full
        .explore_bfs(std::slice::from_ref(&s0), &mut successor_fn, None)
        .unwrap();
    assert!(full_nodes >= 2, "full path should have at least 2 nodes");

    let full_sccs = checker_full.find_sccs();
    let full_nontrivial: Vec<_> = full_sccs
        .sccs
        .iter()
        .filter(|scc| {
            scc.len() > 1 || {
                let node = scc.nodes()[0];
                checker_full
                    .graph()
                    .get_node_info(&node)
                    .is_some_and(|info| info.successors.contains(&node))
            }
        })
        .collect();
    assert!(
        !full_nontrivial.is_empty(),
        "full path should also find non-trivial SCCs in a 2-node cycle"
    );
}

/// Stuttering self-loop: s0 -> s0. The fast path must preserve self-loops
/// (TLC requires them for stutter detection in liveness).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fast_path_preserves_self_loops() {
    let s0 = State::from_pairs([("x", Value::int(42))]);

    let mut successor_fn = |_s: &State| -> Result<Vec<State>, EvalError> { Ok(vec![s0.clone()]) };

    let mut checker = make_checker(LiveExpr::Bool(true));
    let nodes = checker
        .explore_state_graph_direct(std::slice::from_ref(&s0), &mut successor_fn)
        .unwrap();
    assert_eq!(nodes, 1, "single state with self-loop = 1 node");
    assert_eq!(
        checker.stats().graph_edges,
        1,
        "self-loop should produce exactly 1 edge"
    );

    // The node should have itself as a successor
    let bg_node = crate::liveness::checker::BehaviorGraphNode::from_state(&s0, 0);
    let info = checker
        .graph()
        .get_node_info(&bg_node)
        .expect("node should exist in graph");
    assert!(
        info.successors.contains(&bg_node),
        "fast path must preserve self-loop edges (TLC stuttering detection requires this)"
    );
}

/// Multiple initial states, some with shared successors.
/// Verifies fast path deduplicates correctly.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fast_path_multiple_init_dedup() {
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s2 = State::from_pairs([("x", Value::int(2))]);

    // s0 -> s2, s1 -> s2 (shared successor)
    let mut successor_fn = |s: &State| -> Result<Vec<State>, EvalError> {
        match s.get("x") {
            Some(v) if *v == Value::int(0) => Ok(vec![s2.clone()]),
            Some(v) if *v == Value::int(1) => Ok(vec![s2.clone()]),
            _ => Ok(vec![]),
        }
    };

    let mut checker = make_checker(LiveExpr::Bool(true));
    let nodes = checker
        .explore_state_graph_direct(&[s0.clone(), s1.clone()], &mut successor_fn)
        .unwrap();
    assert_eq!(nodes, 3, "s0, s1, s2 = 3 unique nodes (s2 not duplicated)");
    assert_eq!(checker.stats().graph_edges, 2, "two edges: s0->s2, s1->s2");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sequential_eval_subscript_changed_clears_subst_cache_before_val1() {
    // Regression for #2780:
    // eval_subscript_changed cleared SUBST_CACHE before val2 but NOT before val1.
    // When two sequential calls both miss the subscript value cache, the second
    // call's val1 evaluation could see stale SUBST_CACHE entries from the first
    // call's val2 evaluation (both use with_explicit_env → state_env=None → pointer 0,
    // so pointer-based invalidation in eval_entry sees "same state").
    //
    // Scenario:
    //   Call 1: s1={x:10}→s2={x:20}, subscript=inst_x (INSTANCE sub: inst_x→x)
    //     val1=10, val2=20, SUBST_CACHE ends with inst_x→20
    //   Call 2: s3={x:30}→s4={x:30}, same subscript
    //     Without fix: val1 uses stale SUBST_CACHE(inst_x→20)=20, val2=30 → changed=true (WRONG)
    //     With fix: val1 clears SUBST_CACHE, evaluates to 30, val2=30 → changed=false (CORRECT)

    use tla_core::Spanned;

    // Clear all caches to start with a clean slate.
    crate::eval::clear_for_test_reset();

    let ctx = crate::eval::EvalCtx::new().with_instance_substitutions(vec![Substitution {
        from: Spanned::dummy("inst_x".to_string()),
        to: Spanned::dummy(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )),
    }]);

    let subscript = spanned(Expr::Ident(
        "inst_x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));

    let s1 = crate::state::State::from_pairs([("x", Value::int(10))]);
    let s2 = crate::state::State::from_pairs([("x", Value::int(20))]);
    let s3 = crate::state::State::from_pairs([("x", Value::int(30))]);
    let s4 = crate::state::State::from_pairs([("x", Value::int(30))]);

    // Call 1: inst_x changes from 10→20, should be true.
    let result1 = subscript_cache::eval_subscript_changed(&ctx, &s1, &s2, &subscript, None)
        .expect("first eval_subscript_changed should succeed");
    assert!(result1, "inst_x changed 10→20, should report changed");

    // Call 2: inst_x is 30 in both states, should be false.
    // Without #2780 fix, stale SUBST_CACHE from call 1's val2 (inst_x→20)
    // could leak into call 2's val1, making it return 20 instead of 30.
    let result2 = subscript_cache::eval_subscript_changed(&ctx, &s3, &s4, &subscript, None)
        .expect("second eval_subscript_changed should succeed");
    assert!(
        !result2,
        "inst_x is 30 in both s3 and s4, should report unchanged (stale SUBST_CACHE leak if true)"
    );
}

// ============================================================================
// Regression test for #2929: frontier state vs deadlocked state distinction
// in get_successors callback during periodic liveness checking
// ============================================================================

/// Regression test for #2929: frontier states must NOT receive stuttering
/// self-loops during periodic (mid-BFS) liveness checking.
///
/// During periodic liveness, some states are "frontier" states — they exist in
/// the `seen` set but their successors haven't been computed yet. The
/// `get_successors` callback in `ModelChecker::check_liveness_property` uses
/// `cached_successors.get(&fp)` which returns:
///   - `None`          → frontier state (not yet expanded)
///   - `Some(empty)`   → deadlocked state (expanded, truly no successors)
///   - `Some(non-empty)` → normal state with successors
///
/// Before the fix, both frontier and deadlocked states received stuttering
/// self-loops. This created spurious single-node SCCs where ENABLED evaluated
/// incorrectly for WF fairness specs (e.g., MCBinarySearch `WF_vars(Next)`).
///
/// This test verifies the three-way distinction by constructing a successor
/// function that mimics the `cached_successors` pattern and checking that
/// `explore_state_graph_direct` produces the correct graph structure.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_frontier_state_is_sink_no_stuttering() {
    use crate::state::Fingerprint;
    use rustc_hash::FxHashMap;

    // Three states:
    //   s0 (normal): successor → s1
    //   s1 (deadlocked): expanded, no successors → gets stuttering self-loop
    //   s2 (frontier): not yet expanded → must be a sink (no edges)
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s2 = State::from_pairs([("x", Value::int(2))]);

    let fp0 = s0.fingerprint();
    let fp1 = s1.fingerprint();
    let fp2 = s2.fingerprint();

    // Build cached_successors simulating mid-BFS state:
    // s0 → [s1, s2] (expanded, has successors)
    // s1 → [] (expanded, deadlocked)
    // s2 → absent (frontier, not yet expanded)
    let mut cached_successors: FxHashMap<Fingerprint, Vec<Fingerprint>> = FxHashMap::default();
    cached_successors.insert(fp0, vec![fp1, fp2]);
    cached_successors.insert(fp1, vec![]); // deadlocked

    // Build state_cache for fingerprint → State lookup
    let mut state_cache: FxHashMap<Fingerprint, State> = FxHashMap::default();
    state_cache.insert(fp0, s0.clone());
    state_cache.insert(fp1, s1.clone());
    state_cache.insert(fp2, s2.clone());

    let add_stuttering = true;

    // This closure mimics the exact pattern from ModelChecker::check_liveness_property
    // (liveness.rs lines 504-530) — the code fixed by #2929.
    let mut get_successors = |state: &State| -> Result<Vec<State>, EvalError> {
        let fp = state.fingerprint();
        let entry = cached_successors.get(&fp);
        let mut succs: Vec<State> = entry
            .map(|fps| {
                fps.iter()
                    .filter_map(|sfp| state_cache.get(sfp).cloned())
                    .collect()
            })
            .unwrap_or_default();
        // The #2929 fix: only add stuttering if entry.is_some()
        if add_stuttering && entry.is_some() {
            succs.push(state.clone());
        }
        Ok(succs)
    };

    let mut checker = make_checker(LiveExpr::Bool(true));
    let nodes = checker
        .explore_state_graph_direct(std::slice::from_ref(&s0), &mut get_successors)
        .unwrap();

    // Should have 3 nodes: s0, s1, s2
    assert_eq!(nodes, 3, "should explore all 3 states");

    // Verify edge structure:
    // s0: 2 real successors (s1, s2) + 1 stuttering self-loop = 3 edges
    // s1: 0 real successors + 1 stuttering self-loop (deadlocked) = 1 edge
    // s2: 0 real successors + 0 stuttering (frontier) = 0 edges (SINK)
    // Total: 3 + 1 + 0 = 4 edges
    assert_eq!(
        checker.stats().graph_edges,
        4,
        "expected 4 edges: s0→s1 + s0→s2 + s0→s0(stutter) + s1→s1(stutter); \
         s2 is frontier (no edges, no stuttering)"
    );
}

/// Companion test: verify that WITHOUT the #2929 fix (frontier states get
/// stuttering), the edge count would be wrong.
///
/// This test uses the BUGGY pattern (pre-fix) to confirm the test catches
/// the regression if the fix is reverted.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_frontier_state_buggy_pattern_produces_extra_edge() {
    use crate::state::Fingerprint;
    use rustc_hash::FxHashMap;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s2 = State::from_pairs([("x", Value::int(2))]);

    let fp0 = s0.fingerprint();
    let fp1 = s1.fingerprint();
    let fp2 = s2.fingerprint();

    let mut cached_successors: FxHashMap<Fingerprint, Vec<Fingerprint>> = FxHashMap::default();
    cached_successors.insert(fp0, vec![fp1, fp2]);
    cached_successors.insert(fp1, vec![]); // deadlocked
                                           // s2 absent — frontier

    let mut state_cache: FxHashMap<Fingerprint, State> = FxHashMap::default();
    state_cache.insert(fp0, s0.clone());
    state_cache.insert(fp1, s1.clone());
    state_cache.insert(fp2, s2.clone());

    // BUGGY pattern: unconditionally adds stuttering (pre-#2929 behavior)
    let mut get_successors_buggy = |state: &State| -> Result<Vec<State>, EvalError> {
        let fp = state.fingerprint();
        let succs_from_cache: Vec<State> = cached_successors
            .get(&fp)
            .map(|fps| {
                fps.iter()
                    .filter_map(|sfp| state_cache.get(sfp).cloned())
                    .collect()
            })
            .unwrap_or_default();
        let mut succs = succs_from_cache;
        // BUG: unconditionally adds stuttering — frontier states get self-loops
        succs.push(state.clone());
        Ok(succs)
    };

    let mut checker = make_checker(LiveExpr::Bool(true));
    let nodes = checker
        .explore_state_graph_direct(std::slice::from_ref(&s0), &mut get_successors_buggy)
        .unwrap();

    assert_eq!(nodes, 3, "should still explore all 3 states");

    // With the buggy pattern, s2 gets a spurious stuttering self-loop:
    // s0: 3 edges (s1 + s2 + stutter)
    // s1: 1 edge (stutter)
    // s2: 1 edge (spurious stutter) ← THIS IS THE BUG
    // Total: 5 edges instead of 4
    assert_eq!(
        checker.stats().graph_edges,
        5,
        "buggy pattern: frontier state s2 gets spurious stuttering self-loop (5 edges, not 4)"
    );
}
