// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Inline cache reconstruction tests for `populate_node_check_masks_with_inline_cache`.
//!
//! Split from check_masks.rs — Part of #3683

use super::super::subscript_cache;
use super::*;
use crate::liveness::test_helpers::{empty_successors, make_checker_with_vars, spanned};
use crate::liveness::LiveExpr;
use crate::Value;
use std::sync::Arc;
use tla_core::ast::Expr;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_populate_node_check_masks_skips_subscript_precompute_on_all_cached_actions() {
    let mut checker = make_checker_with_vars(LiveExpr::always(LiveExpr::Bool(true)), &["x"]);
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .expect("add_initial_state");
    let n0 = init_nodes[0];
    let _ = checker
        .add_successors(n0, std::slice::from_ref(&s1), &mut get_successors, None)
        .expect("add_successors s0->s1");

    let tag: u32 = 3;
    let subscript = Arc::new(spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    )));
    let check_action = vec![LiveExpr::state_changed(Some(Arc::clone(&subscript)), tag)];

    // Part of #3174: Use inline bitmask results instead of per-tag cross caches.
    let mut inline_action_bitmasks: FxHashMap<
        (crate::state::Fingerprint, crate::state::Fingerprint),
        u64,
    > = FxHashMap::default();
    *inline_action_bitmasks
        .entry((s0.fingerprint(), s1.fingerprint()))
        .or_default() |= 1u64 << tag;
    let inline_state_bitmasks: FxHashMap<crate::state::Fingerprint, u64> = FxHashMap::default();
    let inline_results = InlineCheckResults {
        max_tag: tag,
        state_bitmasks: &inline_state_bitmasks,
        action_bitmasks: &inline_action_bitmasks,
    };

    checker
        .populate_node_check_masks_with_inline_cache(
            &check_action,
            &[],
            &[true],
            &[],
            tag,
            Some(inline_results),
            None,
        )
        .expect("populate_node_check_masks should reconstruct all-cached action masks");

    let info = checker.graph().get_node_info(&n0).unwrap();
    assert!(
        info.action_check_masks.first().is_some_and(|m| m.get(0)),
        "all-cached action mask should be reconstructed from inline bitmask cache"
    );
    assert!(
        subscript_cache::get_subscript_value_cached(s0.fingerprint(), tag).is_none(),
        "all-cached path should skip subscript precompute for the source state"
    );
    assert!(
        subscript_cache::get_subscript_value_cached(s1.fingerprint(), tag).is_none(),
        "all-cached path should skip subscript precompute for the destination state"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_populate_node_check_masks_reconstructs_property_scoped_inline_cache() {
    let mut checker = make_checker_with_vars(LiveExpr::always(LiveExpr::Bool(true)), &["x"]);
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .expect("add_initial_state");
    let n0 = init_nodes[0];
    let _ = checker
        .add_successors(n0, std::slice::from_ref(&s1), &mut get_successors, None)
        .expect("add_successors s0->s1");

    let property_state_tag: u32 = 5;
    let property_action_tag: u32 = 6;
    let subscript = Arc::new(spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    )));
    let check_state = vec![super::helpers::state_pred_x_eq(0, property_state_tag)];
    let check_action = vec![LiveExpr::state_changed(
        Some(Arc::clone(&subscript)),
        property_action_tag,
    )];
    let mut inline_state_bitmasks: FxHashMap<crate::state::Fingerprint, u64> = FxHashMap::default();
    // s0: property_state_tag = true → set bit
    *inline_state_bitmasks.entry(s0.fingerprint()).or_default() |= 1u64 << property_state_tag;
    // s1: property_state_tag = false → 0 bits (but fp present = evaluated)
    inline_state_bitmasks.entry(s1.fingerprint()).or_default();
    let mut inline_action_bitmasks: FxHashMap<
        (crate::state::Fingerprint, crate::state::Fingerprint),
        u64,
    > = FxHashMap::default();
    // s0->s1: property_action_tag = true
    *inline_action_bitmasks
        .entry((s0.fingerprint(), s1.fingerprint()))
        .or_default() |= 1u64 << property_action_tag;
    let inline_results = InlineCheckResults {
        max_tag: property_action_tag,
        state_bitmasks: &inline_state_bitmasks,
        action_bitmasks: &inline_action_bitmasks,
    };

    checker
        .populate_node_check_masks_with_inline_cache(
            &check_action,
            &check_state,
            &[true],
            &[true],
            0,
            Some(inline_results),
            None,
        )
        .expect("populate_node_check_masks should reconstruct property-scoped inline cache");

    let info = checker.graph().get_node_info(&n0).unwrap();
    assert!(
        info.state_check_mask.get(0),
        "state mask should be reconstructed from inline state_results"
    );
    assert!(
        info.action_check_masks.first().is_some_and(|m| m.get(0)),
        "action mask should be reconstructed from inline action_results"
    );
    assert!(
        subscript_cache::get_subscript_value_cached(s0.fingerprint(), property_action_tag)
            .is_none(),
        "property-scoped inline cache should skip subscript precompute for the source state"
    );
    assert!(
        subscript_cache::get_subscript_value_cached(s1.fingerprint(), property_action_tag)
            .is_none(),
        "property-scoped inline cache should skip subscript precompute for the destination state"
    );
}

/// Part of #3174: Verify bitmask-only reconstruction with complete property-scoped
/// inline caches. BFS guarantees all reachable states and transitions have bitmask
/// entries before SCC checking runs.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_populate_node_check_masks_property_inline_cache_complete() {
    let mut checker = make_checker_with_vars(LiveExpr::always(LiveExpr::Bool(true)), &["x"]);
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .expect("add_initial_state");
    let n0 = init_nodes[0];
    let _ = checker
        .add_successors(n0, std::slice::from_ref(&s1), &mut get_successors, None)
        .expect("add_successors s0->s1");

    let property_state_tag: u32 = 7;
    let property_action_tag: u32 = 8;
    let subscript = Arc::new(spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    )));
    let check_state = vec![super::helpers::state_pred_x_eq(0, property_state_tag)];
    let check_action = vec![LiveExpr::state_changed(
        Some(Arc::clone(&subscript)),
        property_action_tag,
    )];
    // Complete bitmask data as BFS would produce:
    let mut inline_state_bitmasks: FxHashMap<crate::state::Fingerprint, u64> = FxHashMap::default();
    // s0 satisfies state_pred(x=0), s1 does not.
    *inline_state_bitmasks.entry(s0.fingerprint()).or_default() |= 1u64 << property_state_tag;
    inline_state_bitmasks.entry(s1.fingerprint()).or_default();
    // Action bitmask: s0→s1 changes x, so StateChanged is true.
    let mut inline_action_bitmasks: FxHashMap<
        (crate::state::Fingerprint, crate::state::Fingerprint),
        u64,
    > = FxHashMap::default();
    *inline_action_bitmasks
        .entry((s0.fingerprint(), s1.fingerprint()))
        .or_default() |= 1u64 << property_action_tag;
    let inline_results = InlineCheckResults {
        max_tag: property_action_tag,
        state_bitmasks: &inline_state_bitmasks,
        action_bitmasks: &inline_action_bitmasks,
    };

    checker
        .populate_node_check_masks_with_inline_cache(
            &check_action,
            &check_state,
            &[true],
            &[true],
            0,
            Some(inline_results),
            None,
        )
        .expect("complete inline cache should reconstruct masks via bitmask fast path");

    let info = checker.graph().get_node_info(&n0).unwrap();
    assert!(
        info.state_check_mask.get(0),
        "state mask for s0 (x=0) should be true via bitmask reconstruction"
    );
    assert!(
        info.action_check_masks.first().is_some_and(|m| m.get(0)),
        "action mask for s0→s1 should be true (x changed) via bitmask reconstruction"
    );
}

/// Part of #3100: Test bitmask-indexed fast path (tags < 64) for cache reconstruction.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_populate_node_check_masks_bitmask_fast_path() {
    let mut checker = make_checker_with_vars(LiveExpr::always(LiveExpr::Bool(true)), &["x"]);
    let mut get_successors = empty_successors;
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let n0 = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .expect("init")[0];
    let n1 = checker
        .add_successors(n0, std::slice::from_ref(&s1), &mut get_successors, None)
        .expect("s0->s1")[0];
    let _ = checker
        .add_successors(n1, std::slice::from_ref(&s0), &mut get_successors, None)
        .expect("s1->s0");

    // Small tags (< 64) trigger bitmask fast path.
    let (state_tag, action_tag): (u32, u32) = (1, 2);
    let check_state = vec![super::helpers::state_pred_x_eq(0, state_tag)];
    let subscript = Arc::new(spanned(Expr::Ident(
        "x".into(),
        tla_core::name_intern::NameId::INVALID,
    )));
    let check_action = vec![LiveExpr::state_changed(Some(subscript), action_tag)];

    // Pre-populate inline caches as if BFS already evaluated these (bitmask-only).
    let mut state_bitmasks: FxHashMap<crate::state::Fingerprint, u64> = FxHashMap::default();
    // s0: state_tag=true → set bit
    *state_bitmasks.entry(s0.fingerprint()).or_default() |= 1u64 << state_tag;
    // s1: state_tag=false → entry present but bit not set
    state_bitmasks.entry(s1.fingerprint()).or_default();
    let mut action_bitmasks: FxHashMap<
        (crate::state::Fingerprint, crate::state::Fingerprint),
        u64,
    > = FxHashMap::default();
    // s0->s1: action_tag=true → set bit
    *action_bitmasks
        .entry((s0.fingerprint(), s1.fingerprint()))
        .or_default() |= 1u64 << action_tag;
    // s1->s0: action_tag=false → entry present but bit not set
    action_bitmasks
        .entry((s1.fingerprint(), s0.fingerprint()))
        .or_default();
    let inline = InlineCheckResults {
        max_tag: action_tag,
        state_bitmasks: &state_bitmasks,
        action_bitmasks: &action_bitmasks,
    };

    checker
        .populate_node_check_masks_with_inline_cache(
            &check_action,
            &check_state,
            &[true],
            &[true],
            0,
            Some(inline),
            None,
        )
        .expect("bitmask fast path should reconstruct masks correctly");

    let n0_info = checker.graph().get_node_info(&n0).unwrap();
    let n1_info = checker.graph().get_node_info(&n1).unwrap();
    assert!(
        n0_info.state_check_mask.get(0),
        "state check should pass on s0"
    );
    assert!(
        !n1_info.state_check_mask.get(0),
        "state check should fail on s1"
    );
    assert!(
        n0_info.action_check_masks.first().is_some_and(|m| m.get(0)),
        "action check should pass on s0->s1"
    );
    assert!(
        !n1_info.action_check_masks.first().is_some_and(|m| m.get(0)),
        "action check should fail on s1->s0"
    );
}

/// Part of #3100: Test bitmask path with compound check expressions (And/Not).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_populate_node_check_masks_bitmask_compound_checks() {
    let mut checker = make_checker_with_vars(LiveExpr::always(LiveExpr::Bool(true)), &["x"]);
    let mut get_successors = empty_successors;
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let n0 = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .expect("init")[0];
    let _ = checker
        .add_successors(n0, std::slice::from_ref(&s1), &mut get_successors, None)
        .expect("s0->s1");

    // Compound: And(StatePred(3), Not(StatePred(4)))
    // s0: tag3=true, tag4=false → And(true,Not(false)) = true
    let (tag_a, tag_b): (u32, u32) = (3, 4);
    let dummy = Arc::new(spanned(Expr::Ident(
        "x".into(),
        tla_core::name_intern::NameId::INVALID,
    )));
    let check_state = vec![LiveExpr::and(vec![
        LiveExpr::state_pred(Arc::clone(&dummy), tag_a),
        LiveExpr::not(LiveExpr::state_pred(Arc::clone(&dummy), tag_b)),
    ])];
    let mut state_bitmasks: FxHashMap<crate::state::Fingerprint, u64> = FxHashMap::default();
    // s0: tag_a=true, tag_b=false → set bit for tag_a only
    *state_bitmasks.entry(s0.fingerprint()).or_default() |= 1u64 << tag_a;
    // s1: tag_a=false, tag_b=true → set bit for tag_b only
    *state_bitmasks.entry(s1.fingerprint()).or_default() |= 1u64 << tag_b;
    let action_bitmasks: FxHashMap<(crate::state::Fingerprint, crate::state::Fingerprint), u64> =
        FxHashMap::default();
    let inline = InlineCheckResults {
        max_tag: tag_b,
        state_bitmasks: &state_bitmasks,
        action_bitmasks: &action_bitmasks,
    };

    checker
        .populate_node_check_masks_with_inline_cache(
            &[],
            &check_state,
            &[],
            &[true],
            0,
            Some(inline),
            None,
        )
        .expect("bitmask compound check should work");

    assert!(
        checker
            .graph()
            .get_node_info(&n0)
            .unwrap()
            .state_check_mask
            .get(0),
        "And(tag_a=true, Not(tag_b=false)) should pass on s0"
    );
}
