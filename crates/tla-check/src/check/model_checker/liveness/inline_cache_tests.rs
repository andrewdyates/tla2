// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for inline liveness cache: preparation, recording, fingerprint mapping,
//! successor witnesses, init-term checking, and action-only property rebinding.

use super::*;
use crate::check::model_checker::CheckResult;
use crate::config::Config;
use crate::liveness::LiveExpr;
use crate::state::{ArrayState, State};
use crate::test_support::parse_module;
use crate::Value;
use crate::{set_liveness_disk_bitmask_flush_threshold_override, set_use_disk_bitmasks_override};
use rustc_hash::FxHashMap;

const INLINE_PROPERTY_SPEC: &str = r#"
---- MODULE InlineProperty ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Prop == []<>(x = 0)
====
"#;

const INLINE_ACTION_ONLY_PROPERTY_SPEC: &str = r#"
---- MODULE InlineActionOnlyProperty ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = 1 - x
OnlyFromZero == x = 0 /\ x' = 1
Prop == []<>OnlyFromZero
====
"#;

fn property_config() -> Config {
    Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn prepare_inline_liveness_cache_collects_property_leaves() {
    let module = parse_module(INLINE_PROPERTY_SPEC);
    let config = property_config();

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    checker.prepare_inline_liveness_cache();

    let plan = checker
        .inline_property_plan("Prop")
        .expect("property inline plan should be cached");
    assert_eq!(
        plan.grouped_plans.len(),
        1,
        "simple property should yield one grouped plan"
    );
    assert_eq!(
        plan.state_leaves.len(),
        1,
        "[]<>(x=0) should contribute one state leaf"
    );
    assert_eq!(
        plan.action_leaves.len(),
        0,
        "state-only property should not contribute action leaves"
    );
    assert!(
        plan.max_cached_tag >= plan.max_fairness_tag,
        "property cache should cover at least the fairness tags"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn record_inline_liveness_results_records_property_state_results() {
    let module = parse_module(INLINE_PROPERTY_SPEC);
    let config = property_config();

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    checker.prepare_inline_liveness_cache();

    let registry = checker.ctx.var_registry().clone();
    let current = State::from_pairs([("x", Value::int(0))]);
    let next = State::from_pairs([("x", Value::int(1))]);
    let current_arr = ArrayState::from_state(&current, &registry);
    let next_arr = ArrayState::from_state(&next, &registry);

    checker
        .record_inline_liveness_results(
            current.fingerprint(),
            &current_arr,
            &[(next_arr, next.fingerprint())],
            &[],
        )
        .expect("property inline results should record successfully");

    let plan = checker
        .inline_property_plan("Prop")
        .expect("property inline plan should remain available");
    let tag = plan
        .state_leaves
        .iter()
        .find_map(LiveExpr::tag)
        .expect("state leaf should have a stable tag");
    let bitmask = plan
        .state_bitmasks
        .get(&current.fingerprint())
        .expect("state bitmask should exist for current fingerprint");
    assert!(
        bitmask & (1u64 << tag) != 0,
        "current state x=0 should satisfy []<> leaf body x=0"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn record_inline_liveness_results_uses_graph_fingerprints() {
    let module = parse_module(INLINE_PROPERTY_SPEC);
    let config = property_config();

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    checker.prepare_inline_liveness_cache();

    let registry = checker.ctx.var_registry().clone();
    let current = State::from_pairs([("x", Value::int(0))]);
    let next = State::from_pairs([("x", Value::int(1))]);
    let current_arr = ArrayState::from_state(&current, &registry);
    let next_arr = ArrayState::from_state(&next, &registry);
    let graph_current_fp = Fingerprint(current.fingerprint().0.wrapping_add(17));
    let graph_next_fp = Fingerprint(next.fingerprint().0.wrapping_add(31));

    checker
        .record_inline_liveness_results(
            graph_current_fp,
            &current_arr,
            &[(next_arr, graph_next_fp)],
            &[],
        )
        .expect("property inline results should use BFS graph fingerprints");

    let plan = checker
        .inline_property_plan("Prop")
        .expect("property inline plan should remain available");
    let tag = plan
        .state_leaves
        .iter()
        .find_map(LiveExpr::tag)
        .expect("state leaf should have a stable tag");
    let bitmask = plan
        .state_bitmasks
        .get(&graph_current_fp)
        .expect("state bitmask should exist for graph fingerprint");
    assert!(
        bitmask & (1u64 << tag) != 0,
        "property inline cache should be keyed by graph fingerprint, not State::fingerprint()",
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn build_state_fp_to_canon_fp_registers_raw_state_fingerprints() {
    let module = parse_module(INLINE_PROPERTY_SPEC);
    let config = property_config();
    let mut checker = ModelChecker::new(&module, &config);
    let registry = checker.ctx.var_registry().clone();

    let current = State::from_pairs([("x", Value::int(0))]);
    let canon_fp = Fingerprint(current.fingerprint().0.wrapping_add(41));

    checker
        .state_storage
        .seen
        .insert(canon_fp, ArrayState::from_state(&current, &registry));

    let fp_map = checker.build_state_fp_to_canon_fp(&registry);

    assert_eq!(
        fp_map.get(&current.fingerprint()),
        Some(&canon_fp),
        "raw state fingerprint must map to the canonical graph fingerprint"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn build_successor_witnesses_registers_raw_successor_fingerprints() {
    let module = parse_module(INLINE_PROPERTY_SPEC);
    let config = property_config();
    let mut checker = ModelChecker::new(&module, &config);
    let registry = checker.ctx.var_registry().clone();

    let current = State::from_pairs([("x", Value::int(0))]);
    let witness = State::from_pairs([("x", Value::int(1))]);
    let canon_fp = current.fingerprint();

    checker.liveness_cache.successor_witnesses.insert(
        canon_fp,
        vec![(canon_fp, ArrayState::from_state(&witness, &registry))],
    );

    let mut fp_map = FxHashMap::default();
    fp_map.insert(current.fingerprint(), canon_fp);

    let succ_witnesses = checker
        .build_successor_witnesses(&registry, &mut fp_map)
        .expect("successor witness cache should convert to liveness witness map");

    assert_eq!(
        fp_map.get(&witness.fingerprint()),
        Some(&canon_fp),
        "raw witness fingerprint must map back to the canonical destination"
    );
    let witness_list = succ_witnesses
        .get(&canon_fp)
        .expect("converted witness map should contain the source fingerprint");
    assert_eq!(
        witness_list.len(),
        1,
        "expected one concrete successor witness"
    );
    assert_eq!(
        witness_list[0].0, canon_fp,
        "witness entry should retain the canonical destination fingerprint"
    );
    // Part of #2661: SuccessorWitnessMap now stores ArrayState. Verify the
    // value by converting back to State and comparing.
    let converted_state = witness_list[0].1.to_state(&registry);
    assert_eq!(
        converted_state.get("x"),
        witness.get("x"),
        "converted witness map should preserve the concrete successor state"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn check_init_terms_uses_cached_array_states() {
    let module = parse_module(INLINE_PROPERTY_SPEC);
    let config = property_config();
    let mut checker = ModelChecker::new(&module, &config);
    let registry = checker.ctx.var_registry().clone();
    let init_term = checker
        .module
        .op_defs
        .get("Init")
        .expect("Init should exist")
        .body
        .clone();

    let passing_init = State::from_pairs([("x", Value::int(0))]);
    let passing_cache = vec![(
        passing_init.fingerprint(),
        ArrayState::from_state(&passing_init, &registry),
    )];
    assert!(
        checker
            .check_init_terms("Prop", std::slice::from_ref(&init_term), &passing_cache)
            .is_none(),
        "cached array-backed init states should satisfy true init terms"
    );

    let failing_init = State::from_pairs([("x", Value::int(1))]);
    let failing_cache = vec![(
        failing_init.fingerprint(),
        ArrayState::from_state(&failing_init, &registry),
    )];
    let result = checker
        .check_init_terms("Prop", std::slice::from_ref(&init_term), &failing_cache)
        .expect("false init term should report a violation");

    match result {
        CheckResult::PropertyViolation {
            property,
            kind,
            trace,
            ..
        } => {
            assert_eq!(property, "Prop");
            assert_eq!(kind, crate::check::api::PropertyViolationKind::StateLevel);
            assert_eq!(
                trace.states.len(),
                1,
                "init violation should have a 1-state trace"
            );
            assert_eq!(
                trace.states[0].get("x"),
                failing_init.get("x"),
                "trace should reconstruct the cached init state"
            );
        }
        other => panic!("expected property violation, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn action_only_inline_property_rebinds_state_boundary_per_parent() {
    let module = parse_module(INLINE_ACTION_ONLY_PROPERTY_SPEC);
    let config = property_config();

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    checker.prepare_inline_liveness_cache();

    let plan = checker
        .inline_property_plan("Prop")
        .expect("action-only property inline plan should be cached");
    assert!(
        plan.state_leaves.is_empty(),
        "action-only property should not synthesize state leaves"
    );
    assert_eq!(
        plan.action_leaves.len(),
        1,
        "action-only property should contribute exactly one action leaf"
    );

    let registry = checker.ctx.var_registry().clone();
    let zero = State::from_pairs([("x", Value::int(0))]);
    let one = State::from_pairs([("x", Value::int(1))]);
    let zero_arr = ArrayState::from_state(&zero, &registry);
    let one_arr = ArrayState::from_state(&one, &registry);

    checker
        .record_inline_liveness_results(
            zero.fingerprint(),
            &zero_arr,
            &[(one_arr.clone(), one.fingerprint())],
            &[],
        )
        .expect("0 -> 1 transition should record inline action result");
    checker
        .record_inline_liveness_results(
            one.fingerprint(),
            &one_arr,
            &[(zero_arr, zero.fingerprint())],
            &[],
        )
        .expect("1 -> 0 transition should record inline action result");

    let plan = checker
        .inline_property_plan("Prop")
        .expect("action-only property inline plan should remain cached");
    let tag = plan
        .action_leaves
        .iter()
        .find_map(LiveExpr::tag)
        .expect("action leaf should have a stable tag");
    let forward_bits = plan
        .action_bitmasks
        .get(&(zero.fingerprint(), one.fingerprint()))
        .expect("0 -> 1 action bitmask should be cached");
    let forward = forward_bits & (1u64 << tag) != 0;
    let backward_bits = plan
        .action_bitmasks
        .get(&(one.fingerprint(), zero.fingerprint()))
        .expect("1 -> 0 action bitmask should be cached");
    let backward = backward_bits & (1u64 << tag) != 0;

    assert_ne!(
        forward, backward,
        "action-only inline caching must re-evaluate against the new parent state instead of reusing the prior inline result"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn action_only_inline_property_uses_disk_action_bitmasks() {
    let _disk_bitmasks = set_use_disk_bitmasks_override(true);
    let _flush_threshold = set_liveness_disk_bitmask_flush_threshold_override(Some(1));

    let module = parse_module(INLINE_ACTION_ONLY_PROPERTY_SPEC);
    let config = property_config();

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    // Disable stuttering so the len assertion below counts only the 2
    // explicitly-recorded transitions (zero→one, one→zero) without the
    // additional stuttering self-loops (zero→zero, one→one).
    checker.set_stuttering_allowed(false);
    checker.prepare_inline_liveness_cache();

    let plan = checker
        .inline_property_plan("Prop")
        .expect("action-only property inline plan should be cached");
    assert!(
        plan.action_bitmasks.is_disk(),
        "action-only property should switch to the disk-backed action bitmask backend",
    );

    let registry = checker.ctx.var_registry().clone();
    let zero = State::from_pairs([("x", Value::int(0))]);
    let one = State::from_pairs([("x", Value::int(1))]);
    let zero_arr = ArrayState::from_state(&zero, &registry);
    let one_arr = ArrayState::from_state(&one, &registry);

    checker
        .record_inline_liveness_results(
            zero.fingerprint(),
            &zero_arr,
            &[(one_arr.clone(), one.fingerprint())],
            &[],
        )
        .expect("0 -> 1 transition should record inline action result with disk bitmasks");
    checker
        .record_inline_liveness_results(
            one.fingerprint(),
            &one_arr,
            &[(zero_arr, zero.fingerprint())],
            &[],
        )
        .expect("1 -> 0 transition should record inline action result with disk bitmasks");

    let plan = checker
        .inline_property_plan("Prop")
        .expect("action-only property inline plan should remain cached");
    let tag = plan
        .action_leaves
        .iter()
        .find_map(LiveExpr::tag)
        .expect("action leaf should have a stable tag");
    let forward_bits = plan
        .action_bitmasks
        .get(&(zero.fingerprint(), one.fingerprint()))
        .expect("0 -> 1 action bitmask should be cached on disk-backed backend");
    let forward = forward_bits & (1u64 << tag) != 0;
    let backward_bits = plan
        .action_bitmasks
        .get(&(one.fingerprint(), zero.fingerprint()))
        .expect("1 -> 0 action bitmask should be cached on disk-backed backend");
    let backward = backward_bits & (1u64 << tag) != 0;

    assert_eq!(
        plan.action_bitmasks.len(),
        2,
        "forced flush should preserve both action transitions in the property-local disk cache",
    );
    assert_ne!(
        forward, backward,
        "disk-backed action-only inline caching must still re-evaluate against the new parent state",
    );
}
