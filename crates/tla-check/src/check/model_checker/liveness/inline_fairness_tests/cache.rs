// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for inline fairness cache preparation, activation, and recording.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn prepare_inline_fairness_cache_collects_wf_leaves() {
    let module = parse_module(INLINE_FAIRNESS_SPEC);
    let config = inline_fairness_config();

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    apply_weak_fairness(&mut checker);

    checker.prepare_inline_fairness_cache();

    assert_eq!(
        checker.liveness_cache.fairness_state_checks.len(),
        1,
        "WF should contribute one ENABLED state leaf"
    );
    assert_eq!(
        checker.liveness_cache.fairness_action_checks.len(),
        2,
        "WF should contribute action predicate + state-changed leaves"
    );
    assert!(checker.inline_fairness_active());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn inline_fairness_active_turns_off_when_view_mode_is_refreshed() {
    let module = parse_module(INLINE_FAIRNESS_SPEC);
    let config = inline_fairness_config();

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    apply_weak_fairness(&mut checker);
    checker.prepare_inline_fairness_cache();
    assert!(checker.inline_fairness_active());

    checker.compiled.cached_view_name = Some("View".to_string());
    checker.refresh_liveness_mode();
    checker.prepare_inline_fairness_cache();

    assert!(
        !checker.inline_fairness_active(),
        "VIEW mode should disable inline fairness via the cached liveness mode"
    );
    assert!(
        checker.liveness_cache.fairness_state_checks.is_empty(),
        "prepare_inline_fairness_cache should stop before rebuilding leaves when VIEW is active"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn record_inline_fairness_results_records_successor_and_stuttering_edges() {
    let module = parse_module(INLINE_FAIRNESS_SPEC);
    let config = inline_fairness_config();

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    apply_weak_fairness(&mut checker);
    checker.prepare_inline_fairness_cache();

    let registry = checker.ctx.var_registry().clone();
    let current = State::from_pairs([("x", Value::int(0))]);
    let next = State::from_pairs([("x", Value::int(1))]);
    let current_arr = ArrayState::from_state(&current, &registry);
    let next_arr = ArrayState::from_state(&next, &registry);
    let current_fp = current.fingerprint();
    let next_fp = next.fingerprint();

    checker
        .record_inline_fairness_results(current_fp, &current_arr, &[(next_arr, next_fp)])
        .expect("inline fairness recording should succeed");

    assert_recorded_transition_results(&checker, current_fp, next_fp);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn record_inline_fairness_results_uses_graph_fingerprints() {
    let module = parse_module(INLINE_FAIRNESS_SPEC);
    let config = inline_fairness_config();
    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    apply_weak_fairness(&mut checker);
    checker.prepare_inline_fairness_cache();

    let registry = checker.ctx.var_registry().clone();
    let current = State::from_pairs([("x", Value::int(0))]);
    let next = State::from_pairs([("x", Value::int(1))]);
    let current_arr = ArrayState::from_state(&current, &registry);
    let next_arr = ArrayState::from_state(&next, &registry);
    let graph_current_fp = Fingerprint(current.fingerprint().0.wrapping_add(11));
    let graph_next_fp = Fingerprint(next.fingerprint().0.wrapping_add(29));

    checker
        .record_inline_fairness_results(
            graph_current_fp,
            &current_arr,
            &[(next_arr, graph_next_fp)],
        )
        .expect("inline fairness recording should use BFS graph fingerprints");

    assert_recorded_transition_results(&checker, graph_current_fp, graph_next_fp);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn full_state_check_uses_inline_fairness_cache_without_regression() {
    let module = parse_module(INLINE_FAIRNESS_SPEC);
    let config = inline_fairness_config();

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    apply_weak_fairness(&mut checker);

    let result = checker.check();
    match &result {
        CheckResult::Success(stats) => {
            assert!(
                stats.states_found > 0,
                "inline fairness spec should explore at least one state"
            );
        }
        other => panic!("simple WF-backed liveness spec should still succeed, got {other:?}"),
    }
    assert!(
        !checker.liveness_cache.inline_state_bitmasks.is_empty(),
        "full-state BFS should populate inline fairness state bitmasks"
    );
    assert!(
        !checker.liveness_cache.inline_action_bitmasks.is_empty(),
        "full-state BFS should populate inline fairness action bitmasks"
    );
}
