// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fingerprint-only liveness replay and depth behavior tests.

use super::*;
use crate::Value;

/// Part of #3175/#3210: When `store_full_states` is false (fingerprint-only
/// mode), liveness checking still works, but the checker no longer mirrors the
/// explored state graph into `seen`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_liveness_works_in_fingerprint_only_mode() {
    let _serial = super::super::acquire_interner_lock();
    let src = r"
---- MODULE ParallelLivenessFpOnly ----
VARIABLE x

Init == x = 0
Next == UNCHANGED x
Prop == <>(x = 99)
====
";
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    // Sanity check: with full states, liveness DOES detect the violation.
    let full_checker = ParallelChecker::new(&module, &config, 2);
    let full_result = full_checker.check();
    assert!(
        matches!(full_result, CheckResult::LivenessViolation { .. }),
        "Sanity: full-state mode should detect liveness violation, got: {full_result:?}"
    );

    // Part of #3175: fp-only mode also detects liveness violations.
    let mut fp_checker = ParallelChecker::new(&module, &config, 2);
    fp_checker.set_store_states(false);
    let fp_result = fp_checker.check();

    match fp_result {
        CheckResult::LivenessViolation { property, .. } => {
            assert_eq!(
                property, "Prop",
                "Expected violation of property 'Prop' in fp-only mode"
            );
            // Part of #3801: fp-only mode with liveness now stores full states
            // in self.seen to ensure the liveness state cache is complete.
            // The state count still comes from seen_fps (the authoritative source).
            assert!(
                !fp_checker.seen.is_empty(),
                "fp-only liveness with cache_for_liveness should store states in seen"
            );
        }
        other => {
            panic!(
                "Expected LivenessViolation in fingerprint-only mode (Part of #3175), got: {other:?}"
            )
        }
    }
}

/// Part of #3210: fp-only parallel liveness must reconstruct a reachable
/// non-init witness state without retaining the explored graph in `seen`.
///
/// The parallel liveness checker may witness the violation either via the
/// concrete `1 <-> 2` cycle or via a stuttering counterexample on one of those
/// non-init states. The key invariant is that the violation witness is not
/// collapsed back to the init state.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_fp_only_liveness_replays_non_init_cycle_without_seen_cache() {
    let _serial = super::super::acquire_interner_lock();
    let src = r"
---- MODULE ParallelFpOnlyNonInitCycle ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next ==
    \/ /\ x = 0
       /\ x' = 1
    \/ /\ x = 1
       /\ x' = 2
    \/ /\ x = 2
       /\ x' = 1

AlwaysReturnZero == []<>(x = 0)
====
";
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["AlwaysReturnZero".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);
    checker.set_store_states(false);

    let result = checker.check();

    match result {
        CheckResult::LivenessViolation {
            property,
            stats,
            cycle,
            ..
        } => {
            assert_eq!(property, "AlwaysReturnZero");
            assert_eq!(
                stats.states_found, 3,
                "fp-only BFS should still explore the full 3-state graph"
            );
            // Part of #3801: fp-only mode with liveness now stores full states
            // in self.seen. The authoritative state count still comes from seen_fps.
            assert_eq!(
                checker.seen.len(),
                3,
                "fp-only liveness with cache_for_liveness should store all 3 states in seen"
            );
            assert_eq!(
                checker.depths.len(),
                3,
                "fp-only liveness should retain depth entries for init and non-init replay states"
            );
            let cycle_x_vals: Vec<Value> = cycle
                .states
                .iter()
                .map(|state| state.get("x").expect("cycle state should have x").clone())
                .collect();
            assert!(
                cycle_x_vals
                    .iter()
                    .any(|value| *value == Value::int(1) || *value == Value::int(2)),
                "fp-only counterexample should reconstruct a non-init witness state: {cycle_x_vals:?}"
            );
        }
        CheckResult::Success(_) => {
            panic!(
                "Expected fp-only liveness violation for []<>(x = 0). \
                 Success means non-init cycle states were lost during replay."
            );
        }
        other => {
            panic!("Expected LivenessViolation for []<>(x = 0) in fp-only mode, got: {other:?}")
        }
    }
}

/// Part of #3801: fp-only parallel liveness with WF fairness constraints must not
/// crash during `populate_node_check_masks`. The formula `WF /\ <>P` decomposes
/// into grouped plans where `~WF` disjuncts have `tf == Bool(true)` and use the
/// FP-direct exploration path. This path relies on `shared_state_cache` containing
/// all behavior graph states. Without the #3801 fix, missing states in the
/// materialized cache cause "missing state for fp" crashes in the eval fallback.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_fp_only_liveness_with_fairness_no_crash() {
    let _serial = super::super::acquire_interner_lock();
    let src = r"
---- MODULE ParallelFpOnlyFairness ----
EXTENDS Naturals

VARIABLE x
vars == <<x>>

Init == x = 0

A == /\ x = 0
     /\ x' = 1

B == /\ x = 1
     /\ x' = 0

Next == A \/ B

Spec == Init /\ [][Next]_vars /\ WF_vars(A) /\ WF_vars(B)

\* With both WF, the system always reaches x=1.
EventuallyOne == <>(x = 1)
====
";
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved = crate::check::resolve_spec_from_config(&spec_config, &tree).unwrap();
    assert!(resolved.stuttering_allowed);
    assert_eq!(
        resolved.fairness.len(),
        2,
        "Should have WF_vars(A) and WF_vars(B)"
    );

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: vec!["EventuallyOne".to_string()],
        ..Default::default()
    };

    let mut full_checker = ParallelChecker::new(&module, &config, 2);
    full_checker.set_fairness(resolved.fairness.clone());
    let full_result = full_checker.check();
    assert!(
        matches!(full_result, CheckResult::Success(_)),
        "Full-state mode should satisfy liveness with WF fairness, got: {full_result:?}"
    );

    let mut fp_checker = ParallelChecker::new(&module, &config, 2);
    fp_checker.set_fairness(resolved.fairness);
    fp_checker.set_store_states(false);
    let fp_result = fp_checker.check();
    match &fp_result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 2,
                "FP-only BFS should find 2 states (x=0, x=1)"
            );
        }
        CheckResult::Error { error, .. } => {
            panic!("FP-only liveness with WF fairness should not crash (Part of #3801): {error:?}");
        }
        other => {
            panic!("FP-only liveness with WF fairness should succeed, got: {other:?}");
        }
    }
}

/// Part of #3233: fp-only liveness without checkpointing still populates `depths`.
/// The `track_depths` gate is `checkpoint_enabled || successors.is_some()`, so when
/// liveness properties are declared, `successors` is `Some(_)` and `track_depths`
/// becomes true. This test proves the liveness side of the depth gate stays intact
/// after the safety-only no-depths optimization.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_fp_only_liveness_depths_populated() {
    let _serial = super::super::acquire_interner_lock();
    let src = r"
---- MODULE ParallelLivenessDepths ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next ==
    \/ /\ x = 0
       /\ x' = 1
    \/ /\ x = 1
       /\ x' = 2
    \/ /\ x = 2
       /\ x' = 1
AlwaysReturnZero == []<>(x = 0)
====
";
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["AlwaysReturnZero".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);
    checker.set_store_states(false);
    // No checkpoint_dir — liveness alone drives track_depths.

    let result = checker.check();
    match &result {
        CheckResult::LivenessViolation {
            property, stats, ..
        } => {
            assert_eq!(property, "AlwaysReturnZero");
            assert_eq!(stats.states_found, 3, "should explore 3 states");
        }
        other => panic!("Expected LivenessViolation, got: {other:?}"),
    }

    // The key assertion: depths is populated because liveness replay needs it,
    // even though checkpointing is off.
    assert_eq!(
        checker.depths.len(),
        3,
        "fp-only liveness must populate depths for all 3 states (track_depths = true via successors)"
    );
}
