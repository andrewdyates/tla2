// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Part of #3175: explicit `set_store_states(false)` preserves fp-only liveness.
///
/// The default constructor path now enables fp-only liveness automatically.
/// This test keeps coverage for callers that explicitly set fingerprint-only
/// mode after construction: the setter must not disable the liveness cache.
///
/// For a single-state spec where the only state is an init state, the liveness
/// checker has complete data (init_states cache has the full state, successors
/// map has the self-loop). The violation should be detected.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_liveness_violation_detected_in_fp_only_mode_via_set_store_states() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE FpOnlyLivenessViolation ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next == UNCHANGED x

EventuallyOne == <>(x = 1)
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["EventuallyOne".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    // Explicitly keep fingerprint-only mode. This should preserve the same
    // cache_for_liveness default established during construction.
    checker.set_store_states(false);

    let result = checker.check();

    match result {
        CheckResult::LivenessViolation { property, .. } => {
            assert_eq!(
                property, "EventuallyOne",
                "Expected violation of property 'EventuallyOne'"
            );
        }
        CheckResult::Success(_) => {
            panic!(
                "Expected LivenessViolation in fp-only mode with cache_for_liveness=true. \
                 Got Success — liveness was incorrectly skipped despite cache_for_liveness."
            );
        }
        other => panic!(
            "Expected LivenessViolation for <>(x = 1) with UNCHANGED x in fp-only mode, \
             got: {other:?}"
        ),
    }
}

/// Part of #3210: sequential fp-only liveness must not repopulate the full-state
/// `seen` map just to report a liveness counterexample.
///
/// The checker should still record every explored fingerprint for BFS dedup, but
/// concrete states are reconstructed later on the cold replay path.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_fp_only_liveness_keeps_seen_map_empty() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let tree = parse_to_syntax_tree(FP_ONLY_NON_INIT_CYCLE_SPEC);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["AlwaysReturnZero".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(false);

    let result = checker.check();

    assert!(
        checker.test_seen_is_empty(),
        "fp-only liveness should not retain explored states in the full-state seen map"
    );
    assert_eq!(
        checker.test_seen_fps_len(),
        3,
        "fp-only BFS should still deduplicate all 3 reachable states by fingerprint"
    );

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
            assert!(
                trace_x_values(&cycle)
                    .iter()
                    .any(|value| *value == Value::int(1) || *value == Value::int(2)),
                "fp-only counterexample should still replay a non-init violating cycle"
            );
        }
        CheckResult::Success(_) => {
            panic!(
                "Expected fp-only liveness violation for []<>(x = 0). \
                 Success means the replay path lost the non-init cycle."
            );
        }
        other => {
            panic!("Expected LivenessViolation for []<>(x = 0) in fp-only mode, got: {other:?}")
        }
    }
}

/// Part of #3205: fp-only liveness must retain non-init states in `state_cache`.
///
/// The behavior graph here has three states:
/// - init `x = 0`
/// - reachable cycle `x = 1 <-> x = 2`
///
/// `[]<>(x = 0)` is violated because once the checker leaves the init state it
/// can loop forever in `{1, 2}` without revisiting `0`.
///
/// Before #3205, fp-only liveness built `state_cache` from `init_states` only.
/// That silently dropped `x = 1` and `x = 2` from successor reconstruction,
/// collapsing the graph to an init self-loop and producing a false negative.
///
/// Part of #3210: this should now still pass without retaining every explored
/// state during BFS, and the returned counterexample must no longer collapse to
/// the init-state self-loop.
///
/// Because stuttering is legal, the violating suffix may be witnessed by a
/// one-state stuttering cycle at `x = 1` or `x = 2`; the counterexample does
/// not need to enumerate the whole `{1, 2}` SCC.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_fp_only_liveness_keeps_non_init_cycle_states() {
    let result =
        run_explicit_fp_only_property_check(FP_ONLY_NON_INIT_CYCLE_SPEC, "AlwaysReturnZero");

    match result {
        CheckResult::LivenessViolation {
            property,
            stats,
            prefix,
            cycle,
            ..
        } => {
            assert_eq!(property, "AlwaysReturnZero");
            assert_eq!(
                stats.states_found, 3,
                "fp-only BFS should still explore the full 3-state graph"
            );
            let prefix_x_vals = trace_x_values(&prefix);
            let cycle_x_vals = trace_x_values(&cycle);
            assert!(
                cycle_x_vals.iter().all(|value| *value != Value::int(0)),
                "fp-only counterexample cycle should stay off the init state: {cycle_x_vals:?}"
            );
            assert!(
                prefix_x_vals.contains(&Value::int(1))
                    || cycle_x_vals.contains(&Value::int(1))
                    || cycle_x_vals.contains(&Value::int(2)),
                "fp-only counterexample should reach a non-init violating suffix, got prefix={prefix_x_vals:?} cycle={cycle_x_vals:?}"
            );
        }
        CheckResult::Success(_) => {
            panic!(
                "Expected fp-only liveness violation for []<>(x = 0). \
                 Success means non-init cycle states were lost during successor reconstruction."
            );
        }
        other => {
            panic!("Expected LivenessViolation for []<>(x = 0) in fp-only mode, got: {other:?}")
        }
    }
}

/// Part of #3175: fp-only liveness with VIEW fingerprinting.
///
/// When VIEW is configured, `state_fingerprint()` returns a VIEW-based hash
/// while `state.fingerprint()` returns the raw state hash. The counterexample
/// reconstruction's self-loop check must use the canonical (VIEW-aware)
/// fingerprint, not the raw one. Before this fix, the self-loop optimization
/// in `reconstruct_liveness_counterexample_from_fingerprints` compared
/// `target_fp` (canonical/VIEW) with `current_state.fingerprint()` (raw),
/// causing a mismatch and RuntimeFailure for VIEW specs with stuttering cycles.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_fp_only_liveness_with_view_fingerprinting() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Spec with a VIEW that projects away variable `y`. The behavior graph
    // has two concrete states (x=0,y=0) and (x=0,y=1) but they map to the
    // same VIEW fingerprint. Liveness property <>(x = 1) is violated because
    // x stays 0 forever. The counterexample cycle will include stuttering
    // (same VIEW fingerprint) which exercises the self-loop check path.
    let src = r#"
---- MODULE ViewFpOnlyLiveness ----
EXTENDS Integers

VARIABLES x, y

Init == x = 0 /\ y = 0

Next == /\ x' = x
        /\ y' = 1 - y

view == <<x>>

EventuallyOne == <>(x = 1)
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["EventuallyOne".to_string()],
        view: Some("view".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    // Stay in fp-only mode (default). VIEW + liveness + fp-only exercises
    // the canonical fingerprint comparison in counterexample reconstruction.

    let result = checker.check();

    match result {
        CheckResult::LivenessViolation {
            property, cycle, ..
        } => {
            assert_eq!(property, "EventuallyOne");
            assert!(
                !cycle.is_empty(),
                "VIEW fp-only liveness should produce a non-empty counterexample cycle"
            );
            // All cycle states should have x=0 (the violation: x never reaches 1)
            let x_vals = trace_x_values(&cycle);
            assert!(
                x_vals.iter().all(|v| *v == Value::int(0)),
                "counterexample cycle should show x stuck at 0, got: {x_vals:?}"
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "VIEW fp-only liveness should not produce an error. \
                 This likely means the canonical fingerprint comparison in \
                 counterexample reconstruction is using raw state.fingerprint() \
                 instead of self.state_fingerprint(). Error: {error}"
            );
        }
        CheckResult::Success(_) => {
            panic!(
                "Expected LivenessViolation for <>(x = 1) with VIEW. \
                 Got Success — liveness checking may have been skipped."
            );
        }
        other => panic!("Expected LivenessViolation for VIEW fp-only liveness, got: {other:?}"),
    }
}
