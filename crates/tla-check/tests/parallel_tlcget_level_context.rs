// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod common;

use tla_check::{
    set_use_handle_state_override, CheckResult, Config, ModelChecker, ParallelChecker,
};

/// Regression for #1102: parallel exploration must use:
/// 1. `curState.level` for ACTION_CONSTRAINT evaluation
/// 2. `succState.level` for successor invariant evaluation
///
/// This test forces the state-based fallback path by configuring VIEW and ACTION_CONSTRAINT.
/// It also exercises both default and HandleState parallel workers.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_tlcget_level_context_for_action_constraints_and_invariants() {
    let spec = r#"
---- MODULE ParallelTLCGetLevelContext ----
EXTENDS TLC, Naturals

VARIABLE x

Init == x = 1
Next == /\ x < 3 /\ x' = x + 1

\* ACTION_CONSTRAINT is evaluated in current-state context.
CurLevelOk == TLCGet("level") = x

\* Invariant is evaluated in successor-state context.
SuccLevelOk == TLCGet("level") = x

\* Force VIEW fingerprinting path and include level in the abstraction.
LevelView == <<x, TLCGet("level")>>

====
"#;

    let module = common::parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["SuccLevelOk".to_string()],
        action_constraints: vec!["CurLevelOk".to_string()],
        view: Some("LevelView".to_string()),
        check_deadlock: false,
        ..Default::default()
    };

    for use_handle_state in [false, true] {
        let _guard = set_use_handle_state_override(use_handle_state);

        for store_states in [false, true] {
            let mut checker = ParallelChecker::new(&module, &config, 2);
            checker.set_store_states(store_states);
            let result = checker.check();

            match result {
                CheckResult::Success(stats) => {
                    assert_eq!(
                        stats.states_found, 3,
                        "parallel TLCGet level context mismatch (handle_state={}, store_states={})",
                        use_handle_state, store_states
                    );
                }
                other => panic!(
                    "Expected Success for handle_state={} store_states={}, got {:?}",
                    use_handle_state, store_states, other
                ),
            }
        }
    }
}

/// Regression for #1281: parallel checker off-by-one state count when VIEW includes
/// TLCGet("level") and ACTION_CONSTRAINT uses TLCGet("level").
///
/// Before the fix, compute_view_fingerprint did not save/restore TLCGet("level"),
/// so after computing the successor's VIEW fingerprint (with succ_level), the
/// ACTION_CONSTRAINT evaluation would see succ_level instead of current_level,
/// causing it to check the wrong log entry and incorrectly reject transitions.
///
/// This test uses multiple initial states and enough BFS depth to trigger the
/// level-dependent filtering, then compares sequential vs parallel state counts.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_view_level_action_constraint_state_count_parity() {
    let spec = r#"
---- MODULE ParallelViewLevelParity ----
EXTENDS TLC, Naturals

VARIABLES x, y

Init == x \in {1, 2, 3} /\ y = 0

Next == /\ x' \in {1, 2, 3}
        /\ y' = y + 1

\* ACTION_CONSTRAINT limits depth, evaluated in current-state context.
DepthBound == TLCGet("level") <= 4

\* VIEW includes level to make states at different depths distinct.
LevelView == <<x, y, TLCGet("level")>>

====
"#;

    let module = common::parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        action_constraints: vec!["DepthBound".to_string()],
        view: Some("LevelView".to_string()),
        check_deadlock: false,
        ..Default::default()
    };

    // Get sequential state count
    let mut seq_checker = ModelChecker::new(&module, &config);
    let seq_result = seq_checker.check();
    let seq_states = match &seq_result {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Sequential check failed: {:?}", other),
    };
    assert!(seq_states > 0, "Sequential check found 0 states");

    // Get parallel state counts for various worker counts
    for workers in [2, 4] {
        for use_handle_state in [false, true] {
            let _guard = set_use_handle_state_override(use_handle_state);

            let par_checker = ParallelChecker::new(&module, &config, workers);
            let par_result = par_checker.check();

            match par_result {
                CheckResult::Success(stats) => {
                    assert_eq!(
                        stats.states_found,
                        seq_states,
                        "Parallel (workers={}, handle_state={}) found {} states, \
                         sequential found {} — off-by-{} regression (#1281)",
                        workers,
                        use_handle_state,
                        stats.states_found,
                        seq_states,
                        (seq_states as isize - stats.states_found as isize).unsigned_abs()
                    );
                }
                other => panic!(
                    "Parallel check (workers={}, handle_state={}) failed: {:?}",
                    workers, use_handle_state, other
                ),
            }
        }
    }
}
