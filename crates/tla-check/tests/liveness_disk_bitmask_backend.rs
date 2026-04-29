// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for #3177: disk-backed bitmask maps for liveness inline recording.
//!
//! These tests validate that the disk-backed bitmask maps (state and action)
//! preserve liveness results when the hot tier is periodically flushed to
//! disk-backed cold storage during BFS.

mod common;

use tla_check::{resolve_spec_from_config, CheckResult};
use tla_check::{
    set_liveness_disk_bitmask_flush_threshold_override, set_use_disk_bitmasks_override, Config,
};
use tla_core::{lower, parse_to_syntax_tree, FileId};

fn check_liveness(src: &str, property: &str, use_disk_bitmasks: bool) -> CheckResult {
    let _skip_guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");
    let _disk_graph_guard = common::EnvVarGuard::remove("TLA2_LIVENESS_DISK_GRAPH");
    let _disk_successor_guard = common::EnvVarGuard::remove("TLA2_LIVENESS_DISK_SUCCESSORS");
    let _disk_bitmask_env_guard = common::EnvVarGuard::remove("TLA2_LIVENESS_DISK_BITMASKS");
    let _disk_bitmask_flush_threshold_guard =
        common::EnvVarGuard::remove("TLA2_LIVENESS_DISK_BITMASK_FLUSH_THRESHOLD");
    let _disk_bitmask_override = set_use_disk_bitmasks_override(use_disk_bitmasks);
    let _disk_bitmask_flush_threshold_override =
        set_liveness_disk_bitmask_flush_threshold_override(Some(32));

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("module lowering should succeed");

    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved =
        resolve_spec_from_config(&spec_config, &tree).expect("spec resolution should succeed");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: vec![property.to_string()],
        ..Default::default()
    };

    let mut checker = tla_check::ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);
    checker.set_fairness(resolved.fairness);
    checker.set_stuttering_allowed(resolved.stuttering_allowed);
    checker.check()
}

/// Cyclic counter with WF liveness: []<>(x = 0). 1000 states, 1000 transitions.
/// Exercises both state and action bitmask maps.
const CYCLIC_COUNTER_SPEC: &str = r#"
---- MODULE CyclicCounterBitmask ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next ==
    \/ /\ x < 999
       /\ x' = x + 1
    \/ /\ x = 999
       /\ x' = 0

Spec == Init /\ [][Next]_x /\ WF_x(Next)

AlwaysEventuallyZero == []<>(x = 0)
====
"#;

/// Parity test: disk bitmask backend produces the same liveness result
/// as the in-memory backend on a 1000-state cyclic spec. The forced low flush
/// threshold makes the BFS path exercise repeated `maybe_flush()` calls.
#[cfg_attr(test, ntest::timeout(120000))]
#[test]
fn liveness_disk_bitmask_backend_parity() {
    let in_memory = check_liveness(CYCLIC_COUNTER_SPEC, "AlwaysEventuallyZero", false);
    match &in_memory {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1000,
                "in-memory bitmask should preserve the 1000-state liveness result"
            );
        }
        other => panic!("expected in-memory bitmask success, got: {other:?}"),
    }

    let disk = check_liveness(CYCLIC_COUNTER_SPEC, "AlwaysEventuallyZero", true);
    match &disk {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1000,
                "disk bitmask backend should preserve the 1000-state liveness result"
            );
        }
        other => panic!("expected disk bitmask backend success, got: {other:?}"),
    }
}

/// Two-action spec exercising action bitmask maps with separate fairness
/// constraints. Both WF_x(Inc) and WF_x(Reset) produce action-level
/// bitmask entries during BFS.
const TWO_ACTION_SPEC: &str = r#"
---- MODULE TwoActionBitmask ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Inc == x < 49 /\ x' = x + 1
Reset == x = 49 /\ x' = 0

Next == Inc \/ Reset

Spec == Init /\ [][Next]_x /\ WF_x(Inc) /\ WF_x(Reset)

EventuallyResets == []<>(x = 0)
====
"#;

/// Parity test with separate fairness constraints (WF per action).
/// This exercises the action bitmask path where different action tags
/// produce different bitmask bits per transition, with a low flush threshold
/// forcing hot->cold merges during BFS.
#[cfg_attr(test, ntest::timeout(120000))]
#[test]
fn liveness_disk_bitmask_two_action_parity() {
    let in_memory = check_liveness(TWO_ACTION_SPEC, "EventuallyResets", false);
    match &in_memory {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 50,
                "in-memory bitmask should find 50 states"
            );
        }
        other => panic!("expected in-memory bitmask success, got: {other:?}"),
    }

    let disk = check_liveness(TWO_ACTION_SPEC, "EventuallyResets", true);
    match &disk {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 50,
                "disk bitmask backend should find 50 states"
            );
        }
        other => panic!("expected disk bitmask backend success, got: {other:?}"),
    }
}
