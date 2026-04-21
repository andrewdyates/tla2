// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for #2732: disk-backed liveness graph backend.
//!
//! Validates that the disk-backed behavior graph produces identical liveness
//! checking results to the default in-memory backend.
//!
//! These tests cover both:
//! - end-to-end verdict parity for representative liveness patterns and graph
//!   sizes
//! - a deterministic memory-pressure proxy where the in-memory graph hits a
//!   node budget and the disk-backed graph completes the same spec

mod common;

use tla_check::{resolve_spec_from_config, CheckResult};
use tla_check::{set_liveness_inmemory_node_limit_override, set_use_disk_graph_override, Config};
use tla_core::{lower, parse_to_syntax_tree, FileId};

/// Helper: parse, resolve, and check a liveness spec.
fn check_liveness(
    src: &str,
    property: &str,
    use_disk: bool,
    in_memory_node_limit: Option<usize>,
) -> CheckResult {
    let _skip_guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");
    let _disk_env_guard = common::EnvVarGuard::remove("TLA2_LIVENESS_DISK_GRAPH");
    let _node_limit_env_guard = common::EnvVarGuard::remove("TLA2_LIVENESS_INMEMORY_NODE_LIMIT");
    let _disk_override = set_use_disk_graph_override(use_disk);
    let _node_limit_override = set_liveness_inmemory_node_limit_override(in_memory_node_limit);

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

fn check_liveness_default(src: &str, property: &str, use_disk: bool) -> CheckResult {
    check_liveness(src, property, use_disk, None)
}

// ---------------------------------------------------------------------------
// Test 1: []<>P with WF — cyclic counter (PASS expected)
// ---------------------------------------------------------------------------

const CYCLIC_COUNTER_SPEC: &str = r#"
---- MODULE CyclicCounter ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next ==
    \/ /\ x < 199
       /\ x' = x + 1
    \/ /\ x = 199
       /\ x' = 0

Spec == Init /\ [][Next]_x /\ WF_x(Next)

AlwaysEventuallyZero == []<>(x = 0)
====
"#;

/// In-memory backend: 200-state cyclic counter with WF passes []<>(x = 0).
#[cfg_attr(test, ntest::timeout(60000))]
#[test]
fn liveness_disk_backend_parity_cyclic_counter_inmemory() {
    let result = check_liveness_default(CYCLIC_COUNTER_SPEC, "AlwaysEventuallyZero", false);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 200,
                "cyclic counter should have exactly 200 states"
            );
        }
        other => panic!("in-memory: expected Success, got: {other:?}"),
    }
}

/// Disk backend: same 200-state spec produces identical Success verdict.
#[cfg_attr(test, ntest::timeout(60000))]
#[test]
fn liveness_disk_backend_parity_cyclic_counter_disk() {
    let result = check_liveness_default(CYCLIC_COUNTER_SPEC, "AlwaysEventuallyZero", true);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 200,
                "disk backend: cyclic counter should have exactly 200 states"
            );
        }
        other => panic!("disk backend: expected Success, got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Test 2: []<>P violation — counter that stops (LIVENESS VIOLATION expected)
// ---------------------------------------------------------------------------

const STUCK_COUNTER_SPEC: &str = r#"
---- MODULE StuckCounter ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next ==
    \/ /\ x < 5
       /\ x' = x + 1
    \/ /\ x = 5
       /\ x' = 5

Spec == Init /\ [][Next]_x /\ WF_x(Next)

AlwaysEventuallyZero == []<>(x = 0)
====
"#;

/// In-memory backend: stuck counter violates []<>(x = 0).
#[cfg_attr(test, ntest::timeout(60000))]
#[test]
fn liveness_disk_backend_parity_stuck_violation_inmemory() {
    let result = check_liveness_default(STUCK_COUNTER_SPEC, "AlwaysEventuallyZero", false);
    match &result {
        CheckResult::LivenessViolation { property, .. } => {
            assert!(
                property.contains("AlwaysEventuallyZero"),
                "in-memory: violation should reference AlwaysEventuallyZero, got: {property}"
            );
        }
        other => panic!("in-memory: expected LivenessViolation, got: {other:?}"),
    }
}

/// Disk backend: same stuck counter produces identical LivenessViolation.
#[cfg_attr(test, ntest::timeout(60000))]
#[test]
fn liveness_disk_backend_parity_stuck_violation_disk() {
    let result = check_liveness_default(STUCK_COUNTER_SPEC, "AlwaysEventuallyZero", true);
    match &result {
        CheckResult::LivenessViolation { property, .. } => {
            assert!(
                property.contains("AlwaysEventuallyZero"),
                "disk backend: violation should reference AlwaysEventuallyZero, got: {property}"
            );
        }
        other => panic!("disk backend: expected LivenessViolation, got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Test 3: Larger liveness graph parity with disk backend
// ---------------------------------------------------------------------------

const LARGE_CYCLIC_COUNTER_SPEC: &str = r#"
---- MODULE LargeCyclicCounter ----
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

/// Disk backend handles a 1000-state liveness spec correctly.
///
/// This extends parity coverage beyond the small cases above. It does not
/// demonstrate an OOM-to-success transition: the in-memory baseline below is
/// still expected to pass.
#[cfg_attr(test, ntest::timeout(120000))]
#[test]
fn liveness_disk_backend_large_spec_completes() {
    let result = check_liveness_default(LARGE_CYCLIC_COUNTER_SPEC, "AlwaysEventuallyZero", true);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1000,
                "disk backend: large cyclic counter should have exactly 1000 states"
            );
        }
        other => panic!("disk backend: expected Success for 1000-state spec, got: {other:?}"),
    }
}

/// In-memory baseline for the 1000-state spec (verifies parity).
#[cfg_attr(test, ntest::timeout(120000))]
#[test]
fn liveness_disk_backend_large_spec_inmemory_baseline() {
    let result = check_liveness_default(LARGE_CYCLIC_COUNTER_SPEC, "AlwaysEventuallyZero", false);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1000,
                "in-memory: large cyclic counter should have exactly 1000 states"
            );
        }
        other => panic!("in-memory: expected Success for 1000-state spec, got: {other:?}"),
    }
}

/// Deterministic proxy for the OOM acceptance criterion from #2732.
///
/// The historical in-memory graph is forced to stop after a bounded number of
/// topology nodes, simulating the memory wall that motivated the disk-backed
/// graph. The same spec must still complete when the disk backend is enabled.
#[cfg_attr(test, ntest::timeout(120000))]
#[test]
fn liveness_disk_backend_completes_under_inmemory_node_pressure() {
    const NODE_LIMIT: usize = 256;

    let in_memory = check_liveness(
        LARGE_CYCLIC_COUNTER_SPEC,
        "AlwaysEventuallyZero",
        false,
        Some(NODE_LIMIT),
    );
    match &in_memory {
        CheckResult::Error { error, .. } => {
            let message = error.to_string();
            assert!(
                message.contains("in-memory liveness graph node limit exceeded"),
                "expected in-memory node-limit failure, got: {message}"
            );
            assert!(
                message.contains(&format!("limit={NODE_LIMIT}")),
                "node-limit failure should report the configured limit, got: {message}"
            );
        }
        other => panic!("expected in-memory node-limit failure, got: {other:?}"),
    }

    let disk = check_liveness(
        LARGE_CYCLIC_COUNTER_SPEC,
        "AlwaysEventuallyZero",
        true,
        Some(NODE_LIMIT),
    );
    match &disk {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1000,
                "disk backend should complete the 1000-state spec under the same node budget"
            );
        }
        other => panic!("disk backend should bypass the in-memory node budget, got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Test 4: Two-variable spec with leads-to (P ~> Q)
// ---------------------------------------------------------------------------

const LEADS_TO_SPEC: &str = r#"
---- MODULE LeadsTo ----

VARIABLE phase

Init == phase = "request"

Next ==
    \/ /\ phase = "request"
       /\ phase' = "process"
    \/ /\ phase = "process"
       /\ phase' = "complete"
    \/ /\ phase = "complete"
       /\ phase' = "request"

Spec == Init /\ [][Next]_phase /\ WF_phase(Next)

RequestLeadsToComplete == (phase = "request") ~> (phase = "complete")
====
"#;

/// In-memory: leads-to property with 3-state phase cycle.
#[cfg_attr(test, ntest::timeout(60000))]
#[test]
fn liveness_disk_backend_parity_leads_to_inmemory() {
    let result = check_liveness_default(LEADS_TO_SPEC, "RequestLeadsToComplete", false);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 3, "3-phase cycle should have 3 states");
        }
        other => panic!("in-memory: expected Success for leads-to, got: {other:?}"),
    }
}

/// Disk backend: same leads-to verdict as in-memory.
#[cfg_attr(test, ntest::timeout(60000))]
#[test]
fn liveness_disk_backend_parity_leads_to_disk() {
    let result = check_liveness_default(LEADS_TO_SPEC, "RequestLeadsToComplete", true);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 3,
                "disk backend: 3-phase cycle should have 3 states"
            );
        }
        other => panic!("disk backend: expected Success for leads-to, got: {other:?}"),
    }
}
