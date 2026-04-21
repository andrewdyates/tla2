// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use tla_core::{lower, parse_to_syntax_tree, FileId};

const DISJOINT_COUNTERS_SPEC: &str = r#"
---- MODULE PorDisjointCounters ----
EXTENDS Naturals

VARIABLE x, y

Init == x = 0 /\ y = 0

IncX ==
    /\ x < 2
    /\ x' = x + 1
    /\ UNCHANGED y

IncY ==
    /\ y < 2
    /\ y' = y + 1
    /\ UNCHANGED x

Next == IncX \/ IncY
====
"#;

const DISJOINT_COUNTERS_WITH_INV_SPEC: &str = r#"
---- MODULE PorDisjointCountersInv ----
EXTENDS Naturals

VARIABLE x, y

Init == x = 0 /\ y = 0

IncX ==
    /\ x < 2
    /\ x' = x + 1
    /\ UNCHANGED y

IncY ==
    /\ y < 2
    /\ y' = y + 1
    /\ UNCHANGED x

Next == IncX \/ IncY
Inv == x + y < 4
====
"#;

const DEPENDENT_ACTIONS_SPEC: &str = r#"
---- MODULE PorDependentActions ----
EXTENDS Naturals

VARIABLE x, y

Init == x = 0 /\ y = 0

ActionA ==
    /\ x < 2
    /\ x' = x + 1
    /\ UNCHANGED y

ActionB ==
    /\ x < 2
    /\ x' = x * 2
    /\ UNCHANGED y

Next == ActionA \/ ActionB
====
"#;

const THREE_DISJOINT_COUNTERS_SPEC: &str = r#"
---- MODULE PorThreeDisjointCounters ----
EXTENDS Naturals

VARIABLE x, y, z

Init == x = 0 /\ y = 0 /\ z = 0

IncX ==
    /\ x < 2
    /\ x' = x + 1
    /\ UNCHANGED <<y, z>>

IncY ==
    /\ y < 2
    /\ y' = y + 1
    /\ UNCHANGED <<x, z>>

IncZ ==
    /\ z < 2
    /\ z' = z + 1
    /\ UNCHANGED <<x, y>>

Next == IncX \/ IncY \/ IncZ
====
"#;

const SIMPLE_POR_STATS_SPEC: &str = r#"
---- MODULE PorStatsSimple ----
EXTENDS Naturals

VARIABLE x, y

Init == x = 0 /\ y = 0

IncX ==
    /\ x < 1
    /\ x' = x + 1
    /\ UNCHANGED y

IncY ==
    /\ y < 1
    /\ y' = y + 1
    /\ UNCHANGED x

Next == IncX \/ IncY
====
"#;

fn make_config(por_enabled: bool, invariants: &[&str]) -> Config {
    Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: invariants.iter().map(|name| (*name).to_string()).collect(),
        por_enabled,
        check_deadlock: false,
        ..Default::default()
    }
}

/// Config with auto-POR explicitly disabled. Use this when you need a "truly no POR"
/// baseline (e.g., for comparing state counts with and without reduction).
fn make_config_no_por(invariants: &[&str]) -> Config {
    Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: invariants.iter().map(|name| (*name).to_string()).collect(),
        por_enabled: false,
        auto_por: Some(false),
        check_deadlock: false,
        ..Default::default()
    }
}

fn run_check(src: &str, config: Config) -> CheckResult {
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.unwrap();

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.check()
}

fn expect_success(result: CheckResult) -> CheckStats {
    match result {
        CheckResult::Success(stats) => stats,
        other => panic!("Expected success, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_por_disjoint_counters_reduces_state_space() {
    let without_por = expect_success(run_check(DISJOINT_COUNTERS_SPEC, make_config_no_por(&[])));
    assert_eq!(without_por.states_found, 9);
    assert_eq!(without_por.transitions, 12);

    let with_por = expect_success(run_check(DISJOINT_COUNTERS_SPEC, make_config(true, &[])));
    assert_eq!(with_por.states_found, 5);
    assert!(with_por.states_found < without_por.states_found);
    assert!(with_por.transitions < without_por.transitions);
    assert_eq!(with_por.por_reduction.action_count, 2);
    assert_eq!(with_por.por_reduction.independent_pairs, 1);
    assert_eq!(with_por.por_reduction.total_pairs, 1);
    assert!(with_por.por_reduction.states_reduced > 0);
    assert!(with_por.por_reduction.actions_skipped > 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_por_preserves_invariant_detection() {
    let result = run_check(
        DISJOINT_COUNTERS_WITH_INV_SPEC,
        make_config(true, &["Inv"]),
    );

    match result {
        CheckResult::InvariantViolation { invariant, .. } => {
            assert_eq!(invariant, "Inv");
        }
        other => panic!("Expected invariant violation, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_por_dependent_actions_no_reduction() {
    let stats = expect_success(run_check(DEPENDENT_ACTIONS_SPEC, make_config(true, &[])));

    assert_eq!(stats.por_reduction.action_count, 2);
    assert_eq!(stats.por_reduction.total_pairs, 1);
    assert_eq!(stats.por_reduction.independent_pairs, 0);
    assert!(stats.por_reduction.states_processed > 0);
    assert_eq!(stats.por_reduction.states_reduced, 0);
    assert_eq!(stats.por_reduction.actions_skipped, 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_por_three_disjoint_counters() {
    let without_por = expect_success(run_check(
        THREE_DISJOINT_COUNTERS_SPEC,
        make_config_no_por(&[]),
    ));
    assert_eq!(without_por.states_found, 27);

    let stats = expect_success(run_check(
        THREE_DISJOINT_COUNTERS_SPEC,
        make_config(true, &[]),
    ));

    assert_eq!(stats.states_found, 7);
    assert!(stats.states_found < without_por.states_found);
    assert_eq!(stats.por_reduction.action_count, 3);
    assert_eq!(stats.por_reduction.total_pairs, 3);
    assert_eq!(stats.por_reduction.independent_pairs, 3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_por_statistics_populated() {
    let stats = expect_success(run_check(SIMPLE_POR_STATS_SPEC, make_config(true, &[])));
    let por = &stats.por_reduction;

    assert_eq!(por.action_count, 2);
    assert_eq!(por.total_pairs, 1);
    assert_eq!(por.independent_pairs, 1);
    assert!(por.states_processed > 0);
    assert!(por.states_reduced > 0);
    assert!(por.actions_skipped > 0);
    assert!(por.states_processed >= por.states_reduced);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_por_disabled_no_statistics() {
    let stats = expect_success(run_check(SIMPLE_POR_STATS_SPEC, make_config_no_por(&[])));
    let por = &stats.por_reduction;

    assert_eq!(por.action_count, 0);
    assert_eq!(por.total_pairs, 0);
    assert_eq!(por.independent_pairs, 0);
    assert_eq!(por.states_processed, 0);
    assert_eq!(por.states_reduced, 0);
    assert_eq!(por.actions_skipped, 0);
}

/// POR must be disabled when liveness properties are present.
/// The C3 BFS proviso is insufficient for liveness checking — liveness
/// requires the "ignoring proviso" (Peled 1996) or "strong proviso".
/// When POR is requested but liveness is present, the checker must fall
/// back to full exploration (no reduction, no POR stats).
const LIVENESS_SPEC: &str = r#"
---- MODULE PorLiveness ----
EXTENDS Naturals

VARIABLE x, y

Init == x = 0 /\ y = 0

IncX ==
    /\ x < 2
    /\ x' = x + 1
    /\ UNCHANGED y

IncY ==
    /\ y < 2
    /\ y' = y + 1
    /\ UNCHANGED x

Next == IncX \/ IncY
LiveProp == <>(x + y >= 0)
====
"#;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_por_disabled_with_liveness_properties() {
    let mut config = make_config(true, &[]);
    config.properties = vec!["LiveProp".to_string()];

    let stats = expect_success(run_check(LIVENESS_SPEC, config));
    let por = &stats.por_reduction;

    // POR should be fully disabled — no independence analysis, no reduction
    assert_eq!(por.action_count, 0);
    assert_eq!(por.independent_pairs, 0);
    assert_eq!(por.states_reduced, 0);
    assert_eq!(por.actions_skipped, 0);
    // Full state space should be explored (same as without POR)
    assert_eq!(stats.states_found, 9);
}

/// Identity assignment detection: `x' = x` should be treated as UNCHANGED x,
/// enabling independence when two actions only touch disjoint variables via
/// explicit identity writes rather than UNCHANGED keyword.
const IDENTITY_ASSIGNMENT_SPEC: &str = r#"
---- MODULE PorIdentityAssignment ----
EXTENDS Naturals

VARIABLE x, y

Init == x = 0 /\ y = 0

IncX ==
    /\ x < 2
    /\ x' = x + 1
    /\ y' = y

IncY ==
    /\ y < 2
    /\ y' = y + 1
    /\ x' = x

Next == IncX \/ IncY
====
"#;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_por_identity_assignment_enables_independence() {
    // `x' = x` is semantically identical to `UNCHANGED x` — POR should
    // detect this and treat the actions as independent.
    let stats = expect_success(run_check(IDENTITY_ASSIGNMENT_SPEC, make_config(true, &[])));
    let por = &stats.por_reduction;

    assert_eq!(por.action_count, 2);
    assert_eq!(por.total_pairs, 1);
    // The identity assignment detector recognizes `x' = x` → UNCHANGED x,
    // so the two actions should be independent.
    assert_eq!(por.independent_pairs, 1);
    // With independence, POR should reduce the state space
    assert!(por.states_reduced > 0);
    assert_eq!(stats.states_found, 5);
}

/// Visibility condition: when an invariant references a variable, any action
/// that writes to that variable is "visible" and must be included in the
/// ample set. This test verifies that POR correctly detects invariant
/// violations even when the violating action would otherwise be reduced.
const VISIBILITY_SPEC: &str = r#"
---- MODULE PorVisibility ----
EXTENDS Naturals

VARIABLE x, y

Init == x = 0 /\ y = 0

IncX ==
    /\ x < 3
    /\ x' = x + 1
    /\ UNCHANGED y

IncY ==
    /\ y < 3
    /\ y' = y + 1
    /\ UNCHANGED x

Next == IncX \/ IncY
XBound == x <= 2
====
"#;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_por_visibility_preserves_invariant_checking() {
    // XBound references x, so IncX is visible. POR must not skip IncX
    // when it would violate the invariant.
    let result = run_check(VISIBILITY_SPEC, make_config(true, &["XBound"]));

    match result {
        CheckResult::InvariantViolation { invariant, .. } => {
            assert_eq!(invariant, "XBound");
        }
        other => panic!("Expected invariant violation of XBound, got: {:?}", other),
    }
}

/// Safety net: POR must never change the set of reachable states for specs
/// where all actions are dependent (no reduction possible). The state count
/// with and without POR must be identical.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_por_same_state_count_as_without_por_when_dependent() {
    let without = expect_success(run_check(DEPENDENT_ACTIONS_SPEC, make_config_no_por(&[])));
    let with = expect_success(run_check(DEPENDENT_ACTIONS_SPEC, make_config(true, &[])));

    // When actions are dependent, POR cannot reduce — state counts must match exactly
    assert_eq!(with.states_found, without.states_found);
    assert_eq!(with.transitions, without.transitions);
}

// ==================== Auto-POR Tests ====================
//
// Part of #3993: Auto-POR enables partial order reduction automatically when
// the independence analysis detects independent action pairs. Users no longer
// need to pass --por explicitly.
//
// NOTE: Auto-POR is controlled by a OnceLock-cached env var (TLA2_AUTO_POR).
// The OnceLock reads the value once per process; env var tests that toggle it
// within a process are not feasible. Tests below rely on auto-POR being enabled
// by default (TLA2_AUTO_POR unset = true).

/// Auto-POR: disjoint counters spec gets reduced without --por.
///
/// This is the key auto-POR test: the spec has independent actions (IncX and
/// IncY touch disjoint variables), so auto-POR should detect this and enable
/// reduction automatically. The reduced state count should match explicit --por.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_auto_por_reduces_disjoint_counters() {
    // Auto-POR (default: por_enabled=false but auto-POR is on)
    let auto_por = expect_success(run_check(DISJOINT_COUNTERS_SPEC, make_config(false, &[])));

    // Explicit --por
    let explicit_por = expect_success(run_check(DISJOINT_COUNTERS_SPEC, make_config(true, &[])));

    // Auto-POR should reduce to same state count as explicit --por
    assert_eq!(auto_por.states_found, explicit_por.states_found);
    assert_eq!(auto_por.states_found, 5);

    // Auto-POR stats should indicate auto-detection
    assert!(
        auto_por.por_reduction.auto_detected,
        "auto-POR should set auto_detected=true"
    );
    assert!(
        !explicit_por.por_reduction.auto_detected,
        "explicit --por should set auto_detected=false"
    );
    assert!(auto_por.por_reduction.independent_pairs > 0);
}

/// Auto-POR: dependent actions spec should NOT get POR overhead.
///
/// When all actions are dependent (no independent pairs), auto-POR should
/// not enable POR and the per-action enumeration path should be avoided.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_auto_por_skips_dependent_actions() {
    let stats = expect_success(run_check(DEPENDENT_ACTIONS_SPEC, make_config(false, &[])));

    // Auto-POR should detect no independent pairs and skip POR.
    // por_reduction should be empty (no POR active).
    assert_eq!(stats.por_reduction.action_count, 0);
    assert_eq!(stats.por_reduction.independent_pairs, 0);
    assert_eq!(stats.por_reduction.states_reduced, 0);
}

/// Auto-POR: three disjoint counters get full reduction.
///
/// With 3 mutually independent actions, auto-POR should achieve the same
/// reduction as explicit --por (3x state space reduction).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_auto_por_three_disjoint_counters() {
    let stats = expect_success(run_check(
        THREE_DISJOINT_COUNTERS_SPEC,
        make_config(false, &[]),
    ));

    // Auto-POR should reduce to 7 states (same as explicit --por)
    assert_eq!(stats.states_found, 7);
    assert_eq!(stats.por_reduction.action_count, 3);
    assert_eq!(stats.por_reduction.independent_pairs, 3);
    assert!(stats.por_reduction.auto_detected);
}

/// Auto-POR preserves invariant violations.
///
/// Auto-POR must not suppress invariant detection. When IncX and IncY
/// are independent but the invariant x + y < 4 is violated by reaching
/// state (x=2, y=2), POR must still detect this.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_auto_por_preserves_invariant_detection() {
    let result = run_check(
        DISJOINT_COUNTERS_WITH_INV_SPEC,
        make_config(false, &["Inv"]),
    );

    match result {
        CheckResult::InvariantViolation { invariant, .. } => {
            assert_eq!(invariant, "Inv");
        }
        other => panic!("Expected invariant violation, got: {:?}", other),
    }
}

/// Auto-POR: identity assignment detection works with auto-POR.
///
/// The spec uses explicit `x' = x` instead of `UNCHANGED x`, which should
/// still be detected as identity writes and enable independence.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_auto_por_identity_assignment() {
    let stats = expect_success(run_check(IDENTITY_ASSIGNMENT_SPEC, make_config(false, &[])));

    // Auto-POR should detect identity assignments and reduce
    assert_eq!(stats.states_found, 5);
    assert_eq!(stats.por_reduction.independent_pairs, 1);
    assert!(stats.por_reduction.auto_detected);
    assert!(stats.por_reduction.states_reduced > 0);
}
