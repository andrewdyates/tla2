// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parallel PROPERTY safety-temporal regression coverage.
//!
//! Part of #3141: mirror the sequential safety-temporal PROPERTY tests in the
//! parallel checker so the fast path is exercised directly.
//!
//! Coverage:
//! - Init + ActionCompiled (`Init /\ [][Next]_vars`): satisfied + violated
//! - StateCompiled (`[](x >= 0)`): satisfied + violated
//! - Combined multi-bucket: Init + StateCompiled + ActionCompiled
//!
//! The parallel checker promotes fully-classifiable safety-temporal properties
//! to BFS-phase checking (via `classify_property_safety_parts` in prepare.rs).
//! These tests verify that promotion + BFS-phase evaluation produces correct
//! results for all three term buckets.

mod common;

use ntest::timeout;
use tla_check::{check_module_parallel, CheckResult, Config};

#[cfg_attr(test, timeout(10000))]
#[test]
fn test_parallel_property_safety_temporal_init_and_always_action_satisfied() {
    let src = r#"
---- MODULE ParallelSafetyPropSat ----
EXTENDS Integers

VARIABLE x
vars == <<x>>

Init == x = 0

Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

SpecProp == Init /\ [][Next]_vars
====
"#;
    let module = common::parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["SpecProp".to_string()],
        ..Default::default()
    };

    let result = check_module_parallel(&module, &config, 2);
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 3, "expected x to range over 0, 1, 2");
        }
        other => panic!("expected parallel PROPERTY safety-temporal success, got {other:?}"),
    }
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn test_parallel_property_safety_temporal_init_and_always_action_violated() {
    let src = r#"
---- MODULE ParallelSafetyPropViol ----
EXTENDS Integers

VARIABLE x
vars == <<x>>

Init == x = 0

Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

Bad == UNCHANGED x
SpecProp == Init /\ [][Bad]_vars
====
"#;
    let module = common::parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["SpecProp".to_string()],
        ..Default::default()
    };

    let result = check_module_parallel(&module, &config, 2);
    match result {
        CheckResult::PropertyViolation { property, .. } => {
            assert_eq!(property, "SpecProp");
        }
        other => panic!(
            "expected parallel PROPERTY safety-temporal violation for SpecProp, got {other:?}"
        ),
    }
}

/// State-level always predicate satisfied: [](x >= 0) holds for x in {0,1,2}.
/// Exercises the StateCompiled term bucket in classify_property_safety_parts.
#[cfg_attr(test, timeout(10000))]
#[test]
fn test_parallel_property_state_level_always_satisfied() {
    let src = r#"
---- MODULE ParallelStatePropSat ----
EXTENDS Integers

VARIABLE x
vars == <<x>>

Init == x = 0

Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

AlwaysNonNeg == [](x >= 0)
====
"#;
    let module = common::parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["AlwaysNonNeg".to_string()],
        ..Default::default()
    };

    let result = check_module_parallel(&module, &config, 2);
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 3, "expected x to range over 0, 1, 2");
        }
        other => panic!("expected parallel state-level always success, got {other:?}"),
    }
}

/// State-level always predicate violated: [](x < 2) fails when x reaches 2.
/// Exercises the StateCompiled term bucket violation detection.
#[cfg_attr(test, timeout(10000))]
#[test]
fn test_parallel_property_state_level_always_violated() {
    let src = r#"
---- MODULE ParallelStatePropViol ----
EXTENDS Integers

VARIABLE x
vars == <<x>>

Init == x = 0

Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

AlwaysLt2 == [](x < 2)
====
"#;
    let module = common::parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["AlwaysLt2".to_string()],
        ..Default::default()
    };

    let result = check_module_parallel(&module, &config, 2);
    match result {
        CheckResult::PropertyViolation { property, .. } => {
            assert_eq!(property, "AlwaysLt2");
        }
        other => {
            panic!("expected parallel state-level always violation for AlwaysLt2, got {other:?}")
        }
    }
}

/// Combined multi-bucket property: Init /\ [](x >= 0) /\ [][Next]_vars
/// Exercises Init + StateCompiled + ActionCompiled together in one property.
#[cfg_attr(test, timeout(10000))]
#[test]
fn test_parallel_property_combined_multi_bucket_satisfied() {
    let src = r#"
---- MODULE ParallelCombinedPropSat ----
EXTENDS Integers

VARIABLE x
vars == <<x>>

Init == x = 0

Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

FullSpec == Init /\ [](x >= 0) /\ [][Next]_vars
====
"#;
    let module = common::parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["FullSpec".to_string()],
        ..Default::default()
    };

    let result = check_module_parallel(&module, &config, 2);
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 3, "expected x to range over 0, 1, 2");
        }
        other => panic!("expected parallel combined multi-bucket success, got {other:?}"),
    }
}
