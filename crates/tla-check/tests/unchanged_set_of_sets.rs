// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression test for #2891: eval_unchanged must use values_equal (not ==)
//! for set-correct equality comparison. Without values_equal, structurally
//! different representations of the same set (e.g., {1,2} vs {2,1}) could
//! compare as not-equal, causing spurious deadlocks or missed behaviors.

mod common;

use tla_check::{check_module, CheckResult, Config};

/// Core regression test for #2891: UNCHANGED keyword with a set-of-sets value.
/// This directly exercises the eval_unchanged code path (not s' = s assignment)
/// with the data type that would trigger incorrect results under `==` comparison.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_keyword_set_of_sets() {
    let spec = r#"
---- MODULE UnchangedKeywordSetOfSets ----
VARIABLE s

Init == s = {{1, 2}, {3}}

Next == UNCHANGED s

Inv == s = {{1, 2}, {3}}
====
"#;

    let module = common::parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1,
                "expected 1 state for UNCHANGED s with set-of-sets, got {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!("UNCHANGED s with set-of-sets should not cause eval error (#2891): {error:?}");
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// Baseline test: explicit prime assignment s' = s with set-of-sets.
/// Exercises the general equality path (not eval_unchanged specifically).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prime_assign_single_var_set_of_sets() {
    let spec = r#"
---- MODULE PrimeAssignSingleVar ----
VARIABLE s

Init == s = {{1, 2}, {3}}

Next == s' = s

Inv == s = {{1, 2}, {3}}
====
"#;

    let module = common::parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1,
                "expected 1 state for s' = s with set-of-sets, got {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!("s' = s with set-of-sets should not cause eval error: {error:?}");
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// Test that UNCHANGED correctly preserves a simple set-valued variable.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_keyword_single_var_set() {
    let spec = r#"
---- MODULE UnchangedKeywordSet ----
VARIABLE s

Init == s = {1, 2, 3}

Next == UNCHANGED s

Inv == s = {1, 2, 3}
====
"#;

    let module = common::parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1,
                "expected 1 state for UNCHANGED s with set value, got {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!("UNCHANGED s with set should not cause eval error: {error:?}");
        }
        other => panic!("unexpected result: {other:?}"),
    }
}
