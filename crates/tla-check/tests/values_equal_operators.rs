// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for #2894: operators that compare Values must use
//! `values_equal` (extensional set equality) instead of `==` (structural).
//!
//! The key test scenario: comparing `1..N` (Value::Interval) against
//! `{1, 2, ..., N}` (Value::Set). These are extensionally equal but
//! structurally different enum variants, so `==` returns false while
//! `values_equal` returns true.

mod common;

use tla_check::{check_module, CheckResult, Config};

/// Regression test for #2894: AssertEq (TLCExt) must use values_equal.
/// Compares 1..3 (Interval) with {1,2,3} (explicit Set). These are
/// extensionally equal but structurally different.
/// With `==`: AssertEq returns FALSE (bug).
/// With `values_equal`: AssertEq returns TRUE (correct).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_asserteq_interval_vs_explicit_set() {
    let spec = r#"
---- MODULE AssertEqIntervalSet ----
EXTENDS Integers, TLCExt

VARIABLE x

Init == x = 1

\* AssertEq(1..3, {1,2,3}) must be TRUE
Next == /\ AssertEq(1..3, {1, 2, 3})
        /\ x' = x

Inv == AssertEq(1..3, {1, 2, 3})
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
                "expected 1 state (AssertEq should hold), got {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!("AssertEq(1..3, {{1,2,3}}) should be TRUE with values_equal (#2894): {error:?}");
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// Regression test for #2894: IsRestriction must use values_equal for
/// function value comparison. Tests with functions whose values are
/// intervals vs explicit sets.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_isrestriction_set_valued_functions() {
    let spec = r#"
---- MODULE IsRestrictionSetValues ----
EXTENDS Integers, Functions

VARIABLE x

\* f maps to interval 1..3, g maps to explicit {1,2,3}
\* IsRestriction(f, g) should be TRUE since f[1] = g[1] extensionally
f == [i \in {1} |-> 1..3]
g == [i \in {1} |-> {1, 2, 3}]

Init == x = 1

Next == x' = x

Inv == IsRestriction(f, g)
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
                "expected 1 state (IsRestriction should hold), got {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!("IsRestriction with interval vs explicit set should be TRUE (#2894): {error:?}");
        }
        other => panic!("unexpected result: {other:?}"),
    }
}
