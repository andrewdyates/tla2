// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Action-form temporal semantics tests (Part of #3150).

use super::*;

/// Part of #3150: real subscript syntax `[][A]_v` remains valid and should
/// still use the action-level safety path.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_real_action_subscript_property_succeeds() {
    let _serial = super::super::acquire_interner_lock();
    let src = r"
---- MODULE ParallelRealActionSubscript ----
EXTENDS Integers
VARIABLE x
vars == <<x>>
Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x
Prop == [][x' > x]_x
====
";
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let checker = ParallelChecker::new(&module, &config, 2);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert!(stats.states_found > 0, "Expected states to be explored");
        }
        other => panic!("Expected Success for real [][A]_v syntax, got: {other:?}"),
    }
}

/// Part of #3150: real angle-bracket subscript syntax `[]<<A>>_v` must also
/// stay on the promoted PROPERTY lane.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_real_angle_action_subscript_property_succeeds() {
    let _serial = super::super::acquire_interner_lock();
    let src = r"
---- MODULE ParallelRealAngleActionSubscript ----
EXTENDS Integers
VARIABLE x
vars == <<x>>
Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE x' = 0
Prop == []<<Next>>_vars
====
";
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let checker = ParallelChecker::new(&module, &config, 2);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert!(stats.states_found > 0, "Expected states to be explored");
        }
        other => panic!("Expected Success for real []<<A>>_v syntax, got: {other:?}"),
    }
}

/// Part of #3150: TLC rejects bare action-level `[]A`; it must not be
/// promoted into the safety-temporal fast path.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_bare_action_always_rejected() {
    let _serial = super::super::acquire_interner_lock();
    let src = r"
---- MODULE ParallelBareActionAlways ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x
Prop == [](x' > x)
====
";
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let checker = ParallelChecker::new(&module, &config, 2);
    let result = checker.check();

    super::assert_temporal_action_form_rejected(result, "bare []A");
}

/// Part of #3150: the explicitly expanded form is also invalid; TLC only
/// accepts the original `[A]_v` syntax, not `[](A \/ UNCHANGED v)`.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_expanded_action_always_rejected() {
    let _serial = super::super::acquire_interner_lock();
    let src = r"
---- MODULE ParallelExpandedActionAlways ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x
Prop == []((x' > x) \/ UNCHANGED x)
====
";
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let checker = ParallelChecker::new(&module, &config, 2);
    let result = checker.check();

    super::assert_temporal_action_form_rejected(result, "expanded [](A \\/ UNCHANGED v)");
}
