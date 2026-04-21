// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_safety_temporal_property_init_and_always_action_satisfied() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // PROPERTY that is actually a safety-style spec formula:
    //   Init /\ [][Next]_vars
    // should be checkable without the full liveness tableau algorithm.
    let src = r"
---- MODULE SafetyPropSat ----
EXTENDS Integers

VARIABLE x
vars == <<x>>

Init == x = 0

Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

SpecProp == Init /\ [][Next]_vars
====
";
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        properties: vec!["SpecProp".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();
    match result {
        CheckResult::Success(stats) => {
            // x takes values 0, 1, 2
            assert_eq!(stats.states_found, 3);
        }
        other => panic!("Expected success, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_safety_temporal_property_init_and_always_action_violated() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Next increments, but property requires stuttering (UNCHANGED x) on every step.
    let src = r"
---- MODULE SafetyPropViol ----
EXTENDS Integers

VARIABLE x
vars == <<x>>

Init == x = 0

Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

Bad == UNCHANGED x
SpecProp == Init /\ [][Bad]_vars
====
";
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        properties: vec!["SpecProp".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true); // Property checking requires full states

    let result = checker.check();
    match result {
        // Part of #2834: implied action violations from PROPERTIES are correctly
        // reported as PropertyViolation (they are property checks, not invariants).
        CheckResult::PropertyViolation {
            property,
            trace: _,
            stats: _,
            kind: _,
        } => {
            assert_eq!(property, "SpecProp");
        }
        other => panic!("Expected PropertyViolation for implied action, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_safety_temporal_bare_action_always_rejected() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r"
---- MODULE SafetyPropBareAction ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

Prop == [](x' > x)
====
";
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);

    let result = checker.check();
    assert_temporal_action_form_rejected(result, "bare []A");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_safety_temporal_real_angle_action_subscript_property_succeeds() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r"
---- MODULE SafetyPropRealAngleAction ----
EXTENDS Integers

VARIABLE x
vars == <<x>>

Init == x = 0

Next == IF x < 2 THEN x' = x + 1 ELSE x' = 0

Prop == []<<Next>>_vars
====
";
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 3);
        }
        other => panic!("Expected success for real []<<A>>_v syntax, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_safety_temporal_expanded_action_always_rejected() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r"
---- MODULE SafetyPropExpandedAction ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

Prop == []((x' > x) \\/ UNCHANGED x)
====
";
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);

    let result = checker.check();
    assert_temporal_action_form_rejected(result, "expanded [](A \\/ UNCHANGED v)");
}
