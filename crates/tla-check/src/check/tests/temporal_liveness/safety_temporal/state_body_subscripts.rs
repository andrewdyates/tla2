// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_property_action_subscript_with_state_body_allows_first_decision_change() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE DecisionOnce ----
VARIABLE decision
none == "none"

Init == decision = none

Next == \/ /\ decision = none
           /\ decision' = "chosen"
        \/ UNCHANGED decision

PaxosConsistency == [][decision = none]_<<decision>>
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        properties: vec!["PaxosConsistency".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 2, "expected none -> chosen state space");
        }
        other => panic!(
            "[][decision = none]_<<decision>> should allow the first decision change, got: {other:?}"
        ),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_property_action_subscript_with_state_body_reports_action_violation() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE DecisionFlip ----
VARIABLE decision
none == "none"

Init == decision = none

Next == \/ /\ decision = none
           /\ decision' = "v1"
        \/ /\ decision = "v1"
           /\ decision' = "v2"
        \/ UNCHANGED decision

PaxosConsistency == [][decision = none]_<<decision>>
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        properties: vec!["PaxosConsistency".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();
    match result {
        CheckResult::PropertyViolation {
            property,
            kind,
            trace,
            stats: _,
        } => {
            assert_eq!(property, "PaxosConsistency");
            assert_eq!(kind, crate::check::api::PropertyViolationKind::ActionLevel);
            // Trace reconstruction may fail (fingerprint not in location index)
            // when not using continue_on_error. Verify trace content only if
            // reconstruction succeeded.
            if let Some(last) = trace.states.last() {
                let decision = last
                    .get("decision")
                    .expect("trace state should include decision");
                assert_eq!(decision, &Value::String("v2".into()));
            }
        }
        other => panic!(
            "[][decision = none]_<<decision>> should fail on the non-stuttering follow-up transition, got: {other:?}"
        ),
    }
}

/// Regression test for #263: in continue_on_error mode, deferred action
/// properties must still surface as PropertyViolation(ActionLevel) instead of
/// being reconstructed later as invariant violations.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_continue_on_error_preserves_action_property_violation_kind() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE DecisionFlipContinue ----
VARIABLE decision
none == "none"

Init == decision = none

Next == \/ /\ decision = none
           /\ decision' = "v1"
        \/ /\ decision = "v1"
           /\ decision' = "v2"
        \/ UNCHANGED decision

PaxosConsistency == [][decision = none]_<<decision>>
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        properties: vec!["PaxosConsistency".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_continue_on_error(true);

    let result = checker.check();
    match result {
        CheckResult::PropertyViolation {
            property,
            kind,
            trace,
            stats: _,
        } => {
            assert_eq!(property, "PaxosConsistency");
            assert_eq!(kind, crate::check::api::PropertyViolationKind::ActionLevel);
            let last = trace.states.last().expect("non-empty trace");
            let decision = last
                .get("decision")
                .expect("trace state should include decision");
            assert_eq!(decision, &Value::String("v2".into()));
        }
        other => panic!(
            "continue_on_error must preserve action-level property attribution, got: {other:?}"
        ),
    }
}
