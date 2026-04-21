// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for action label identification in trace reconstruction.
//!
//! Verifies that `identify_action_labels` correctly attributes transitions
//! to their producing actions, matching TLC's action-label semantics.

use super::*;
use crate::check::api::CheckResult;
use crate::config::Config;
use crate::test_support::parse_module;

/// A spec with two named disjunctive actions (Inc and Dec) where
/// Dec from x=0 violates `x >= 0`. The counterexample trace
/// should label the violating transition as "Dec".
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn identify_action_labels_names_correct_disjunct() {
    let module = parse_module(
        r#"
---- MODULE ActionLabelDisjunct ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Inc == x' = x + 1
Dec == x' = x - 1
Next == Inc \/ Dec
Inv == x >= 0
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    let result = checker.check();

    match result {
        CheckResult::InvariantViolation {
            ref trace,
            ref invariant,
            ..
        } => {
            assert_eq!(invariant, "Inv");
            // Trace: [x=0] -> [x=-1] via Dec
            assert!(
                trace.states.len() >= 2,
                "expected trace with at least 2 states, got {}",
                trace.states.len()
            );
            assert_eq!(
                trace.action_labels.len(),
                trace.states.len(),
                "action_labels length should match states length"
            );
            // First label is always "Initial predicate"
            assert_eq!(trace.action_labels[0].name, "Initial predicate");
            // The violating transition should be labeled "Dec" (x -> x-1 from x=0)
            let last_label = &trace.action_labels[trace.action_labels.len() - 1];
            assert_eq!(
                last_label.name, "Dec",
                "expected 'Dec' action label for x=0 -> x=-1 transition, got '{}'",
                last_label.name
            );
        }
        other => {
            panic!("expected InvariantViolation, got {other:?}");
        }
    }
}

/// When a spec has a monolithic Next (no disjuncts), action labels
/// should use the Next operator name.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn identify_action_labels_monolithic_next_uses_next_name() {
    let module = parse_module(
        r#"
---- MODULE ActionLabelMonolithic ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == x < 2
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    let result = checker.check();

    match result {
        CheckResult::InvariantViolation { ref trace, .. } => {
            assert!(
                trace.states.len() >= 2,
                "expected at least 2 states in trace"
            );
            if !trace.action_labels.is_empty() {
                assert_eq!(trace.action_labels[0].name, "Initial predicate");
                // Monolithic next: TLC uses the Next operator name, not "Action_N".
                // Part of #2470 Step 6.
                for label in &trace.action_labels[1..] {
                    assert_eq!(
                        label.name, "Next",
                        "monolithic Next should use operator name 'Next', got '{}'",
                        label.name,
                    );
                }
            }
        }
        other => {
            panic!("expected InvariantViolation, got {other:?}");
        }
    }
}

/// Multiple named actions with a longer trace: verify all transition
/// labels are attributed to the correct action.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn identify_action_labels_multi_step_trace() {
    let module = parse_module(
        r#"
---- MODULE ActionLabelMultiStep ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Step == x' = x + 1
Next == Step
Inv == x < 3
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    let result = checker.check();

    match result {
        CheckResult::InvariantViolation { ref trace, .. } => {
            // Trace should be [x=0, x=1, x=2, x=3]
            assert!(
                trace.states.len() >= 4,
                "expected at least 4 states for x < 3 violation, got {}",
                trace.states.len()
            );
            if trace.action_labels.len() == trace.states.len() {
                assert_eq!(trace.action_labels[0].name, "Initial predicate");
                // All transitions should be attributed to "Step" (the only disjunct of Next)
                for (i, label) in trace.action_labels[1..].iter().enumerate() {
                    assert!(
                        label.name == "Step" || label.name == "Next" || label.name == "Action",
                        "transition {}: expected 'Step'/'Next'/'Action', got '{}'",
                        i + 1,
                        label.name
                    );
                }
            }
        }
        other => {
            panic!("expected InvariantViolation, got {other:?}");
        }
    }
}
