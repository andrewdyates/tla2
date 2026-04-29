// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::state::State;
use crate::Value;
use ntest::timeout;
use std::collections::HashMap;
use std::sync::Arc;

use super::engine::ObservationConstraint;

#[test]
#[timeout(10_000)]
fn test_observation_constraint_basic() {
    let state = State::new()
        .with_var("x", Value::int(1))
        .with_var("y", Value::int(2));

    let mut values = HashMap::new();
    values.insert(Arc::from("x"), Value::int(1));
    values.insert(Arc::from("y"), Value::int(2));

    let obs = ObservationConstraint { values };
    assert!(obs.matches(&state));

    // Mismatch
    let mut values2 = HashMap::new();
    values2.insert(Arc::from("x"), Value::int(1));
    values2.insert(Arc::from("y"), Value::int(3)); // wrong
    let obs2 = ObservationConstraint { values: values2 };
    assert!(!obs2.matches(&state));
}

#[test]
#[timeout(10_000)]
fn test_step_diagnostic_display_no_actions() {
    let diag = StepDiagnostic {
        successors_enumerated: 42,
        observation_matches: 0,
        action_results: vec![],
        available_actions: vec!["Decide".into(), "Propagate".into()],
    };
    let msg = diag.to_string();
    assert!(msg.contains("42 successors enumerated"));
    assert!(msg.contains("0 matched observation"));
    assert!(msg.contains("Decide"));
    assert!(msg.contains("Propagate"));
    assert!(!msg.contains("actions attempted"));
}

#[test]
#[timeout(10_000)]
fn test_step_diagnostic_display_with_action_results() {
    let diag = StepDiagnostic {
        successors_enumerated: 10,
        observation_matches: 1,
        action_results: vec![
            ActionMatchResult {
                name: "DetectConflict".into(),
                matched: false,
            },
            ActionMatchResult {
                name: "Propagate".into(),
                matched: true,
            },
        ],
        available_actions: vec!["DetectConflict".into(), "Propagate".into()],
    };
    let msg = diag.to_string();
    assert!(msg.contains("1 matched observation"));
    assert!(msg.contains("DetectConflict=no match"));
    assert!(msg.contains("Propagate=matched"));
}

#[test]
#[timeout(10_000)]
fn test_no_matching_states_error_includes_diagnostic() {
    let diag = StepDiagnostic {
        successors_enumerated: 5,
        observation_matches: 0,
        action_results: vec![],
        available_actions: vec!["Foo".into()],
    };
    let err = TraceValidationError::NoMatchingStates {
        step: 2,
        diagnostic: diag,
    };
    let msg = err.to_string();
    assert!(msg.contains("trace step 2"));
    assert!(msg.contains("0 candidates"));
    assert!(msg.contains("5 successors enumerated"));
    assert!(msg.contains("available spec actions: Foo"));
}

#[test]
#[timeout(10_000)]
fn test_action_label_not_satisfied_error_includes_diagnostic() {
    let diag = StepDiagnostic {
        successors_enumerated: 8,
        observation_matches: 1,
        action_results: vec![
            ActionMatchResult {
                name: "A".into(),
                matched: true,
            },
            ActionMatchResult {
                name: "B".into(),
                matched: false,
            },
        ],
        available_actions: vec!["A".into(), "B".into()],
    };
    let err = TraceValidationError::ActionLabelNotSatisfied {
        step: 3,
        label: "B".into(),
        diagnostic: diag,
    };
    let msg = err.to_string();
    assert!(msg.contains("trace step 3"));
    assert!(msg.contains("\"B\""));
    assert!(msg.contains("A=matched"));
    assert!(msg.contains("B=no match"));
}

#[test]
#[timeout(10_000)]
fn test_action_label_mode_default_is_error() {
    assert_eq!(ActionLabelMode::default(), ActionLabelMode::Error);
}

#[test]
#[timeout(10_000)]
fn test_trace_validation_warning_fields() {
    let w = TraceValidationWarning {
        step: 5,
        message: "action label \"X\" did not match".into(),
    };
    assert_eq!(w.step, 5);
    assert!(w.message.contains("did not match"));
}

#[test]
#[timeout(10_000)]
fn test_success_warnings_empty_by_default() {
    let success = TraceValidationSuccess {
        steps_validated: 3,
        candidates_per_step: vec![1, 2, 1],
        total_candidates_enumerated: 10,
        warnings: vec![],
    };
    assert!(success.warnings.is_empty());
}
