// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for liveness error categories, distinct suggestions, JSON cycle
//! action label propagation, and error type mapping.

use super::*;
use crate::{EvalCheckError, LivenessCheckError, RuntimeCheckError};

/// Regression test for #2156: the three liveness error categories
/// (violation, runtime failure, unsupported formula) must map to distinct error codes.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_liveness_error_categories_distinct_codes() {
    use super::super::error_mapping::error_code_from_check_error;
    use crate::CheckError;
    use std::collections::HashSet;

    let categories: Vec<(CheckError, &str)> = vec![
        // Category 1: liveness incomplete / could-not-check (expected limitation)
        (
            LivenessCheckError::Generic("cannot check".to_string()).into(),
            "LivenessError",
        ),
        // Category 2: liveness runtime failure (internal tool bug)
        (
            LivenessCheckError::RuntimeFailure("tarjan invariant".to_string()).into(),
            "LivenessRuntimeFailure",
        ),
        // Category 3a: unsupported formula pattern
        (
            LivenessCheckError::CannotHandleFormula {
                location: "line 1".to_string(),
                reason: None,
            }
            .into(),
            "TlcLiveCannotHandleFormula",
        ),
        // Category 3b: tautological formula (also "cannot handle")
        (
            LivenessCheckError::FormulaTautology {
                property: "Liveness".to_string(),
            }
            .into(),
            "LiveFormulaTautology",
        ),
    ];

    let codes: Vec<String> = categories
        .iter()
        .map(|(err, _)| error_code_from_check_error(err))
        .collect();

    // All codes must be distinct
    let unique: HashSet<&str> = codes.iter().map(std::string::String::as_str).collect();
    assert_eq!(
        unique.len(),
        codes.len(),
        "Liveness error categories must have distinct codes: {:?}",
        categories
            .iter()
            .zip(&codes)
            .map(|((_, name), code)| format!("{name} → {code}"))
            .collect::<Vec<_>>()
    );

    // None may collide with the violation code
    for (i, code) in codes.iter().enumerate() {
        assert_ne!(
            code,
            error_codes::TLC_LIVENESS_VIOLATED,
            "{} must not map to violation code",
            categories[i].1
        );
    }
}

/// Regression test for #2156: LivenessError and LivenessRuntimeFailure
/// must produce distinct suggestions distinguishing expected vs internal errors.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_liveness_error_vs_runtime_failure_distinct_suggestions() {
    use super::super::error_mapping::suggestion_from_check_error;
    use crate::CheckError;

    let incomplete: CheckError = LivenessCheckError::Generic("cannot complete".to_string()).into();
    let runtime: CheckError =
        LivenessCheckError::RuntimeFailure("tarjan invariant".to_string()).into();

    let sug_inc = suggestion_from_check_error(&incomplete).expect("LivenessError has suggestion");
    let sug_rt =
        suggestion_from_check_error(&runtime).expect("LivenessRuntimeFailure has suggestion");

    // Actions must differ — one is "could not complete", the other is "internal runtime failure"
    assert_ne!(
        sug_inc.action, sug_rt.action,
        "LivenessError and LivenessRuntimeFailure must have distinct suggestion actions"
    );
}

/// Regression test for c39dd26: liveness JSON counterexample must include action
/// labels from BOTH prefix and cycle states. Before the fix, only prefix action
/// labels were propagated into the combined trace, causing cycle states to fall
/// back to "Init"/"Next" placeholders.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_liveness_json_cycle_action_labels_propagated() {
    use crate::{ActionLabel, CheckResult, CheckStats, State, Trace};

    // Create prefix (2 states) with action labels
    let prefix_states: Vec<State> = (0..2)
        .map(|i| State::from_pairs([("x", Value::SmallInt(i))]))
        .collect();
    let prefix_labels = vec![
        ActionLabel {
            name: "Initial predicate".to_string(),
            source_location: None,
        },
        ActionLabel {
            name: "Advance".to_string(),
            source_location: None,
        },
    ];
    let prefix = Trace::from_states_with_labels(prefix_states, prefix_labels);

    // Create cycle (2 states) with action labels
    let cycle_states: Vec<State> = (2..4)
        .map(|i| State::from_pairs([("x", Value::SmallInt(i))]))
        .collect();
    let cycle_labels = vec![
        ActionLabel {
            name: "CycleStep".to_string(),
            source_location: None,
        },
        ActionLabel {
            name: "CycleBack".to_string(),
            source_location: None,
        },
    ];
    let cycle = Trace::from_states_with_labels(cycle_states, cycle_labels);

    let result = CheckResult::LivenessViolation {
        property: "TestProp".to_string(),
        prefix,
        cycle,
        stats: CheckStats::default(),
    };

    let output = JsonOutput::new(
        Path::new("/tmp/test_liveness.tla"),
        Some(Path::new("/tmp/test_liveness.cfg")),
        "TestLiveness",
        1,
    )
    .with_check_result(&result, Duration::from_secs(1));

    let json_str = output.to_json().expect("invariant: serialization succeeds");

    // Verify cycle states have their actual action labels, not fallback "Next"
    let parsed: serde_json::Value =
        serde_json::from_str(&json_str).expect("invariant: output is valid JSON");

    let states = parsed["counterexample"]["states"]
        .as_array()
        .expect("counterexample should have states array");

    assert_eq!(
        states.len(),
        4,
        "Combined trace should have 4 states (2 prefix + 2 cycle)"
    );

    // State 1: "Initial predicate" (prefix)
    assert_eq!(
        states[0]["action"]["name"].as_str().unwrap(),
        "Initial predicate"
    );
    // State 2: "Advance" (prefix)
    assert_eq!(states[1]["action"]["name"].as_str().unwrap(), "Advance");
    // State 3: "CycleStep" (cycle — this was broken before c39dd26)
    assert_eq!(
        states[2]["action"]["name"].as_str().unwrap(),
        "CycleStep",
        "Cycle state action label must come from cycle trace, not fall back to 'Next'"
    );
    // State 4: "CycleBack" (cycle — this was broken before c39dd26)
    assert_eq!(
        states[3]["action"]["name"].as_str().unwrap(),
        "CycleBack",
        "Cycle state action label must come from cycle trace, not fall back to 'Next'"
    );

    // Verify loop_start is set correctly
    assert_eq!(
        parsed["counterexample"]["loop_start"].as_u64().unwrap(),
        3,
        "loop_start should be prefix length + 1 (1-indexed)"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_assume_false_emits_assume_violation_error_type() {
    use crate::{CheckResult, CheckStats};

    let result = CheckResult::from_error(
        RuntimeCheckError::AssumeFalse {
            location: "bytes 42-99 of module MC".to_string(),
        }
        .into(),
        CheckStats::default(),
    );

    let output = JsonOutput::new(Path::new("/tmp/test.tla"), None, "Test", 1)
        .with_check_result(&result, Duration::from_secs(0));

    assert_eq!(
        output.result.error_type.as_deref(),
        Some("assume_violation"),
        "AssumeFalse must emit 'assume_violation', not 'runtime_error'"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_error_emits_runtime_error_type() {
    use crate::{CheckResult, CheckStats};

    let result = CheckResult::from_error(
        EvalCheckError::Eval(crate::EvalError::TypeError {
            expected: "bool",
            got: "int",
            span: None,
        })
        .into(),
        CheckStats::default(),
    );

    let output = JsonOutput::new(Path::new("/tmp/test.tla"), None, "Test", 1)
        .with_check_result(&result, Duration::from_secs(0));

    assert_eq!(
        output.result.error_type.as_deref(),
        Some("runtime_error"),
        "Non-AssumeFalse CheckError variants must emit 'runtime_error'"
    );
}
