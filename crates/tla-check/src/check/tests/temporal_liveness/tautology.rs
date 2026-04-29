// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Part of #2215: []TRUE is classified as a safety property by `separate_safety_liveness_parts()`
/// and never reaches the liveness checker. TLC also accepts this as Success, so we match.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_always_true_property_classified_as_safety_succeeds() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE AlwaysTrueTest ----
VARIABLE x
Init == x = 0
Next == x' = x
Prop == []TRUE
====
"#;
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
    // []TRUE goes through the safety-temporal path and succeeds (matches TLC behavior).
    match result {
        CheckResult::Success(stats) => {
            assert!(
                stats.states_found > 0,
                "[]TRUE safety path should explore at least one state, got 0"
            );
            assert_eq!(
                stats.states_found, 1,
                "single-variable stuttering spec should have exactly 1 state"
            );
        }
        other => panic!(
            "Expected Success for []TRUE property (safety path), got: {:?}",
            other
        ),
    }
}

/// Part of #2215: <>TRUE is a tautological liveness property. TLC rejects it with
/// TLC_LIVE_FORMULA_TAUTOLOGY (EC 2253). We should match.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tautological_liveness_property_eventually_true_rejected() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE EventuallyTrueTest ----
VARIABLE x
Init == x = 0
Next == x' = x
Prop == <>TRUE
====
"#;
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
        CheckResult::Error { error, .. } => {
            assert!(
                matches!(
                    error,
                    CheckError::Liveness(LivenessCheckError::FormulaTautology { .. })
                ),
                "Expected LiveFormulaTautology error, got: {:?}",
                error
            );
        }
        other => panic!(
            "Expected Error(LiveFormulaTautology) for <>TRUE, got: {:?}",
            other
        ),
    }
}

/// Part of #2215: []<>TRUE is a tautological liveness property. The negation
/// []<>TRUE → ~([]<>TRUE) → <>[]FALSE → trivially unsatisfiable.
/// TLC should also reject this pattern.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tautological_liveness_always_eventually_true_rejected() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE AlwaysEventuallyTrueTest ----
VARIABLE x
Init == x = 0
Next == x' = x
Prop == []<>TRUE
====
"#;
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
        CheckResult::Error { error, .. } => {
            assert!(
                matches!(
                    error,
                    CheckError::Liveness(LivenessCheckError::FormulaTautology { .. })
                ),
                "Expected LiveFormulaTautology for []<>TRUE, got: {:?}",
                error
            );
        }
        other => panic!(
            "Expected Error(LiveFormulaTautology) for []<>TRUE, got: {:?}",
            other
        ),
    }
}

/// Part of #2215: Non-tautological liveness property should NOT trigger
/// the tautology check. <>(x = 1) is a real liveness property that depends
/// on the spec's behavior — not trivially satisfiable.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_non_tautological_liveness_property_not_rejected() {
    use crate::LivenessCheckError;
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE NonTautTest ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == IF x < 3 THEN x' = x + 1 ELSE UNCHANGED x
Prop == <>(x = 3)
====
"#;
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
    // This should NOT be detected as tautological — it's a real liveness property.
    // It may fail liveness (stuttering), but it should NOT be rejected outright.
    assert!(
        !matches!(
            result,
            CheckResult::Error {
                error: CheckError::Liveness(LivenessCheckError::FormulaTautology { .. }),
                ..
            }
        ),
        "Non-tautological property <>(x=3) should NOT be flagged as tautology, got: {:?}",
        result
    );
}
