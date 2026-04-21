// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `check_property_tautologies`.

use super::*;
use crate::LivenessCheckError;

/// Tautological liveness: `Prop == <>TRUE` — negation is `[]FALSE`,
/// which is trivially unsatisfiable. Should be detected.
#[test]
fn tautology_eventually_true_detected() {
    let src = r#"
---- MODULE TautEventuallyTrue ----
VARIABLE x
Prop == <>TRUE
===="#;
    let (op_defs, ctx, _root) = setup_for_classification(src);
    let properties = vec!["Prop".to_string()];
    let result = check_property_tautologies(&ctx, &properties, &op_defs, "TautEventuallyTrue");

    assert!(result.is_some(), "Expected tautology detection for <>TRUE");
    match result.unwrap() {
        CheckError::Liveness(LivenessCheckError::FormulaTautology { property }) => {
            assert_eq!(property, "Prop");
        }
        other => panic!("Expected LiveFormulaTautology, got: {:?}", other),
    }
}

/// Non-tautological liveness: `Prop == <>(x = 1)` — negation `[](x /= 1)`
/// is satisfiable. Should return None.
#[test]
fn tautology_normal_liveness_not_detected() {
    let src = r#"
---- MODULE TautNormal ----
VARIABLE x
Prop == <>(x = 1)
===="#;
    let (op_defs, ctx, _root) = setup_for_classification(src);
    let properties = vec!["Prop".to_string()];
    let result = check_property_tautologies(&ctx, &properties, &op_defs, "TautNormal");

    assert!(
        result.is_none(),
        "Non-tautological property should not be flagged"
    );
}

/// Purely safety property: `Inv == [](x >= 0)` — no liveness part to
/// check, so tautology detection should return None.
#[test]
fn tautology_purely_safety_returns_none() {
    let src = r#"
---- MODULE TautPureSafety ----
EXTENDS Integers
VARIABLE x
Inv == [](x >= 0)
===="#;
    let (op_defs, ctx, _root) = setup_for_classification(src);
    let properties = vec!["Inv".to_string()];
    let result = check_property_tautologies(&ctx, &properties, &op_defs, "TautPureSafety");

    assert!(
        result.is_none(),
        "Purely safety property has no liveness part to be tautological"
    );
}

/// Mixed property with tautological liveness: `Prop == [](x >= 0) /\ <>TRUE`.
/// The safety part `[](x >= 0)` should be separated out, and the liveness
/// part `<>TRUE` should be detected as tautological.
#[test]
fn tautology_mixed_safety_tautological_liveness_detected() {
    let src = r#"
---- MODULE TautMixed ----
EXTENDS Integers
VARIABLE x
Prop == [](x >= 0) /\ <>TRUE
===="#;
    let (op_defs, ctx, _root) = setup_for_classification(src);
    let properties = vec!["Prop".to_string()];
    let result = check_property_tautologies(&ctx, &properties, &op_defs, "TautMixed");

    assert!(
        result.is_some(),
        "Expected tautology detection for liveness part of mixed property"
    );
    match result.unwrap() {
        CheckError::Liveness(LivenessCheckError::FormulaTautology { property }) => {
            assert_eq!(property, "Prop");
        }
        other => panic!("Expected LiveFormulaTautology, got: {:?}", other),
    }
}

/// Empty properties — should return None immediately.
#[test]
fn tautology_empty_properties_returns_none() {
    let src = r#"
---- MODULE TautEmpty ----
VARIABLE x
===="#;
    let (op_defs, ctx, _root) = setup_for_classification(src);
    let result = check_property_tautologies(&ctx, &[], &op_defs, "TautEmpty");
    assert!(result.is_none());
}
