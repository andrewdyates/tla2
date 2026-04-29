// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `classify_property_safety_parts` and `classify_safety_temporal`.

use super::*;

/// Purely safety property: `Inv == [](x >= 0)` — should extract an eval-state
/// check and mark Inv as a promoted invariant.
#[test]
fn classify_purely_safety_property_extracts_state_guard() {
    let src = r"
---- MODULE ClassifyPureSafety ----
EXTENDS Integers
VARIABLE x
Inv == [](x >= 0)
====";
    let (op_defs, ctx, _root) = setup_for_classification(src);
    let properties = vec!["Inv".to_string()];
    let result = classify_property_safety_parts(&ctx, &properties, &op_defs);

    assert_eq!(
        result.eval_state_invariants.len(),
        1,
        "Expected one eval-state invariant extracted from []P"
    );
    assert_eq!(result.eval_state_invariants[0].0, "Inv");
    assert!(
        result
            .promoted_invariant_properties
            .contains(&"Inv".to_string()),
        "Purely safety property should be fully promoted"
    );
    assert!(
        result.eval_implied_actions.is_empty(),
        "No action-level eval terms expected"
    );
}

/// Purely liveness property: `Prop == <>(x = 1)` — no safety guards,
/// no promotions. Everything deferred to post-BFS liveness.
#[test]
fn classify_purely_liveness_property_extracts_nothing() {
    let src = r"
---- MODULE ClassifyPureLiveness ----
VARIABLE x
Prop == <>(x = 1)
====";
    let (op_defs, ctx, _root) = setup_for_classification(src);
    let properties = vec!["Prop".to_string()];
    let result = classify_property_safety_parts(&ctx, &properties, &op_defs);

    assert!(
        result.eval_state_invariants.is_empty(),
        "No eval-state invariants for purely liveness property"
    );
    assert!(
        result.eval_implied_actions.is_empty(),
        "No eval-action terms for purely liveness property"
    );
    assert!(
        result.promoted_invariant_properties.is_empty(),
        "Liveness property should not be promoted"
    );
    assert!(
        result.promoted_action_properties.is_empty(),
        "Liveness property should not be promoted"
    );
}

/// Mixed property: `Prop == [](x >= 0) /\ <>(x = 1)` — state guard
/// extracted for `[](x >= 0)`, but property NOT promoted (has liveness).
#[test]
fn classify_mixed_state_liveness_extracts_but_no_promotion() {
    let src = r"
---- MODULE ClassifyMixed ----
EXTENDS Integers
VARIABLE x
Prop == [](x >= 0) /\ <>(x = 1)
====";
    let (op_defs, ctx, _root) = setup_for_classification(src);
    let properties = vec!["Prop".to_string()];
    let result = classify_property_safety_parts(&ctx, &properties, &op_defs);

    assert_eq!(
        result.eval_state_invariants.len(),
        1,
        "State safety term should be extracted into eval_state_invariants"
    );
    assert!(
        !result
            .promoted_invariant_properties
            .contains(&"Prop".to_string()),
        "Mixed property must NOT be promoted — liveness part remains"
    );
}

/// Property with ENABLED in Always body: `Prop == [](ENABLED <<Next>>_vars)`
/// should use the eval-state-invariant lane instead of the liveness path.
#[test]
fn classify_always_with_enabled_promoted_to_eval_state_invariant() {
    let src = r"
---- MODULE ClassifyEnabled ----
VARIABLE x
vars == <<x>>
Next == x' = x
Prop == [](ENABLED <<Next>>_vars)
====";
    let (op_defs, ctx, _root) = setup_for_classification(src);
    let properties = vec!["Prop".to_string()];
    let result = classify_property_safety_parts(&ctx, &properties, &op_defs);

    assert!(
        result.eval_state_invariants.len() == 1,
        "ENABLED property should use eval_state_invariants"
    );
    assert!(
        result
            .promoted_invariant_properties
            .contains(&"Prop".to_string()),
        "ENABLED property should be promoted for BFS checking"
    );
}

#[test]
fn classify_enabled_property_consistent_across_shared_adapters() {
    let src = r"
---- MODULE ClassifyEnabledConsistency ----
VARIABLE x
vars == <<x>>
Next == x' = x
Prop == []((~ENABLED <<Next>>_vars) => (x = x))
====";
    let (op_defs, ctx, _root) = setup_for_classification(src);
    let properties = vec!["Prop".to_string()];
    let property_result = classify_property_safety_parts(&ctx, &properties, &op_defs);

    assert_eq!(
        property_result.eval_state_invariants.len(),
        1,
        "shared PROPERTY planner should route ENABLED state terms to eval_state_invariants"
    );

    match classify_safety_temporal(&ctx, &op_defs, "Prop") {
        SafetyTemporalClassification::Applicable {
            init_terms,
            always_state_terms,
            always_action_terms,
        } => {
            assert!(
                init_terms.is_empty(),
                "property should not create init terms"
            );
            assert_eq!(
                always_state_terms.len(),
                1,
                "shared planner should expose one state-level safety term"
            );
            assert!(
                always_action_terms.is_empty(),
                "state-level ENABLED property should not create action terms"
            );
        }
        SafetyTemporalClassification::NotApplicable => {
            panic!("shared safety-temporal adapter should accept state-level ENABLED property")
        }
    }
}

#[test]
fn classify_safety_temporal_rejects_eventually_property() {
    let src = r"
---- MODULE ClassifyEventually ----
VARIABLE x
Prop == <>(x = 1)
====";
    let (op_defs, ctx, _root) = setup_for_classification(src);

    assert!(
        matches!(
            classify_safety_temporal(&ctx, &op_defs, "Prop"),
            SafetyTemporalClassification::NotApplicable
        ),
        "genuine temporal properties must still use the liveness checker"
    );
}

#[test]
fn classify_bare_action_always_is_not_promoted() {
    let src = r"
---- MODULE ClassifyBareActionAlways ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
Prop == [](x' > x)
====";
    let (op_defs, ctx, _root) = setup_for_classification(src);
    let properties = vec!["Prop".to_string()];
    let result = classify_property_safety_parts(&ctx, &properties, &op_defs);

    assert!(
        result.eval_implied_actions.is_empty(),
        "bare []A must not be promoted onto the eval-implied-action lane"
    );
    assert!(
        result.promoted_action_properties.is_empty(),
        "bare []A must remain on the liveness/rejection path"
    );
    assert!(
        matches!(
            classify_safety_temporal(&ctx, &op_defs, "Prop"),
            SafetyTemporalClassification::NotApplicable
        ),
        "bare []A must not enter the safety-temporal fast path"
    );
}

#[test]
fn classify_real_action_subscript_still_promotes() {
    let src = r"
---- MODULE ClassifyRealActionSubscript ----
EXTENDS Integers
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Prop == [][Next]_vars
====";
    let (op_defs, ctx, _root) = setup_for_classification(src);
    let properties = vec!["Prop".to_string()];
    let result = classify_property_safety_parts(&ctx, &properties, &op_defs);

    assert_eq!(
        result.eval_implied_actions.len(),
        1,
        "real [][A]_vars syntax must still promote to eval-implied-action checking"
    );
    assert!(
        result
            .promoted_action_properties
            .contains(&"Prop".to_string()),
        "real [][A]_vars should remain fully promoted"
    );
}

#[test]
fn classify_real_angle_action_subscript_still_promotes() {
    let src = r"
---- MODULE ClassifyRealAngleActionSubscript ----
EXTENDS Integers
VARIABLE x
vars == <<x>>
Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE x' = 0
Prop == []<<Next>>_vars
====";
    let (op_defs, ctx, _root) = setup_for_classification(src);
    let properties = vec!["Prop".to_string()];
    let result = classify_property_safety_parts(&ctx, &properties, &op_defs);

    assert_eq!(
        result.eval_implied_actions.len(),
        1,
        "real []<<A>>_vars syntax must still promote to eval-implied-action checking"
    );
    assert!(
        result
            .promoted_action_properties
            .contains(&"Prop".to_string()),
        "real []<<A>>_vars should remain fully promoted"
    );
    let classification = classify_safety_temporal(&ctx, &op_defs, "Prop");
    assert!(
        matches!(
            &classification,
            SafetyTemporalClassification::Applicable {
                always_action_terms,
                ..
            } if always_action_terms.len() == 1
        ),
        "real []<<A>>_vars should remain on the safety-temporal fast path, got: {classification:?}"
    );
}

/// Empty properties list — should produce empty classification.
#[test]
fn classify_empty_properties_returns_empty() {
    let src = r"
---- MODULE ClassifyEmpty ----
VARIABLE x
====";
    let (op_defs, ctx, _root) = setup_for_classification(src);
    let result = classify_property_safety_parts(&ctx, &[], &op_defs);

    assert!(result.eval_state_invariants.is_empty());
    assert!(result.eval_implied_actions.is_empty());
    assert!(result.promoted_invariant_properties.is_empty());
    assert!(result.promoted_action_properties.is_empty());
}

/// Part of #263: PaxosConsistency pattern — `[][decision = none]_<<decision>>`
/// where the action body is a state-level expression and the subscript
/// variables are a tuple. This is the exact pattern from the FastPaxos spec.
/// The `[A]_v` lowering records an action subscript span that must be
/// recognized by the classifier for correct BFS-phase implied-action checking.
#[test]
fn classify_action_subscript_with_state_body_promotes_to_implied_action() {
    let src = r#"
---- MODULE ClassifyPaxosConsistency ----
VARIABLE decision
none == "none"
PaxosConsistency == [][decision = none]_<<decision>>
===="#;
    let (op_defs, ctx, _root) = setup_for_classification(src);
    let properties = vec!["PaxosConsistency".to_string()];
    let result = classify_property_safety_parts(&ctx, &properties, &op_defs);

    assert_eq!(
        result.eval_implied_actions.len(),
        1,
        "[][A]_<<v>> with state-level A must promote to eval-implied-action; \
         got {} implied actions and {} state invariants",
        result.eval_implied_actions.len(),
        result.eval_state_invariants.len(),
    );
    assert!(
        result
            .promoted_action_properties
            .contains(&"PaxosConsistency".to_string()),
        "PaxosConsistency should be fully promoted (no liveness terms)"
    );

    // Also verify the safety-temporal fast path agrees.
    let classification = classify_safety_temporal(&ctx, &op_defs, "PaxosConsistency");
    assert!(
        matches!(
            &classification,
            SafetyTemporalClassification::Applicable {
                always_action_terms,
                ..
            } if always_action_terms.len() == 1
        ),
        "safety-temporal should classify as applicable with 1 action term, \
         got: {classification:?}"
    );
}
