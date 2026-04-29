// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Named-instance PROPERTY classification regressions for #3148.

use super::*;
use std::sync::Arc;
use tla_core::ast::Unit;
use tla_core::{lower, parse_to_syntax_tree, FileId};

fn setup_named_instance_property_classification(
    inner_src: &str,
    outer_src: &str,
) -> (FxHashMap<String, tla_core::ast::OperatorDef>, EvalCtx) {
    let inner_tree = parse_to_syntax_tree(inner_src);
    let inner_lowered = lower(FileId(1), &inner_tree);
    assert!(
        inner_lowered.errors.is_empty(),
        "inner module errors: {:?}",
        inner_lowered.errors
    );
    let inner_module = inner_lowered.module.expect("inner module should lower");

    let outer_tree = parse_to_syntax_tree(outer_src);
    let outer_lowered = lower(FileId(0), &outer_tree);
    assert!(
        outer_lowered.errors.is_empty(),
        "outer module errors: {:?}",
        outer_lowered.errors
    );
    let outer_module = outer_lowered.module.expect("outer module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&outer_module);
    ctx.load_instance_module(inner_module.name.node.clone(), &inner_module);

    let mut op_defs: FxHashMap<String, tla_core::ast::OperatorDef> = FxHashMap::default();
    for unit in &outer_module.units {
        match &unit.node {
            Unit::Variable(var_names) => {
                for var in var_names {
                    ctx.register_var(Arc::from(var.node.as_str()));
                }
            }
            Unit::Operator(def) => {
                op_defs.insert(def.name.node.clone(), def.clone());
            }
            _ => {}
        }
    }

    (op_defs, ctx)
}

fn named_instance_sources(inner_module: &str, outer_module: &str) -> (String, String) {
    let inner_src = format!(
        r#"
---- MODULE {inner_module} ----
EXTENDS Integers
VARIABLE x
vars == <<x>>
Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x
Spec == Init /\ [][Next]_vars
Bad == []((Next) \/ UNCHANGED vars)
Raw == []Next
===="#
    );
    let outer_src = format!(
        r#"
---- MODULE {outer_module} ----
EXTENDS Integers
VARIABLE x
I == INSTANCE {inner_module}
Refines == I!Spec
Expanded == I!Bad
RawRefines == I!Raw
===="#
    );
    (inner_src, outer_src)
}

fn named_instance_init_split_sources(inner_module: &str, outer_module: &str) -> (String, String) {
    let inner_src = format!(
        r#"
---- MODULE {inner_module} ----
EXTENDS Integers
VARIABLE x
vars == <<x>>
Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x
Spec == Init /\ [][Next]_vars
===="#
    );
    let outer_src = format!(
        r#"
---- MODULE {outer_module} ----
EXTENDS Integers
VARIABLE x
InitLeft == x = 0
InitRight == x \in 0..2
I == INSTANCE {inner_module} WITH Init <- (InitLeft /\ InitRight)
Refines == I!Spec
===="#
    );
    (inner_src, outer_src)
}

fn classify_named_instance_property(
    inner_module: &str,
    outer_module: &str,
    property: &str,
) -> PropertySafetyClassification {
    let (inner_src, outer_src) = named_instance_sources(inner_module, outer_module);
    let (op_defs, ctx) = setup_named_instance_property_classification(&inner_src, &outer_src);
    classify_property_safety_parts(&ctx, &[property.to_string()], &op_defs)
}

fn classify_named_instance_init_split_property(
    inner_module: &str,
    outer_module: &str,
    property: &str,
) -> PropertySafetyClassification {
    let (inner_src, outer_src) = named_instance_init_split_sources(inner_module, outer_module);
    let (op_defs, ctx) = setup_named_instance_property_classification(&inner_src, &outer_src);
    classify_property_safety_parts(&ctx, &[property.to_string()], &op_defs)
}

fn assert_unpromoted(result: &PropertySafetyClassification, property: &str, description: &str) {
    assert!(
        result.init_predicates.is_empty(),
        "{description} should not extract init predicates"
    );
    assert!(
        result.eval_state_invariants.is_empty(),
        "{description} should not extract eval-state invariants"
    );
    assert!(
        result.eval_implied_actions.is_empty(),
        "{description} must not promote to eval-based implied-action checking"
    );
    assert!(
        !result
            .promoted_invariant_properties
            .contains(&property.to_string()),
        "{description} must remain on the rejection/liveness path"
    );
    assert!(
        !result
            .promoted_action_properties
            .contains(&property.to_string()),
        "{description} must remain on the rejection/liveness path"
    );
}

#[test]
fn classify_named_instance_real_action_subscript_promotes_eval_implied_action() {
    let result =
        classify_named_instance_property("InnerInstanceSpec", "OuterInstanceSpec", "Refines");

    assert_eq!(
        result.init_predicates.len(),
        1,
        "named-instance Spec should contribute one init predicate"
    );
    assert_eq!(
        result.eval_implied_actions.len(),
        1,
        "named-instance [][Next]_vars should promote to eval-based implied-action checking"
    );
    assert!(
        result.eval_state_invariants.is_empty(),
        "named-instance action subscript should not create eval-state invariants"
    );
    assert!(
        result
            .promoted_invariant_properties
            .contains(&"Refines".to_string()),
        "fully handled named-instance Spec should be skipped by post-BFS liveness"
    );
    assert!(
        result
            .promoted_action_properties
            .contains(&"Refines".to_string()),
        "fully handled named-instance Spec should be marked as promoted action safety"
    );
}

#[test]
fn classify_named_instance_expanded_action_always_stays_unpromoted() {
    let result =
        classify_named_instance_property("InnerExpandedSpec", "OuterExpandedSpec", "Expanded");
    assert_unpromoted(&result, "Expanded", "expanded [](A \\/ UNCHANGED vars)");
}

#[test]
fn classify_named_instance_raw_action_always_stays_unpromoted() {
    let result = classify_named_instance_property("InnerRawSpec", "OuterRawSpec", "RawRefines");
    assert_unpromoted(&result, "RawRefines", "named-instance []Next");
}

#[test]
fn classify_named_instance_init_substitution_keeps_property_promoted() {
    let result = classify_named_instance_init_split_property(
        "InnerInitSplitSpec",
        "OuterInitSplitSpec",
        "Refines",
    );

    assert_eq!(
        result.init_predicates.len(),
        1,
        "planner keeps the substituted instance init as one eval-time init predicate"
    );
    assert_eq!(
        result.eval_implied_actions.len(),
        1,
        "named-instance [][Next]_vars should stay promoted after init conjunct expansion"
    );
    assert!(
        result.eval_state_invariants.is_empty(),
        "named-instance action subscript should not create eval-state invariants"
    );
    assert!(
        result
            .promoted_invariant_properties
            .contains(&"Refines".to_string()),
        "fully handled named-instance Spec should stay off the liveness queue"
    );
    assert!(
        result
            .promoted_action_properties
            .contains(&"Refines".to_string()),
        "fully handled named-instance Spec should remain marked as promoted action safety"
    );
}
