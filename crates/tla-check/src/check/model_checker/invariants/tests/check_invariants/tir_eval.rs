// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TIR/promoted-property routing coverage for `check_invariants_array`.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_invariants_initial_state_tir_eval_keeps_eval_only_promoted_property() {
    let module = parse_module(
        r#"
---- MODULE InitEnabledProperty3401 ----
VARIABLE x
Init == x = 0
Next == FALSE
AlwaysEnabled == []ENABLED Next
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["AlwaysEnabled".to_string()],
        check_deadlock: false,
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    let classification = crate::checker_ops::classify_property_safety_parts(
        &mc.ctx,
        &mc.config.properties,
        &mc.module.op_defs,
    );
    assert_eq!(
        classification.eval_state_invariants.len(),
        1,
        "[]ENABLED Next should produce exactly one eval-based state invariant"
    );
    mc.compiled.eval_state_invariants = classification.eval_state_invariants;
    mc.compiled.promoted_property_invariants = classification.promoted_invariant_properties;
    mc.tir_parity = Some(
        super::super::super::super::tir_parity::TirParityState::test_eval_selected(
            module.clone(),
            Vec::new(),
            ["AlwaysEnabled"],
        ),
    );
    crate::eval::set_enabled_hook(crate::enabled::eval_enabled_cp);

    let state = State::from_pairs([("x", Value::int(0))]);
    let registry = mc.ctx.var_registry().clone();
    let arr = ArrayState::from_state(&state, &registry);

    let result = mc.check_invariants_array(&arr).unwrap();
    assert_eq!(
        result,
        Some("AlwaysEnabled".to_string()),
        "initial-state TIR invariant evaluation must include eval-only promoted PROPERTY terms"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_invariants_tir_eval_keeps_binding_form_invariant_on_ast_guard_path() {
    let module = parse_module(
        r#"
---- MODULE InvBindingFallback3288 ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Safety == [i \in {0, 1} |-> i][x] = x
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    mc.tir_parity = Some(
        super::super::super::super::tir_parity::TirParityState::test_eval_selected(
            module.clone(),
            Vec::new(),
            ["Safety"],
        ),
    );

    let state = State::from_pairs([("x", Value::int(0))]);
    let registry = mc.ctx.var_registry().clone();
    let arr = ArrayState::from_state(&state, &registry);

    let result = mc.check_invariants_array(&arr).unwrap();
    assert_eq!(
        result, None,
        "binding-form invariants selected for TIR should still pass via the AST/guard path"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_invariants_tir_eval_keeps_promoted_property_compiled_guards() {
    let module = parse_module(
        r#"
---- MODULE InvProperty3401 ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
TypeOK == x \in 0..2
Safe == x <= 1
AlwaysSafe == []Safe
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        properties: vec!["AlwaysSafe".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    prepare_invariants_with_promoted_property(&mut mc);
    mc.tir_parity = Some(
        super::super::super::super::tir_parity::TirParityState::test_eval_selected(
            module.clone(),
            Vec::new(),
            ["TypeOK", "AlwaysSafe"],
        ),
    );

    let state = State::from_pairs([("x", Value::int(2))]);
    let registry = mc.ctx.var_registry().clone();
    let arr = ArrayState::from_state(&state, &registry);

    // "AlwaysSafe" violation should still be detected via the eval path.
    let result = mc.check_invariants_array(&arr).unwrap();
    assert_eq!(
        result,
        Some("AlwaysSafe".to_string()),
        "TIR invariant eval must detect promoted PROPERTY violations via the eval path"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_successor_invariant_tir_eval_keeps_promoted_property_eval_path() {
    let module = parse_module(
        r#"
---- MODULE SuccProperty3401 ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
TypeOK == x \in 0..2
Safe == x <= 1
AlwaysSafe == []Safe
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        properties: vec!["AlwaysSafe".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    prepare_invariants_with_promoted_property(&mut mc);
    mc.tir_parity = Some(
        super::super::super::super::tir_parity::TirParityState::test_eval_selected(
            module.clone(),
            Vec::new(),
            ["TypeOK", "AlwaysSafe"],
        ),
    );

    let state = State::from_pairs([("x", Value::int(2))]);
    let registry = mc.ctx.var_registry().clone();
    let arr = ArrayState::from_state(&state, &registry);

    let outcome = mc.check_successor_invariant(Fingerprint(0), &arr, Fingerprint(1), 1);
    assert!(
        matches!(
            outcome,
            crate::checker_ops::InvariantOutcome::Violation {
                invariant,
                state_fp
            } if invariant == "AlwaysSafe" && state_fp == Fingerprint(1)
        ),
        "successor TIR invariant eval must detect promoted PROPERTY violations via the eval path"
    );
}
