// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Part of #3100: Tests for ENABLED-based action skip (WF disjunction short-circuit).

use super::*;

/// Test that `extract_enabled_action_group` finds the ENABLED-to-action tag mapping
/// from a WF expansion and that `prepare_inline_fairness_cache` stores the groups.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn enabled_action_groups_extracted_from_wf() {
    let module = parse_module(INLINE_FAIRNESS_SPEC);
    let config = inline_fairness_config();

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    apply_weak_fairness(&mut checker);

    checker.prepare_inline_fairness_cache();

    assert_eq!(
        checker.liveness_cache.enabled_action_groups.len(),
        1,
        "WF_x(Next) should produce one enabled-action group"
    );

    let group = &checker.liveness_cache.enabled_action_groups[0];

    // The ENABLED tag should match the one in fairness_state_checks.
    let enabled_tag = find_tag(
        &checker.liveness_cache.fairness_state_checks,
        |expr| match expr {
            LiveExpr::Enabled { tag, .. } => Some(*tag),
            _ => None,
        },
    );
    assert_eq!(
        group.enabled_tag, enabled_tag,
        "enabled_action_group.enabled_tag should match the ENABLED leaf tag"
    );

    // The action tags should cover both ActionPred and StateChanged.
    assert_eq!(
        group.action_tags.len(),
        2,
        "WF_x(Next) group should have 2 action tags (ActionPred + StateChanged)"
    );
    let action_tag = find_tag(
        &checker.liveness_cache.fairness_action_checks,
        |expr| match expr {
            LiveExpr::ActionPred { tag, .. } => Some(*tag),
            _ => None,
        },
    );
    let changed_tag = find_tag(
        &checker.liveness_cache.fairness_action_checks,
        |expr| match expr {
            LiveExpr::StateChanged { tag, .. } => Some(*tag),
            _ => None,
        },
    );
    assert!(
        group.action_tags.contains(&action_tag),
        "group should contain the ActionPred tag"
    );
    assert!(
        group.action_tags.contains(&changed_tag),
        "group should contain the StateChanged tag"
    );
}

const DISABLED_ACTION_SPEC: &str = r#"
---- MODULE DisabledAction ----
EXTENDS Integers
VARIABLE x, y
Init == x = 0 /\ y = 0
Inc == x' = x + 1 /\ y' = y
Dec == x > 0 /\ x' = x - 1 /\ y' = y
Prop == []<>(x = 0)
====
"#;

/// Test that the ENABLED-based skip pre-populates action results as false
/// when ENABLED is false for a state. In this spec, Dec is only enabled when x > 0,
/// so at x=0 the action skip should pre-populate Dec's action tags.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn enabled_skip_prepopulates_false_when_action_disabled() {
    let module = parse_module(DISABLED_ACTION_SPEC);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Inc".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);

    // Apply WF on Dec — Dec is NOT enabled at x=0.
    checker.set_fairness(vec![FairnessConstraint::Weak {
        vars: "<<x, y>>".to_string(),
        action: "Dec".to_string(),
        action_node: None,
    }]);

    checker.prepare_inline_fairness_cache();

    // Verify we have an enabled-action group.
    assert_eq!(
        checker.liveness_cache.enabled_action_groups.len(),
        1,
        "WF should produce one enabled-action group"
    );

    let registry = checker.ctx.var_registry().clone();
    let current = State::from_pairs([("x", Value::int(0)), ("y", Value::int(0))]);
    let next = State::from_pairs([("x", Value::int(1)), ("y", Value::int(0))]);
    let current_arr = ArrayState::from_state(&current, &registry);
    let next_arr = ArrayState::from_state(&next, &registry);
    let current_fp = current.fingerprint();
    let next_fp = next.fingerprint();

    // Record inline fairness results — ENABLED(Dec) should be false at x=0.
    checker
        .record_inline_fairness_results(current_fp, &current_arr, &[(next_arr, next_fp)])
        .expect("inline fairness recording should succeed");

    // Verify ENABLED(Dec) is false via bitmask.
    let enabled_tag = checker.liveness_cache.enabled_action_groups[0].enabled_tag;
    let state_bits = checker
        .liveness_cache
        .inline_state_bitmasks
        .get(&current_fp)
        .expect("state bitmask should exist for current_fp");
    assert!(
        (state_bits & (1u64 << enabled_tag) == 0),
        "ENABLED(<<Dec>>_<<x,y>>) should be false at x=0"
    );

    // Verify the action tags were pre-populated as false by the ENABLED skip.
    let action_bits = checker
        .liveness_cache
        .inline_action_bitmasks
        .get(&(current_fp, next_fp))
        .expect("action bitmask should exist for (current_fp, next_fp)");
    for &action_tag in &checker.liveness_cache.enabled_action_groups[0].action_tags {
        assert!(
            (action_bits & (1u64 << action_tag) == 0),
            "action tag {} should be false when ENABLED is false (enabled-skip)",
            action_tag,
        );
    }
}
