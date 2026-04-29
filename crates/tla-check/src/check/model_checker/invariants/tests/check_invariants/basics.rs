// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Baseline pass/fail/error semantics for `check_invariants_array`.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_invariants_all_pass() {
    let module = parse_module(
        r#"
---- MODULE InvPass ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Safety == x >= 0
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
    let state = State::from_pairs([("x", Value::int(0))]);
    // Part of #2484 Phase 3: use ArrayState path
    let registry = mc.ctx.var_registry().clone();
    let arr = ArrayState::from_state(&state, &registry);
    let result = mc.check_invariants_array(&arr);
    assert_eq!(result.unwrap(), None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_invariants_clears_stale_action_scope() {
    let module = parse_module(
        r#"
---- MODULE InvActionScope ----
EXTENDS TLC
VARIABLE x
Init == x = 0
Next == x' = x + 1
ActionEmpty == TLCGet("action").name = ""
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["ActionEmpty".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    let current = State::from_pairs([("x", Value::int(0))]);
    let next = State::from_pairs([("x", Value::int(1))]);
    let registry = mc.ctx.var_registry().clone();
    let current_arr = ArrayState::from_state(&current, &registry);
    let next_arr = ArrayState::from_state(&next, &registry);

    let _stale_next_guard = mc.ctx.bind_next_state_env_guard(next_arr.env_ref());

    let result = mc.check_invariants_array(&current_arr);
    assert_eq!(
        result.unwrap(),
        None,
        "state invariants must clear stale action scope before evaluating TLCGet(\"action\")"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_invariants_violation() {
    let module = parse_module(
        r#"
---- MODULE InvFail ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Positive == x > 0
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Positive".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    // x = 0 violates Positive (x > 0)
    let state = State::from_pairs([("x", Value::int(0))]);
    // Part of #2484 Phase 3: use ArrayState path
    let registry = mc.ctx.var_registry().clone();
    let arr = ArrayState::from_state(&state, &registry);
    let result = mc.check_invariants_array(&arr).unwrap();
    assert_eq!(result, Some("Positive".to_string()));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_invariants_non_boolean_error() {
    let module = parse_module(
        r#"
---- MODULE InvNonBool ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
NotBool == x + 1
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["NotBool".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    let state = State::from_pairs([("x", Value::int(0))]);
    // Part of #2484 Phase 3: use ArrayState path
    let registry = mc.ctx.var_registry().clone();
    let arr = ArrayState::from_state(&state, &registry);
    let result = mc.check_invariants_array(&arr);
    assert!(matches!(
        result,
        Err(CheckError::Eval(EvalCheckError::InvariantNotBoolean(ref name))) if name == "NotBool"
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_invariants_empty_invariants_passes() {
    let module = parse_module(
        r#"
---- MODULE InvEmpty ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    let state = State::from_pairs([("x", Value::int(0))]);
    // Part of #2484 Phase 3: use ArrayState path
    let registry = mc.ctx.var_registry().clone();
    let arr = ArrayState::from_state(&state, &registry);
    let result = mc.check_invariants_array(&arr);
    assert_eq!(result.unwrap(), None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_invariants_first_fail_stops() {
    // When multiple invariants are configured, check stops at the first failure
    let module = parse_module(
        r#"
---- MODULE InvMulti ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
AlwaysFalse == FALSE
AlsoFalse == FALSE
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["AlwaysFalse".to_string(), "AlsoFalse".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    let state = State::from_pairs([("x", Value::int(0))]);
    // Part of #2484 Phase 3: use ArrayState path
    let registry = mc.ctx.var_registry().clone();
    let arr = ArrayState::from_state(&state, &registry);
    let result = mc.check_invariants_array(&arr).unwrap();
    // Should report the first failing invariant
    assert_eq!(result, Some("AlwaysFalse".to_string()));
}

/// Test that cooperative invariant skip (full) causes `check_successor_invariant`
/// to return `Ok` even when an invariant is violated.
///
/// Part of #3810: verifies the full-skip path — when PDR proves ALL invariants,
/// the BFS lane skips per-state invariant evaluation entirely.
#[cfg(feature = "z4")]
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cooperative_full_invariant_skip_returns_ok() {
    use crate::checker_ops::InvariantOutcome;
    use crate::cooperative_state::SharedCooperativeState;
    use std::sync::Arc;

    let module = parse_module(
        r#"
---- MODULE CoopFullSkip ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
AlwaysFalse == FALSE
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["AlwaysFalse".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);

    // Without cooperative state, checking should report a violation.
    let registry = mc.ctx.var_registry().clone();
    let state = State::from_pairs([("x", Value::int(0))]);
    let arr = ArrayState::from_state(&state, &registry);
    let fp = Fingerprint(42);

    let outcome_before = mc.check_successor_invariant(Fingerprint(1), &arr, fp, 1);
    assert!(
        matches!(outcome_before, InvariantOutcome::Violation { ref invariant, .. } if invariant == "AlwaysFalse"),
        "without cooperative state, AlwaysFalse should be violated"
    );

    // Set cooperative state and mark all invariants proved.
    let coop = Arc::new(SharedCooperativeState::with_invariant_count(0, 1));
    coop.set_invariants_proved();
    mc.set_cooperative_state(coop);

    // Now check_successor_invariant should skip and return Ok.
    let outcome_after = mc.check_successor_invariant(Fingerprint(1), &arr, fp, 1);
    assert!(
        matches!(outcome_after, InvariantOutcome::Ok),
        "with all invariants proved by PDR, should skip and return Ok"
    );
}

/// Test that cooperative partial invariant skip only checks unproved invariants.
///
/// Part of #3810: verifies the partial-skip path — when PDR proves some
/// invariants, BFS only evaluates the unproved ones per-state.
#[cfg(feature = "z4")]
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cooperative_partial_invariant_skip_checks_only_unproved() {
    use crate::checker_ops::InvariantOutcome;
    use crate::cooperative_state::SharedCooperativeState;
    use std::sync::Arc;

    let module = parse_module(
        r#"
---- MODULE CoopPartialSkip ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
AlwaysFalse == FALSE
AlwaysTrue == TRUE
====
"#,
    );
    // Config with two invariants: AlwaysFalse (index 0) and AlwaysTrue (index 1).
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["AlwaysFalse".to_string(), "AlwaysTrue".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);

    let registry = mc.ctx.var_registry().clone();
    let state = State::from_pairs([("x", Value::int(0))]);
    let arr = ArrayState::from_state(&state, &registry);
    let fp = Fingerprint(42);

    // Without cooperative state, checking should report AlwaysFalse violation.
    let outcome_no_coop = mc.check_successor_invariant(Fingerprint(1), &arr, fp, 1);
    assert!(
        matches!(outcome_no_coop, InvariantOutcome::Violation { ref invariant, .. } if invariant == "AlwaysFalse"),
        "without cooperative, AlwaysFalse should be violated"
    );

    // Set cooperative state: mark invariant 0 (AlwaysFalse) as proved by PDR.
    // Only invariant 1 (AlwaysTrue) should be checked.
    let coop = Arc::new(SharedCooperativeState::with_invariant_count(0, 2));
    coop.mark_invariant_proved(0); // Prove AlwaysFalse
    assert!(coop.has_partial_proofs(), "should have partial proofs");
    mc.set_cooperative_state(coop);

    // Now check_successor_invariant should only check AlwaysTrue (which passes).
    let outcome_partial = mc.check_successor_invariant(Fingerprint(1), &arr, fp, 1);
    assert!(
        matches!(outcome_partial, InvariantOutcome::Ok),
        "with AlwaysFalse proved by PDR, only AlwaysTrue is checked and passes"
    );
}

/// Test that cooperative partial skip still detects violations in unproved invariants.
///
/// Part of #3810: when PDR proves one invariant but another (unproved) one is
/// violated, the violation must still be detected.
#[cfg(feature = "z4")]
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cooperative_partial_skip_detects_unproved_violation() {
    use crate::checker_ops::InvariantOutcome;
    use crate::cooperative_state::SharedCooperativeState;
    use std::sync::Arc;

    let module = parse_module(
        r#"
---- MODULE CoopPartialViolation ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
AlwaysTrue == TRUE
AlwaysFalse == FALSE
====
"#,
    );
    // Config: AlwaysTrue (index 0), AlwaysFalse (index 1).
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["AlwaysTrue".to_string(), "AlwaysFalse".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);

    let registry = mc.ctx.var_registry().clone();
    let state = State::from_pairs([("x", Value::int(0))]);
    let arr = ArrayState::from_state(&state, &registry);
    let fp = Fingerprint(42);

    // Prove AlwaysTrue (index 0), leave AlwaysFalse (index 1) unproved.
    let coop = Arc::new(SharedCooperativeState::with_invariant_count(0, 2));
    coop.mark_invariant_proved(0); // Prove AlwaysTrue
    mc.set_cooperative_state(coop);

    // AlwaysFalse is still unproved and violated — should be detected.
    let outcome = mc.check_successor_invariant(Fingerprint(1), &arr, fp, 1);
    assert!(
        matches!(outcome, InvariantOutcome::Violation { ref invariant, .. } if invariant == "AlwaysFalse"),
        "unproved AlwaysFalse should still be detected as violated"
    );
}
