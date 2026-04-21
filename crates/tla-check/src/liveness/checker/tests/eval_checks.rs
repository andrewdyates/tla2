// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! eval_check_on_state, eval_check_on_transition, eval_action_checks_batched
//!
//! Split from liveness/checker/tests.rs — Part of #2779

use super::*;
use crate::liveness::checker::check_mask::CheckMask;
use crate::liveness::test_helpers::{make_checker, make_checker_with_vars, spanned};
use crate::liveness::LiveExpr;
use crate::Value;
use std::sync::Arc;
use tla_core::ast::Expr;

// ============================================================================
// Direct unit tests for eval_check_on_state / eval_check_on_transition (#2497 items 6, 7)
// ============================================================================

/// Test `eval_check_on_state` directly with a StatePred LiveExpr.
///
/// Constructs a state predicate `x > 0` and evaluates against states with
/// positive and non-positive x values.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_check_on_state_state_pred_true_and_false() {
    let gt_zero = LiveExpr::StatePred {
        expr: Arc::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(0.into()))),
        ))),
        bindings: None,
        tag: 100,
    };

    let s_positive = State::from_pairs([("x", Value::int(5))]);
    let s_zero = State::from_pairs([("x", Value::int(0))]);
    let s_negative = State::from_pairs([("x", Value::int(-1))]);

    let mut checker = make_checker(LiveExpr::Bool(true));

    assert!(
        checker
            .eval_check_on_state(&gt_zero, &s_positive)
            .expect("eval should succeed for x=5"),
        "x=5 > 0 should be true"
    );
    assert!(
        !checker
            .eval_check_on_state(&gt_zero, &s_zero)
            .expect("eval should succeed for x=0"),
        "x=0 > 0 should be false"
    );
    assert!(
        !checker
            .eval_check_on_state(&gt_zero, &s_negative)
            .expect("eval should succeed for x=-1"),
        "x=-1 > 0 should be false"
    );
}

/// Test `eval_check_on_state` with boolean combinators (And, Or, Not).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_check_on_state_boolean_combinators() {
    let mut checker = make_checker(LiveExpr::Bool(true));
    let s = State::from_pairs([("x", Value::int(3))]);

    // Bool literal
    assert!(checker
        .eval_check_on_state(&LiveExpr::Bool(true), &s)
        .unwrap());
    assert!(!checker
        .eval_check_on_state(&LiveExpr::Bool(false), &s)
        .unwrap());

    // Not
    let not_true = LiveExpr::Not(Box::new(LiveExpr::Bool(true)));
    assert!(!checker.eval_check_on_state(&not_true, &s).unwrap());

    // And: true /\ false => false
    let and_expr = LiveExpr::And(vec![LiveExpr::Bool(true), LiveExpr::Bool(false)]);
    assert!(!checker.eval_check_on_state(&and_expr, &s).unwrap());

    // And: true /\ true => true
    let and_true = LiveExpr::And(vec![LiveExpr::Bool(true), LiveExpr::Bool(true)]);
    assert!(checker.eval_check_on_state(&and_true, &s).unwrap());

    // Or: false \/ true => true
    let or_expr = LiveExpr::Or(vec![LiveExpr::Bool(false), LiveExpr::Bool(true)]);
    assert!(checker.eval_check_on_state(&or_expr, &s).unwrap());

    // Or: false \/ false => false
    let or_false = LiveExpr::Or(vec![LiveExpr::Bool(false), LiveExpr::Bool(false)]);
    assert!(!checker.eval_check_on_state(&or_false, &s).unwrap());
}

/// Test `eval_check_on_transition` directly with a StateChanged LiveExpr.
///
/// When the subscript value differs between current and next state, the
/// check should return true; when unchanged, false.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_check_on_transition_state_changed() {
    crate::eval::clear_for_test_reset();

    let subscript_expr = Arc::new(spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    )));
    let changed = LiveExpr::StateChanged {
        subscript: Some(subscript_expr),
        bindings: None,
        tag: 200,
    };

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s0_dup = State::from_pairs([("x", Value::int(0))]);

    let mut checker = make_checker(LiveExpr::Bool(true));

    // Different states: x changes from 0 to 1
    let result = checker
        .eval_check_on_transition(&changed, &s0, &s1)
        .expect("eval should succeed for changed transition");
    assert!(result, "x changed from 0 to 1, StateChanged should be true");

    // Same state: x stays at 0
    crate::eval::clear_for_test_reset();
    let result = checker
        .eval_check_on_transition(&changed, &s0, &s0_dup)
        .expect("eval should succeed for unchanged transition");
    assert!(
        !result,
        "x is 0 in both states, StateChanged should be false"
    );
}

/// Test `eval_action_checks_batched` with multiple checks in a single batch.
///
/// Sets up two state predicates as action-level checks and verifies the
/// bitmask correctly encodes which checks pass for a given transition.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_action_checks_batched_multi_check() {
    crate::eval::clear_for_test_reset();

    // Check 0: x changed (subscript = x)
    let changed_x = LiveExpr::StateChanged {
        subscript: Some(Arc::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))),
        bindings: None,
        tag: 300,
    };
    // Check 1: always true
    let always_true = LiveExpr::Bool(true);
    // Check 2: always false
    let always_false = LiveExpr::Bool(false);

    let checks = vec![changed_x, always_true, always_false];
    let used = vec![true, true, true];

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let mut checker = make_checker(LiveExpr::Bool(true));

    let mask = checker
        .eval_action_checks_batched(&checks, &used, &s0, &s1)
        .expect("batched eval should succeed");

    // Check 0: x changed → bit 0 set
    assert!(mask.get(0), "check 0 (x changed) should pass");
    // Check 1: always true → bit 1 set
    assert!(mask.get(1), "check 1 (always true) should pass");
    // Check 2: always false → bit 2 clear
    assert!(!mask.get(2), "check 2 (always false) should not pass");

    // Verify mask is exactly bits 0 and 1
    assert_eq!(
        mask,
        CheckMask::from_u64(0b011),
        "mask should be 0b011 (checks 0 and 1 pass)"
    );
}

/// Test `eval_action_checks_batched` respects the `used` filter.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_action_checks_batched_respects_used_filter() {
    crate::eval::clear_for_test_reset();

    let always_true = LiveExpr::Bool(true);
    let checks = vec![always_true.clone(), always_true.clone(), always_true];
    // Only check index 1 is marked used.
    let used = vec![false, true, false];

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let mut checker = make_checker(LiveExpr::Bool(true));

    let mask = checker
        .eval_action_checks_batched(&checks, &used, &s0, &s1)
        .expect("batched eval should succeed");

    // Only bit 1 should be set.
    assert_eq!(
        mask,
        CheckMask::from_u64(1u64 << 1),
        "only used check (index 1) should be in the mask"
    );
}

// ============================================================================
// Production-path tests (#2497 Prover audit: tests must exercise array-based
// binding via populated VarRegistry, not just the HashMap fallback path)
// ============================================================================

/// Production-path variant of `test_eval_check_on_state_state_pred_true_and_false`.
///
/// Uses `make_checker_with_vars` so VarRegistry is populated, exercising the
/// array-based `bind_state_array_guard` path in `eval_live_check_expr` (lines 162-194)
/// rather than the HashMap fallback (lines 195-218).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_check_on_state_production_path() {
    let gt_zero = LiveExpr::StatePred {
        expr: Arc::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(0.into()))),
        ))),
        bindings: None,
        tag: 100,
    };

    let s_positive = State::from_pairs([("x", Value::int(5))]);
    let s_zero = State::from_pairs([("x", Value::int(0))]);
    let s_negative = State::from_pairs([("x", Value::int(-1))]);

    let mut checker = make_checker_with_vars(LiveExpr::Bool(true), &["x"]);

    assert!(
        checker
            .eval_check_on_state(&gt_zero, &s_positive)
            .expect("eval should succeed for x=5"),
        "x=5 > 0 should be true (production path)"
    );
    assert!(
        !checker
            .eval_check_on_state(&gt_zero, &s_zero)
            .expect("eval should succeed for x=0"),
        "x=0 > 0 should be false (production path)"
    );
    assert!(
        !checker
            .eval_check_on_state(&gt_zero, &s_negative)
            .expect("eval should succeed for x=-1"),
        "x=-1 > 0 should be false (production path)"
    );
}

/// Production-path variant of `test_eval_check_on_transition_state_changed`.
///
/// Uses `make_checker_with_vars` to exercise the array-based binding path in
/// `eval_live_check_expr` when evaluating StateChanged subscript comparisons.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_check_on_transition_production_path() {
    crate::eval::clear_for_test_reset();

    let subscript_expr = Arc::new(spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    )));
    let changed = LiveExpr::StateChanged {
        subscript: Some(subscript_expr),
        bindings: None,
        tag: 200,
    };

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s0_dup = State::from_pairs([("x", Value::int(0))]);

    let mut checker = make_checker_with_vars(LiveExpr::Bool(true), &["x"]);

    // Different states: x changes from 0 to 1
    let result = checker
        .eval_check_on_transition(&changed, &s0, &s1)
        .expect("eval should succeed for changed transition");
    assert!(
        result,
        "x changed from 0 to 1, StateChanged should be true (production path)"
    );

    // Same state: x stays at 0
    crate::eval::clear_for_test_reset();
    let result = checker
        .eval_check_on_transition(&changed, &s0, &s0_dup)
        .expect("eval should succeed for unchanged transition");
    assert!(
        !result,
        "x is 0 in both states, StateChanged should be false (production path)"
    );
}

/// Production-path variant of `test_eval_action_checks_batched_multi_check`.
///
/// Uses `make_checker_with_vars` to exercise the batched array-based binding
/// path in `eval_action_checks_batched` (lines 59-84) where state arrays are
/// bound ONCE for all checks, rather than the per-check fallback (lines 85-97).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_action_checks_batched_production_path() {
    crate::eval::clear_for_test_reset();

    // Check 0: x changed (subscript = x)
    let changed_x = LiveExpr::StateChanged {
        subscript: Some(Arc::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))),
        bindings: None,
        tag: 300,
    };
    // Check 1: always true
    let always_true = LiveExpr::Bool(true);
    // Check 2: always false
    let always_false = LiveExpr::Bool(false);

    let checks = vec![changed_x, always_true, always_false];
    let used = vec![true, true, true];

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let mut checker = make_checker_with_vars(LiveExpr::Bool(true), &["x"]);

    let mask = checker
        .eval_action_checks_batched(&checks, &used, &s0, &s1)
        .expect("batched eval should succeed (production path)");

    // Check 0: x changed → bit 0 set
    assert!(
        mask.get(0),
        "check 0 (x changed) should pass (production path)"
    );
    // Check 1: always true → bit 1 set
    assert!(
        mask.get(1),
        "check 1 (always true) should pass (production path)"
    );
    // Check 2: always false → bit 2 clear
    assert!(
        !mask.get(2),
        "check 2 (always false) should not pass (production path)"
    );

    assert_eq!(
        mask,
        CheckMask::from_u64(0b011),
        "mask should be 0b011 (checks 0 and 1 pass) (production path)"
    );
}

/// Production-path variant of `test_eval_action_checks_batched_respects_used_filter`.
///
/// Verifies the `used` filter works correctly when array-based binding is active.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_action_checks_batched_used_filter_production_path() {
    crate::eval::clear_for_test_reset();

    let always_true = LiveExpr::Bool(true);
    let checks = vec![always_true.clone(), always_true.clone(), always_true];
    // Only check index 1 is marked used.
    let used = vec![false, true, false];

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let mut checker = make_checker_with_vars(LiveExpr::Bool(true), &["x"]);

    let mask = checker
        .eval_action_checks_batched(&checks, &used, &s0, &s1)
        .expect("batched eval should succeed (production path)");

    assert_eq!(
        mask,
        CheckMask::from_u64(1u64 << 1),
        "only used check (index 1) should be in the mask (production path)"
    );
}
