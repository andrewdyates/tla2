// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_array_fast_no_state_change_required() {
    use crate::liveness::checker::ea_precompute_enabled::EnabledInfo;

    // Setup: action = TRUE (always enabled), no state change required.
    // With cached_succs containing one successor, ENABLED should be true.
    let action = Arc::new(spanned(Expr::Bool(true)));
    let info = EnabledInfo {
        action,
        bindings: None,
        require_state_change: false,
        subscript: None,
        tag: 1,
    };

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s0_fp = s0.fingerprint();

    let cached_succs = vec![s1.clone()];
    let succ_envs = vec![build_env_from_state(&s1)];

    let mut ctx = crate::eval::EvalCtx::new();
    ctx.register_vars(["x".to_string()]);
    let registry = ctx.var_registry().clone();
    let from_values = s0.to_values(&registry);
    let _guard = ctx.bind_state_array_guard(&from_values);

    let result = LivenessChecker::eval_enabled_array_fast(
        &mut ctx,
        &info,
        &s0,
        s0_fp,
        &cached_succs,
        &succ_envs,
        &registry,
    );
    assert!(result.unwrap(), "action=TRUE should be enabled");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_array_fast_no_successors_returns_false() {
    use crate::liveness::checker::ea_precompute_enabled::EnabledInfo;

    // No cached successors → ENABLED is false (no successor satisfies action).
    let action = Arc::new(spanned(Expr::Bool(true)));
    let info = EnabledInfo {
        action,
        bindings: None,
        require_state_change: false,
        subscript: None,
        tag: 2,
    };

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s0_fp = s0.fingerprint();
    let cached_succs: Vec<State> = vec![];
    let succ_envs: Vec<Arc<crate::eval::Env>> = vec![];

    let mut ctx = crate::eval::EvalCtx::new();
    ctx.register_vars(["x".to_string()]);
    let registry = ctx.var_registry().clone();
    let from_values = s0.to_values(&registry);
    let _guard = ctx.bind_state_array_guard(&from_values);

    let result = LivenessChecker::eval_enabled_array_fast(
        &mut ctx,
        &info,
        &s0,
        s0_fp,
        &cached_succs,
        &succ_envs,
        &registry,
    );
    assert!(!result.unwrap(), "no successors → not enabled");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_array_fast_stuttering_detection_fp_equality() {
    use crate::liveness::checker::ea_precompute_enabled::EnabledInfo;

    // require_state_change=true, no subscript → uses fingerprint equality.
    // Successor with same fp as from_state should be skipped (stuttering).
    let action = Arc::new(spanned(Expr::Bool(true)));
    let info = EnabledInfo {
        action,
        bindings: None,
        require_state_change: true,
        subscript: None, // triggers succ_fp == from_fp path
        tag: 3,
    };

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s0_fp = s0.fingerprint();
    // Only successor is a copy of s0 (same fingerprint) → stuttering
    let cached_succs = vec![s0.clone()];
    let succ_envs = vec![build_env_from_state(&s0)];

    let mut ctx = crate::eval::EvalCtx::new();
    ctx.register_vars(["x".to_string()]);
    let registry = ctx.var_registry().clone();
    let from_values = s0.to_values(&registry);
    let _guard = ctx.bind_state_array_guard(&from_values);

    let result = LivenessChecker::eval_enabled_array_fast(
        &mut ctx,
        &info,
        &s0,
        s0_fp,
        &cached_succs,
        &succ_envs,
        &registry,
    );
    assert!(
        !result.unwrap(),
        "stuttering successor (same fp) should be skipped, no other successors → false"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_array_fast_action_false_returns_not_enabled() {
    use crate::liveness::checker::ea_precompute_enabled::EnabledInfo;

    // Action evaluates to FALSE → not enabled even with a valid successor.
    let action = Arc::new(spanned(Expr::Bool(false)));
    let info = EnabledInfo {
        action,
        bindings: None,
        require_state_change: false,
        subscript: None,
        tag: 4,
    };

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s0_fp = s0.fingerprint();

    let cached_succs = vec![s1.clone()];
    let succ_envs = vec![build_env_from_state(&s1)];

    let mut ctx = crate::eval::EvalCtx::new();
    ctx.register_vars(["x".to_string()]);
    let registry = ctx.var_registry().clone();
    let from_values = s0.to_values(&registry);
    let _guard = ctx.bind_state_array_guard(&from_values);

    let result = LivenessChecker::eval_enabled_array_fast(
        &mut ctx,
        &info,
        &s0,
        s0_fp,
        &cached_succs,
        &succ_envs,
        &registry,
    );
    assert!(!result.unwrap(), "action=FALSE → not enabled");
}
