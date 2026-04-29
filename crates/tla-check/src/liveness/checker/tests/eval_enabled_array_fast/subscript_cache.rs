// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_array_fast_subscript_cache_hit_unchanged() {
    use crate::liveness::checker::ea_precompute_enabled::EnabledInfo;

    // require_state_change=true, with subscript → checks subscript cache.
    // Pre-populate cache so check_subscript_changed_cached returns Some(false).
    let action = Arc::new(spanned(Expr::Bool(true)));
    let subscript = Arc::new(spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    )));
    let tag = 10;
    let info = EnabledInfo {
        action,
        bindings: None,
        require_state_change: true,
        subscript: Some(subscript),
        tag,
    };

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s0_fp = s0.fingerprint();
    let s1_fp = s1.fingerprint();

    // Pre-populate subscript cache: both s0 and s1 have the SAME subscript value
    // → check_subscript_changed_cached returns Some(false) → skip this successor
    crate::liveness::checker::subscript_cache::clear_subscript_value_cache();
    crate::liveness::checker::subscript_cache::set_subscript_value_cache(
        s0_fp,
        tag,
        Value::int(42),
    );
    crate::liveness::checker::subscript_cache::set_subscript_value_cache(
        s1_fp,
        tag,
        Value::int(42),
    );

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
    assert!(
        !result.unwrap(),
        "subscript unchanged (cache hit) → successor skipped → false"
    );

    // Cleanup
    crate::liveness::checker::subscript_cache::clear_subscript_value_cache();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_array_fast_subscript_cache_hit_changed() {
    use crate::liveness::checker::ea_precompute_enabled::EnabledInfo;

    // Same setup but subscript values DIFFER → check_subscript_changed_cached
    // returns Some(true) → don't skip, evaluate action (TRUE) → enabled.
    let action = Arc::new(spanned(Expr::Bool(true)));
    let subscript = Arc::new(spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    )));
    let tag = 11;
    let info = EnabledInfo {
        action,
        bindings: None,
        require_state_change: true,
        subscript: Some(subscript),
        tag,
    };

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s0_fp = s0.fingerprint();
    let s1_fp = s1.fingerprint();

    // Pre-populate: different subscript values → changed → proceed with eval
    crate::liveness::checker::subscript_cache::clear_subscript_value_cache();
    crate::liveness::checker::subscript_cache::set_subscript_value_cache(
        s0_fp,
        tag,
        Value::int(100),
    );
    crate::liveness::checker::subscript_cache::set_subscript_value_cache(
        s1_fp,
        tag,
        Value::int(200),
    );

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
    assert!(
        result.unwrap(),
        "subscript changed (cache hit) + action=TRUE → enabled"
    );

    // Cleanup
    crate::liveness::checker::subscript_cache::clear_subscript_value_cache();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_array_fast_subscript_cache_miss_fallback_unchanged() {
    use crate::liveness::checker::ea_precompute_enabled::EnabledInfo;

    // require_state_change=true, with subscript, but subscript cache is EMPTY
    // → check_subscript_changed_cached returns None → falls back to
    // eval_enabled_fallback which does full subscript evaluation.
    //
    // Use Expr::Bool(true) as subscript: evaluates identically in both states
    // → subscript "unchanged" → successor skipped → result false.
    let action = Arc::new(spanned(Expr::Bool(true)));
    let subscript = Arc::new(spanned(Expr::Bool(true)));
    let tag = 20;
    let info = EnabledInfo {
        action,
        bindings: None,
        require_state_change: true,
        subscript: Some(subscript),
        tag,
    };

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s0_fp = s0.fingerprint();

    // Ensure subscript cache is empty → cache miss → fallback
    crate::liveness::checker::subscript_cache::clear_subscript_value_cache();

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
    // Fallback evaluates subscript (Bool(true)) in both states → same value
    // → subscript unchanged → successor skipped → false
    assert!(
        !result.unwrap(),
        "cache miss → fallback → subscript unchanged (constant) → not enabled"
    );

    crate::liveness::checker::subscript_cache::clear_subscript_value_cache();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_array_fast_subscript_cache_miss_fallback_changed() {
    use crate::liveness::checker::ea_precompute_enabled::EnabledInfo;

    // Cache miss with variable-dependent subscript. The fallback closure
    // builds explicit envs from each state's variables, so Ident("x")
    // resolves to 0 in s0 and 1 in s1 → subscript changed → action=TRUE
    // → enabled.
    let action = Arc::new(spanned(Expr::Bool(true)));
    let subscript = Arc::new(spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    )));
    let tag = 21;
    let info = EnabledInfo {
        action,
        bindings: None,
        require_state_change: true,
        subscript: Some(subscript),
        tag,
    };

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s0_fp = s0.fingerprint();

    // Ensure subscript cache is empty → cache miss → fallback
    crate::liveness::checker::subscript_cache::clear_subscript_value_cache();

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
    // Fallback evaluates subscript Ident("x") in s0 env (x=0) and s1 env (x=1)
    // → different values → subscript changed → action=TRUE → enabled
    assert!(
        result.unwrap(),
        "cache miss → fallback → subscript changed (x:0→1) + action=TRUE → enabled"
    );

    crate::liveness::checker::subscript_cache::clear_subscript_value_cache();
}
