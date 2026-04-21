// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! eval_enabled_cached tests — cache hit, miss, bypass
//!
//! Split from liveness/checker/tests.rs — Part of #2779

use crate::Value;

/// Test `eval_enabled_cached` with a populated VarRegistry — second call
/// should return cached result without invoking the evaluator.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_cached_returns_cached_on_second_call() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    crate::liveness::clear_enabled_cache();

    let mut ctx = crate::eval::EvalCtx::new();
    ctx.register_vars(["x"].iter().map(|s| (*s).to_string()));

    let fp = crate::state::State::from_pairs([("x", Value::int(0))]).fingerprint();
    let tag = 42u32;

    let call_count = AtomicUsize::new(0);

    // First call: evaluator should execute, returns true.
    let result1 = crate::liveness::checker::eval_enabled_cached(&ctx, fp, tag, || {
        call_count.fetch_add(1, Ordering::SeqCst);
        Ok(true)
    })
    .expect("eval_enabled_cached should succeed");
    assert!(result1, "first call should return evaluator result (true)");
    assert_eq!(
        call_count.load(Ordering::SeqCst),
        1,
        "evaluator should be called once"
    );

    // Second call: cache hit — evaluator should NOT execute.
    let result2 = crate::liveness::checker::eval_enabled_cached(&ctx, fp, tag, || {
        call_count.fetch_add(1, Ordering::SeqCst);
        Ok(false) // different value — proves cache is used
    })
    .expect("eval_enabled_cached should succeed on cache hit");
    assert!(
        result2,
        "second call should return cached value (true), not evaluator value (false)"
    );
    assert_eq!(
        call_count.load(Ordering::SeqCst),
        1,
        "evaluator should NOT be called on cache hit"
    );
}

/// Test `eval_enabled_cached` with different tags — each tag should have
/// an independent cache entry.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_cached_different_tag_misses_cache() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    crate::liveness::clear_enabled_cache();

    let mut ctx = crate::eval::EvalCtx::new();
    ctx.register_vars(["x"].iter().map(|s| (*s).to_string()));

    let fp = crate::state::State::from_pairs([("x", Value::int(0))]).fingerprint();
    let call_count = AtomicUsize::new(0);

    // Tag 1: cache true.
    let _ = crate::liveness::checker::eval_enabled_cached(&ctx, fp, 1, || {
        call_count.fetch_add(1, Ordering::SeqCst);
        Ok(true)
    })
    .unwrap();
    assert_eq!(call_count.load(Ordering::SeqCst), 1);

    // Tag 2: cache miss — evaluator should execute (different tag).
    let result = crate::liveness::checker::eval_enabled_cached(&ctx, fp, 2, || {
        call_count.fetch_add(1, Ordering::SeqCst);
        Ok(false)
    })
    .unwrap();
    assert!(
        !result,
        "different tag should miss cache and return evaluator result (false)"
    );
    assert_eq!(
        call_count.load(Ordering::SeqCst),
        2,
        "evaluator should be called for each unique tag"
    );

    // Tag 1 again: cache hit.
    let result = crate::liveness::checker::eval_enabled_cached(&ctx, fp, 1, || {
        call_count.fetch_add(1, Ordering::SeqCst);
        Ok(false) // should be ignored
    })
    .unwrap();
    assert!(result, "tag 1 should still return cached true");
    assert_eq!(
        call_count.load(Ordering::SeqCst),
        2,
        "no new evaluator call for cached tag"
    );
}

/// Test `eval_enabled_cached` with empty VarRegistry — caching should be
/// bypassed and the evaluator should be invoked every time.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_cached_empty_registry_bypasses_cache() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    crate::liveness::clear_enabled_cache();

    let ctx = crate::eval::EvalCtx::new(); // empty VarRegistry

    let fp = crate::state::State::from_pairs([("x", Value::int(0))]).fingerprint();
    let tag = 99u32;
    let call_count = AtomicUsize::new(0);

    // First call: evaluator should execute.
    let result1 = crate::liveness::checker::eval_enabled_cached(&ctx, fp, tag, || {
        call_count.fetch_add(1, Ordering::SeqCst);
        Ok(true)
    })
    .unwrap();
    assert!(result1);
    assert_eq!(call_count.load(Ordering::SeqCst), 1);

    // Second call: evaluator should ALSO execute (no caching for empty registry).
    let result2 = crate::liveness::checker::eval_enabled_cached(&ctx, fp, tag, || {
        call_count.fetch_add(1, Ordering::SeqCst);
        Ok(false)
    })
    .unwrap();
    assert!(
        !result2,
        "empty registry should bypass cache, returning fresh evaluator result"
    );
    assert_eq!(
        call_count.load(Ordering::SeqCst),
        2,
        "evaluator should be called both times (no caching)"
    );
}
