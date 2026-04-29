// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Hoist generation invalidation guards and state-eval boundary contract tests.

use super::*;

// === API-level hoist generation guard tests (Part of #3407) ===
//
// Verify that state-binding RAII guards (NextStateEnvGuard, StateEnvGuard,
// ScopeGuard) automatically invalidate hoist cache entries when they switch
// state context, and restore the generation counter on drop.

/// Part of #3407 Step 3: bind_next_state_array_guard bumps the hoist state
/// generation, invalidating cached values from the previous state context.
/// On drop, the generation is restored so outer hoist frames become valid again.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_next_state_guard_invalidates_hoist_cache() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(1)];
    ctx.bind_state_array(&state);

    // Create a hoistable expression (must be in is_stage1_hoistable allowlist).
    // Expr::Not is stage-1 hoistable; Expr::Int/Bool are not.
    let expr = Spanned::dummy(Expr::Not(Box::new(Spanned::dummy(Expr::Bool(false)))));
    let cached_value = Value::Bool(true);
    let mut hoistable = FxHashSet::default();
    hoistable.insert(std::ptr::addr_of!(expr.node) as usize);
    let _hoist_guard =
        enter_quantifier_hoist_scope(Rc::new(hoistable)).expect("hoist scope should push");
    quantifier_hoist_store(&expr.node, &cached_value);

    // Hoist lookup should succeed before state switch.
    assert_eq!(
        quantifier_hoist_lookup(&expr.node),
        Some(cached_value.clone()),
        "hoist cache should return stored value before state switch"
    );

    {
        // bind_next_state_array_guard bumps hoist generation via HoistGenerationGuard.
        let next = vec![Value::int(99)];
        let _state_guard = ctx.bind_next_state_array_guard(&next);

        // Hoist lookup should FAIL — generation was bumped by the guard.
        assert_eq!(
            quantifier_hoist_lookup(&expr.node),
            None,
            "hoist cache must be invalidated after bind_next_state_array_guard \
             (generation mismatch from HoistGenerationGuard)"
        );
    }
    // Guard dropped — generation restored.

    // Hoist lookup should succeed again after guard drop restores generation.
    assert_eq!(
        quantifier_hoist_lookup(&expr.node),
        Some(cached_value),
        "hoist cache should be accessible again after guard drop restores generation"
    );

    clear_for_test_reset();
}

/// Part of #3460: explicit next-state scopes also need hoist-generation bumps so
/// cached values from the outer context are not reused while a temporary
/// successor overlay is active.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_explicit_next_state_guard_invalidates_hoist_cache() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");

    let expr = Spanned::dummy(Expr::Not(Box::new(Spanned::dummy(Expr::Bool(false)))));
    let cached_value = Value::Bool(true);
    let mut hoistable = FxHashSet::default();
    hoistable.insert(std::ptr::addr_of!(expr.node) as usize);
    let _hoist_guard =
        enter_quantifier_hoist_scope(Rc::new(hoistable)).expect("hoist scope should push");
    quantifier_hoist_store(&expr.node, &cached_value);

    assert_eq!(
        quantifier_hoist_lookup(&expr.node),
        Some(cached_value.clone()),
        "setup: hoist cache should be populated"
    );

    {
        let mut explicit_next = Env::default();
        explicit_next.insert(Arc::from("x"), Value::int(99));
        let _guard = ctx.bind_explicit_next_state_guard(explicit_next);
        assert_eq!(
            quantifier_hoist_lookup(&expr.node),
            None,
            "hoist cache must be invalidated after bind_explicit_next_state_guard"
        );
    }

    assert_eq!(
        quantifier_hoist_lookup(&expr.node),
        Some(cached_value),
        "hoist cache should be restored after explicit next-state guard drop"
    );

    clear_for_test_reset();
}

/// Part of #3407 Step 3: bind_state_array_guard also bumps generation.
/// This protects the current-state binding path (used in liveness evaluation).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_guard_invalidates_hoist_cache() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(1)];
    ctx.bind_state_array(&state);

    // Use Expr::Add — stage-1 hoistable binary operator.
    let expr = Spanned::dummy(Expr::Add(
        Box::new(Spanned::dummy(Expr::Int(1.into()))),
        Box::new(Spanned::dummy(Expr::Int(76.into()))),
    ));
    let cached_value = Value::int(77);
    let mut hoistable = FxHashSet::default();
    hoistable.insert(std::ptr::addr_of!(expr.node) as usize);
    let _hoist_guard =
        enter_quantifier_hoist_scope(Rc::new(hoistable)).expect("hoist scope should push");
    quantifier_hoist_store(&expr.node, &cached_value);

    assert_eq!(
        quantifier_hoist_lookup(&expr.node),
        Some(cached_value.clone()),
        "setup: hoist cache should be populated"
    );

    {
        let other_state = vec![Value::int(999)];
        let _state_guard = ctx.bind_state_array_guard(&other_state);

        assert_eq!(
            quantifier_hoist_lookup(&expr.node),
            None,
            "hoist cache must be invalidated after bind_state_array_guard"
        );
    }

    assert_eq!(
        quantifier_hoist_lookup(&expr.node),
        Some(cached_value),
        "hoist cache should be restored after state guard drop"
    );

    clear_for_test_reset();
}

/// Part of #3407 Step 3: scope_guard_with_next_state bumps generation.
/// This protects the liveness property checking path where both env and
/// next_state are temporarily modified.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scope_guard_with_next_state_invalidates_hoist_cache() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(1)];
    ctx.bind_state_array(&state);

    // Use Expr::Eq — stage-1 hoistable comparison operator.
    let expr = Spanned::dummy(Expr::Eq(
        Box::new(Spanned::dummy(Expr::Int(1.into()))),
        Box::new(Spanned::dummy(Expr::Int(1.into()))),
    ));
    let cached_value = Value::Bool(true);
    let mut hoistable = FxHashSet::default();
    hoistable.insert(std::ptr::addr_of!(expr.node) as usize);
    let _hoist_guard =
        enter_quantifier_hoist_scope(Rc::new(hoistable)).expect("hoist scope should push");
    quantifier_hoist_store(&expr.node, &cached_value);

    assert_eq!(
        quantifier_hoist_lookup(&expr.node),
        Some(cached_value.clone()),
        "setup: hoist cache should be populated"
    );

    {
        let _scope_guard = ctx.scope_guard_with_next_state();

        assert_eq!(
            quantifier_hoist_lookup(&expr.node),
            None,
            "hoist cache must be invalidated after scope_guard_with_next_state"
        );
    }

    assert_eq!(
        quantifier_hoist_lookup(&expr.node),
        Some(cached_value),
        "hoist cache should be restored after scope guard drop"
    );

    clear_for_test_reset();
}

// === State-eval boundary contract tests (Part of #3469) ===
//
// Focused tests for the boundary hierarchy documented in eval_cache_lifecycle.rs:
//   clear_for_state_boundary < clear_for_eval_scope_boundary < clear_for_bound_state_eval_scope

/// Part of #3469: `clear_for_bound_state_eval_scope` resets lookup mode AND clears
/// eval-scope caches. This is the checker-level boundary (superset of `clear_for_state_eval_replay`).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_clear_for_bound_state_eval_scope_resets_lookup_mode_and_clears_caches() {
    clear_for_test_reset();

    let ctx = EvalCtx::new();
    insert_subst_cache("bound_scope_test", Value::Bool(true));
    assert_eq!(subst_cache_len(), 1, "setup should populate SUBST_CACHE");

    ctx.runtime_state
        .state_lookup_mode
        .set(StateLookupMode::Next);

    clear_for_bound_state_eval_scope(&ctx);

    assert_eq!(
        ctx.runtime_state.state_lookup_mode.get(),
        StateLookupMode::Current,
        "bound_state_eval_scope should reset lookup mode to Current"
    );
    assert_eq!(
        subst_cache_len(),
        0,
        "bound_state_eval_scope should clear eval-scope caches (delegates to clear_for_eval_scope_boundary)"
    );

    clear_for_test_reset();
}

/// Part of #3469: Generation counters are advanced by `invalidate_state_identity_tracking`,
/// which is called inside `clear_for_eval_scope_boundary`. Verify the contract.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_generation_counters_advance_on_identity_invalidation() {
    use crate::eval_cache_lifecycle::{
        current_next_state_gen, current_state_gen, invalidate_state_identity_tracking,
        reset_state_generation_counters,
    };
    reset_state_generation_counters();

    let gen_before = current_state_gen();
    let next_gen_before = current_next_state_gen();

    invalidate_state_identity_tracking();

    let gen_after = current_state_gen();
    let next_gen_after = current_next_state_gen();

    assert!(
        gen_after > gen_before,
        "state generation must advance after invalidate_state_identity_tracking \
         (was {gen_before}, now {gen_after})"
    );
    assert!(
        next_gen_after > next_gen_before,
        "next-state generation must advance after invalidate_state_identity_tracking \
         (was {next_gen_before}, now {next_gen_after})"
    );

    reset_state_generation_counters();
}

/// Part of #3469: `clear_for_eval_scope_boundary` must advance generation counters
/// (via its call to `invalidate_state_identity_tracking`), ensuring the next `eval_entry`
/// sees a state change.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_scope_boundary_advances_generation_counters() {
    use crate::cache::lifecycle::clear_for_eval_scope_boundary;
    use crate::eval_cache_lifecycle::{current_state_gen, reset_state_generation_counters};

    clear_for_test_reset();
    reset_state_generation_counters();

    let gen_before = current_state_gen();
    clear_for_eval_scope_boundary();
    let gen_after = current_state_gen();

    assert!(
        gen_after > gen_before,
        "clear_for_eval_scope_boundary must advance state generation counter \
         (was {gen_before}, now {gen_after}) — this forces eval_entry to detect state change"
    );

    clear_for_test_reset();
}

/// Part of #3469: Boundary hierarchy contrast — `clear_for_state_boundary` does NOT
/// advance generation counters (it's a weaker clear). This confirms the hierarchy
/// documented in the boundary matrix.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_boundary_does_not_advance_generation_counters() {
    use crate::cache::lifecycle::clear_for_state_boundary;
    use crate::eval_cache_lifecycle::{current_state_gen, reset_state_generation_counters};

    clear_for_test_reset();
    reset_state_generation_counters();

    let gen_before = current_state_gen();
    clear_for_state_boundary();
    let gen_after = current_state_gen();

    assert_eq!(
        gen_after, gen_before,
        "clear_for_state_boundary must NOT advance generation counters \
         (it's a weaker boundary — only clear_for_eval_scope_boundary and above do)"
    );

    clear_for_test_reset();
}

/// Part of #3469: `clear_for_state_eval_replay` and `clear_for_bound_state_eval_scope`
/// both produce the same cache-level effect (both delegate to `clear_for_eval_scope_boundary`).
/// The difference: replay asserts `op_dep_stack` is empty, bound_state_eval_scope does not.
/// This test verifies the cache-level equivalence.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_replay_and_bound_scope_both_advance_generation_and_clear_caches() {
    use crate::eval_cache_lifecycle::{current_state_gen, reset_state_generation_counters};
    clear_for_test_reset();

    let ctx = EvalCtx::new();

    // Test clear_for_state_eval_replay
    reset_state_generation_counters();
    insert_subst_cache("replay_test", Value::Bool(true));
    ctx.runtime_state
        .state_lookup_mode
        .set(StateLookupMode::Next);
    let gen_before_replay = current_state_gen();

    clear_for_state_eval_replay(&ctx);

    let gen_after_replay = current_state_gen();
    let cache_after_replay = subst_cache_len();
    let mode_after_replay = ctx.runtime_state.state_lookup_mode.get();

    // Test clear_for_bound_state_eval_scope
    reset_state_generation_counters();
    insert_subst_cache("bound_test", Value::Bool(true));
    ctx.runtime_state
        .state_lookup_mode
        .set(StateLookupMode::Next);
    let gen_before_bound = current_state_gen();

    clear_for_bound_state_eval_scope(&ctx);

    let gen_after_bound = current_state_gen();
    let cache_after_bound = subst_cache_len();
    let mode_after_bound = ctx.runtime_state.state_lookup_mode.get();

    // Both should produce the same effects
    assert!(
        gen_after_replay > gen_before_replay,
        "replay must advance gen"
    );
    assert!(
        gen_after_bound > gen_before_bound,
        "bound_scope must advance gen"
    );
    assert_eq!(cache_after_replay, 0, "replay must clear caches");
    assert_eq!(cache_after_bound, 0, "bound_scope must clear caches");
    assert_eq!(
        mode_after_replay,
        StateLookupMode::Current,
        "replay must reset mode"
    );
    assert_eq!(
        mode_after_bound,
        StateLookupMode::Current,
        "bound_scope must reset mode"
    );

    clear_for_test_reset();
}
