// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::Arc;

fn seed_state_identity_tracking(ctx: &EvalCtx) {
    eval_entry_with(ctx, || Ok::<(), crate::error::EvalError>(()))
        .expect("eval_entry_with should succeed");
}

fn state_identity_tracking_snapshot() -> (usize, usize) {
    crate::eval_cache_lifecycle::state_identity_tracking_snapshot()
}

const INVALIDATED_STATE_IDENTITY_SNAPSHOT: (usize, usize) = (usize::MAX, usize::MAX);

fn assert_state_identity_tracking_invalidated(message: &str) {
    assert_eq!(
        state_identity_tracking_snapshot(),
        INVALIDATED_STATE_IDENTITY_SNAPSHOT,
        "{message}"
    );
}

/// Part of #3411 Step 3: bind_next_state_array_guard invalidates state-identity
/// tracking on create and again on drop.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_next_state_guard_invalidates_state_identity_tracking_on_create_and_drop() {
    clear_for_test_reset();
    crate::invalidate_state_identity_tracking();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let next_state = vec![Value::int(1)];
    ctx.bind_next_state_array(&next_state);
    seed_state_identity_tracking(&ctx);
    assert_eq!(
        state_identity_tracking_snapshot(),
        (0, next_state.as_ptr() as usize),
        "setup: eval_entry_with should record the bound next-state pointer"
    );

    {
        let other_next_state = vec![Value::int(2)];
        let _guard = ctx.bind_next_state_array_guard(&other_next_state);
        assert_state_identity_tracking_invalidated(
            "bind_next_state_array_guard must invalidate tracking before the inner eval scope",
        );
    }

    assert_state_identity_tracking_invalidated(
        "bind_next_state_array_guard drop must invalidate tracking after restoring the outer next-state",
    );

    crate::invalidate_state_identity_tracking();
    clear_for_test_reset();
}

/// Part of #3411 Step 3: bind_state_array_guard invalidates state-identity
/// tracking on create and again on drop.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_guard_invalidates_state_identity_tracking_on_create_and_drop() {
    clear_for_test_reset();
    crate::invalidate_state_identity_tracking();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(1)];
    ctx.bind_state_array(&state);
    seed_state_identity_tracking(&ctx);
    assert_eq!(
        state_identity_tracking_snapshot(),
        (state.as_ptr() as usize, 0),
        "setup: eval_entry_with should record the bound current-state pointer"
    );

    {
        let other_state = vec![Value::int(2)];
        let _guard = ctx.bind_state_array_guard(&other_state);
        assert_state_identity_tracking_invalidated(
            "bind_state_array_guard must invalidate tracking before the inner eval scope",
        );
    }

    assert_state_identity_tracking_invalidated(
        "bind_state_array_guard drop must invalidate tracking after restoring the outer state",
    );

    crate::invalidate_state_identity_tracking();
    clear_for_test_reset();
}

/// Part of #3411 Step 3: take_next_state_env_guard invalidates state-identity
/// tracking on create and again on drop.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_take_next_state_guard_invalidates_state_identity_tracking_on_create_and_drop() {
    clear_for_test_reset();
    crate::invalidate_state_identity_tracking();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let next_state = vec![Value::int(1)];
    ctx.bind_next_state_array(&next_state);
    seed_state_identity_tracking(&ctx);
    assert_eq!(
        state_identity_tracking_snapshot(),
        (0, next_state.as_ptr() as usize),
        "setup: eval_entry_with should record the bound next-state pointer"
    );

    {
        let _guard = ctx.take_next_state_env_guard();
        assert_state_identity_tracking_invalidated(
            "take_next_state_env_guard must invalidate tracking before the next-state binding is cleared",
        );
    }

    assert_state_identity_tracking_invalidated(
        "take_next_state_env_guard drop must invalidate tracking after restoring the outer next-state",
    );

    crate::invalidate_state_identity_tracking();
    clear_for_test_reset();
}

/// Part of #3460: explicit next-state guard invalidates state-identity tracking
/// on create and again on drop, even though the explicit next-state itself is
/// not represented by array pointers.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_explicit_next_state_guard_invalidates_state_identity_tracking_on_create_and_drop() {
    clear_for_test_reset();
    crate::invalidate_state_identity_tracking();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    seed_state_identity_tracking(&ctx);
    assert_eq!(
        state_identity_tracking_snapshot(),
        (0, 0),
        "setup: env-only eval should record the clean no-array snapshot"
    );

    {
        let mut explicit_next = Env::default();
        explicit_next.insert(Arc::from("x"), Value::int(2));
        let _guard = ctx.bind_explicit_next_state_guard(explicit_next);
        assert_state_identity_tracking_invalidated(
            "bind_explicit_next_state_guard must invalidate tracking before the inner explicit next-state scope",
        );

        seed_state_identity_tracking(&ctx);
        assert_eq!(
            state_identity_tracking_snapshot(),
            (0, 0),
            "inner eval should repopulate the env-only tracking snapshot"
        );
    }

    assert_state_identity_tracking_invalidated(
        "bind_explicit_next_state_guard drop must invalidate tracking after restoring the outer next-state view",
    );

    crate::invalidate_state_identity_tracking();
    clear_for_test_reset();
}

/// Part of #3411 Step 3: take_state_env_guard invalidates state-identity tracking
/// on create and again on drop.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_take_state_guard_invalidates_state_identity_tracking_on_create_and_drop() {
    clear_for_test_reset();
    crate::invalidate_state_identity_tracking();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(1)];
    ctx.bind_state_array(&state);
    seed_state_identity_tracking(&ctx);
    assert_eq!(
        state_identity_tracking_snapshot(),
        (state.as_ptr() as usize, 0),
        "setup: eval_entry_with should record the bound current-state pointer"
    );

    {
        let _guard = ctx.take_state_env_guard();
        assert_state_identity_tracking_invalidated(
            "take_state_env_guard must invalidate tracking before the state binding is cleared",
        );
    }

    assert_state_identity_tracking_invalidated(
        "take_state_env_guard drop must invalidate tracking after restoring the outer state",
    );

    crate::invalidate_state_identity_tracking();
    clear_for_test_reset();
}

/// Part of #3411 Step 3: scope_guard_with_next_state uses a restore-only state
/// identity guard, so entering the scope leaves tracking intact while restoring
/// the outer explicit next-state invalidates it on drop.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scope_guard_with_next_state_invalidates_state_identity_tracking_on_restore() {
    clear_for_test_reset();
    crate::invalidate_state_identity_tracking();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(1)];
    ctx.bind_state_array(&state);
    seed_state_identity_tracking(&ctx);
    assert_eq!(
        state_identity_tracking_snapshot(),
        (state.as_ptr() as usize, 0),
        "setup: eval_entry_with should record the bound current-state pointer"
    );

    {
        let _guard = ctx.scope_guard_with_next_state();
        assert_eq!(
            state_identity_tracking_snapshot(),
            (state.as_ptr() as usize, 0),
            "scope_guard_with_next_state should not invalidate until the saved explicit next-state is restored"
        );

        let mut next_state = Env::default();
        next_state.insert(Arc::from("x"), Value::int(2));
        ctx.set_next_state(next_state);
        assert_state_identity_tracking_invalidated(
            "set_next_state must invalidate state identity tracking for the explicit next-state transition",
        );

        seed_state_identity_tracking(&ctx);
        assert_eq!(
            state_identity_tracking_snapshot(),
            (state.as_ptr() as usize, 0),
            "inner eval should repopulate tracking before the outer next-state is restored"
        );
    }

    assert_state_identity_tracking_invalidated(
        "scope_guard_with_next_state drop must invalidate tracking after restoring the saved explicit next-state",
    );

    crate::invalidate_state_identity_tracking();
    clear_for_test_reset();
}

/// Part of #3411 memory_verification audit: plain `scope_guard()` must NOT carry
/// a StateIdentityGuard. Env-only scopes (no next_state change) should not pay
/// the 2-cell invalidation cost on drop. This is the negative counterpart to
/// `test_scope_guard_with_next_state_invalidates_state_identity_tracking_on_restore`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scope_guard_does_not_invalidate_state_identity_tracking() {
    clear_for_test_reset();
    crate::invalidate_state_identity_tracking();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(1)];
    ctx.bind_state_array(&state);
    seed_state_identity_tracking(&ctx);
    let snapshot_before = state_identity_tracking_snapshot();
    assert_eq!(
        snapshot_before,
        (state.as_ptr() as usize, 0),
        "setup: eval_entry_with should record the bound current-state pointer"
    );

    {
        let _guard = ctx.scope_guard();
        assert_eq!(
            state_identity_tracking_snapshot(),
            snapshot_before,
            "scope_guard() must not invalidate state identity tracking on create"
        );
        // Modify env inside the scope to simulate real usage
        ctx.bind_mut(Arc::from("y"), Value::int(42));
    }

    // After drop: scope_guard() restores env but carries _state_identity_guard: None,
    // so tracking should still reflect the original seeded state pointer.
    assert_eq!(
        state_identity_tracking_snapshot(),
        snapshot_before,
        "scope_guard() drop must NOT invalidate state identity tracking — \
         env-only scopes do not affect array state identity"
    );

    crate::invalidate_state_identity_tracking();
    clear_for_test_reset();
}

/// Part of #3411 audit fix: `set_next_state` must also force a fresh eval-entry
/// boundary for env-only contexts where both tracked array identities are absent.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_next_state_invalidates_env_only_contexts() {
    clear_for_test_reset();
    crate::invalidate_state_identity_tracking();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    seed_state_identity_tracking(&ctx);
    assert_eq!(
        state_identity_tracking_snapshot(),
        (0, 0),
        "setup: env-only eval should keep the clean no-array snapshot"
    );

    let mut next_state = Env::default();
    next_state.insert(Arc::from("x"), Value::int(2));
    ctx.set_next_state(next_state);
    assert_state_identity_tracking_invalidated(
        "set_next_state must mark env-only contexts dirty so the next eval_entry clears caches",
    );

    seed_state_identity_tracking(&ctx);
    assert_eq!(
        state_identity_tracking_snapshot(),
        (0, 0),
        "env-only eval_entry should consume the dirty marker and restore the clean no-array snapshot"
    );

    crate::invalidate_state_identity_tracking();
    clear_for_test_reset();
}
