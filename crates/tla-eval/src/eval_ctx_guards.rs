// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RAII guard types for `EvalCtx` scope management.
//!
//! Extracted from `core.rs` as part of #2764 / #1643. Contains:
//! - `NextStateEnvGuard`: restores `next_state_env` on drop
//! - `NextStateMutGuard`: restores HashMap-based `next_state` on drop (Part of #3421)
//! - `ExplicitNextStateGuard`: temporarily binds explicit `next_state`
//! - `StateEnvGuard`: restores `state_env` on drop
//! - `SkipPrimeValidationGuard`: restores `skip_prime_validation` on drop
//! - `ScopeGuard`: restores `env` (and optionally `next_state`) on drop

use super::{
    invalidate_state_identity_tracking_with_ctx, Env, EvalCtx, StateEnvRef, StateIdentityGuard,
};
use crate::cache::HoistGenerationGuard;
use std::sync::Arc;

/// RAII guard that saves and restores the HashMap-based `next_state` on drop.
///
/// Created by [`EvalCtx::take_next_state_guard`]. Clears `next_state` on
/// creation and restores the previous value on drop, including on panic or
/// early `?` return. This eliminates the class of restore-skipping bugs in
/// liveness save/restore patterns where manual `*ctx.next_state_mut() = prev`
/// is bypassed by `?`-driven early returns.
///
/// Part of #3421: the HashMap-based `next_state` had no RAII guard, unlike
/// `next_state_env` (covered by [`NextStateEnvGuard`]).
///
/// # Safety
///
/// Uses a raw `*mut EvalCtx` internally so the caller can continue using
/// `&mut EvalCtx` for evaluation while the guard is alive. The guard must
/// not outlive the `EvalCtx` it was created from — Rust scoping enforces
/// this when the guard is bound to a local variable.
#[must_use = "if unused, the guard drops immediately and the restore is a no-op"]
pub struct NextStateMutGuard {
    pub(super) ctx: *mut EvalCtx,
    pub(super) prev: Option<Arc<Env>>,
}

impl Drop for NextStateMutGuard {
    fn drop(&mut self) {
        // SAFETY: Same invariant as `NextStateEnvGuard` — guard was created from
        // `&mut EvalCtx` and is dropped before the `EvalCtx` goes out of scope.
        unsafe {
            let ctx = &*self.ctx;
            (*self.ctx).stable_mut().next_state = self.prev.take();
            // Part of #3962: Use ctx-aware variant to keep generation shadows in sync.
            invalidate_state_identity_tracking_with_ctx(ctx);
        }
    }
}

/// RAII guard that restores explicit `next_state` bindings on drop.
///
/// Created by [`EvalCtx::bind_explicit_next_state_guard`]. Temporarily binds the
/// HashMap-based `next_state`, clears any array-backed `next_state_env`, and
/// restores both on drop, including on panic or early return.
#[allow(dead_code)] // Tested in eval_ctx_guards tests; not yet adopted by tla-check callers.
#[must_use = "if unused, the guard drops immediately and the restore is a no-op"]
pub(crate) struct ExplicitNextStateGuard {
    pub(super) ctx: *mut EvalCtx,
    pub(super) prev_next_state: Option<Arc<Env>>,
    pub(super) prev_next_state_env: Option<StateEnvRef>,
    /// Part of #3460: explicit next-state scopes must bump hoist generation so
    /// cached values from the outer context are not reused.
    pub(super) _hoist_guard: HoistGenerationGuard,
    /// Part of #3460: explicit next-state scopes must invalidate state-identity
    /// tracking on create and again after the outer bindings are restored.
    /// Last field so it drops after the explicit bindings are restored.
    pub(super) _state_identity_guard: StateIdentityGuard,
}

impl Drop for ExplicitNextStateGuard {
    fn drop(&mut self) {
        // SAFETY: Same invariant as `NextStateEnvGuard` — guard was created from
        // `&mut EvalCtx` and is dropped before the `EvalCtx` goes out of scope.
        unsafe {
            let ctx = &mut *self.ctx;
            let stable = ctx.stable_mut();
            stable.next_state = self.prev_next_state.take();
            stable.next_state_env = self.prev_next_state_env.take();
            ctx.tlc_action_context = None;
        }
    }
}

/// RAII guard that restores `next_state_env` on drop.
///
/// Created by [`EvalCtx::bind_next_state_array_guard`] or
/// [`EvalCtx::take_next_state_env_guard`]. Automatically restores the
/// previous `next_state_env` when dropped, including on panic or early return.
///
/// # Safety
///
/// Uses a raw `*mut EvalCtx` internally so the caller can continue using
/// `&mut EvalCtx` for evaluation while the guard is alive. The guard must
/// not outlive the `EvalCtx` it was created from — Rust scoping enforces
/// this when the guard is bound to a local variable.
#[must_use = "if unused, the guard drops immediately and the restore is a no-op"]
pub struct NextStateEnvGuard {
    pub(super) ctx: *mut EvalCtx,
    pub(super) prev: Option<StateEnvRef>,
    /// Part of #3407: Bumps hoist state generation on create, restores on drop.
    /// No-op when no hoist scope is active (previous_generation is None).
    pub(super) _hoist_guard: HoistGenerationGuard,
    /// Part of #3411: invalidates state-identity tracking on create/drop.
    /// Last field so it drops after explicit Drop restores state env pointers.
    pub(super) _state_identity_guard: StateIdentityGuard,
}

impl Drop for NextStateEnvGuard {
    fn drop(&mut self) {
        // SAFETY: The guard was created from a `&mut EvalCtx` and is dropped
        // before the `EvalCtx` goes out of scope. No other mutable references
        // to `EvalCtx` exist during `Drop`.
        unsafe {
            (*self.ctx).restore_next_state_env(self.prev);
        }
    }
}

/// RAII guard that restores `state_env` on drop.
///
/// Created by [`EvalCtx::bind_state_array_guard`] or
/// [`EvalCtx::take_state_env_guard`]. Automatically restores the
/// previous `state_env` when dropped, including on panic or early return.
#[must_use = "if unused, the guard drops immediately and the restore is a no-op"]
pub struct StateEnvGuard {
    pub(super) ctx: *mut EvalCtx,
    pub(super) prev: Option<StateEnvRef>,
    /// Part of #3407: Bumps hoist state generation on create, restores on drop.
    pub(super) _hoist_guard: HoistGenerationGuard,
    /// Part of #3411: invalidates state-identity tracking on create/drop.
    /// Last field so it drops after explicit Drop restores state env pointers.
    pub(super) _state_identity_guard: StateIdentityGuard,
}

impl Drop for StateEnvGuard {
    fn drop(&mut self) {
        // SAFETY: Same invariant as `NextStateEnvGuard`.
        unsafe {
            (*self.ctx).restore_state_env(self.prev);
        }
    }
}

/// RAII guard that restores `skip_prime_validation` on drop.
///
/// Created by [`EvalCtx::skip_prime_guard`]. Prevents the flag from leaking
/// on early `?` returns or panics — the same class of bug that motivated
/// `StateLookupModeGuard` (fix #2283) and `SubstCacheGuard` (fix #2260).
///
/// # Safety
///
/// Uses a raw `*mut EvalCtx` internally so the caller can continue using
/// `&mut EvalCtx` for evaluation while the guard is alive. The guard must
/// not outlive the `EvalCtx` it was created from — Rust scoping enforces
/// this when the guard is bound to a local variable.
#[must_use = "if unused, the guard drops immediately and the restore is a no-op"]
pub struct SkipPrimeValidationGuard {
    pub(super) ctx: *mut EvalCtx,
    pub(super) prev: bool,
}

impl SkipPrimeValidationGuard {
    /// The previous value of `skip_prime_validation` before the guard was created.
    ///
    /// Needed by `ScopeRestore::saved_skip_prime` in the conjunct enumeration path,
    /// where the saved value is passed to a deferred-restore struct in addition to
    /// being restored locally by this guard on drop.
    #[inline]
    pub fn prev(&self) -> bool {
        self.prev
    }
}

impl Drop for SkipPrimeValidationGuard {
    fn drop(&mut self) {
        // SAFETY: Same invariant as `NextStateEnvGuard` — guard was created from
        // `&mut EvalCtx` and is dropped before the `EvalCtx` goes out of scope.
        unsafe {
            (*self.ctx).stable_mut().skip_prime_validation = self.prev;
        }
    }
}

/// RAII guard that restores the `EvalCtx` variable environment (`env`) on drop.
///
/// Created by [`EvalCtx::scope_guard`] or [`EvalCtx::scope_guard_with_next_state`].
/// Automatically restores the saved `env` (and optionally `next_state`) when
/// dropped, including on panic or early `?` return. This eliminates the class
/// of scope-leak bugs caused by manual `save_scope`/`restore_scope` pairs
/// (see #2738, #2733).
///
/// # Safety
///
/// Uses a raw `*mut EvalCtx` internally so the caller can continue using
/// `&mut EvalCtx` for evaluation while the guard is alive. The guard must
/// not outlive the `EvalCtx` it was created from — Rust scoping enforces
/// this when the guard is bound to a local variable.
#[must_use = "if unused, the guard drops immediately and the restore is a no-op"]
pub struct ScopeGuard {
    pub(super) ctx: *mut EvalCtx,
    /// Arc-wrapped for O(1) save/restore (Part of #1383).
    pub(super) saved_env: Arc<Env>,
    /// When `Some`, the guard also restores `next_state` on drop.
    /// `None` = don't restore, `Some(None)` = restore to None, `Some(Some(e))` = restore to e.
    #[allow(clippy::option_option)]
    pub(super) saved_next_state: Option<Option<Arc<Env>>>,
    /// Part of #3407: Bumps hoist state generation on create, restores on drop.
    pub(super) _hoist_guard: HoistGenerationGuard,
    /// Part of #3411: `scope_guard_with_next_state()` uses a restore-only guard so
    /// the restored explicit next-state becomes a fresh eval cache boundary.
    /// Plain `scope_guard()` leaves this as `None`.
    pub(super) _state_identity_guard: Option<StateIdentityGuard>,
}

impl Drop for ScopeGuard {
    fn drop(&mut self) {
        // SAFETY: Same invariant as `NextStateEnvGuard` — guard was created from
        // `&mut EvalCtx` and is dropped before the `EvalCtx` goes out of scope.
        unsafe {
            let s = (*self.ctx).stable_mut();
            s.env = std::mem::take(&mut self.saved_env);
            if let Some(next) = self.saved_next_state.take() {
                s.next_state = next;
            }
        }
    }
}
