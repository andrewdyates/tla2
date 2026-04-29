// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Cache lifecycle entrypoint and stack-safe evaluation wrapper.
//!
//! Extracted from `core.rs` as part of #2764 / #1643. Contains:
//! - Stack overflow protection constants and `stack_safe`
//! - Thread-local state/next-state tracking for cache invalidation
//! - `eval_entry`: External evaluation entry point with cache management
//! - `force_lazy_thunk_if_needed`: Lazy thunk forcing with dep tracking

use super::{
    eval, is_dep_tracking_active, on_cache_event, propagate_thunk_deps, store_thunk_deps,
    thunk_has_instance_lazy_taint, trim_eval_entry_caches, CacheEvent, EvalCtx, EvalError,
    EvalResult, SubstCacheGuard,
};
use crate::helpers::restore_captured_binding_chain;
use crate::value::Value;
use std::sync::Arc;
use tla_core::Spanned;

/// Red zone size: when stack has less than this remaining, grow.
///
/// This must be large enough to handle match arms that allocate sizable stack frames.
/// If the red zone is too small, a single large frame allocation can jump across the
/// guard page before `stacker::maybe_grow` gets a chance to switch stacks.
const STACK_RED_ZONE: usize = 1024 * 1024; // 1MB red zone
/// Stack growth size: how much to grow when we hit the red zone
const STACK_GROW_SIZE: usize = 16 * 1024 * 1024; // 16MB growth - plenty of room

/// Stack-safe recursive call wrapper.
///
/// Wraps `stacker::maybe_grow` with canonical constants (1MB red zone, 16MB growth).
/// Use this for all recursive evaluation, compilation, and enumeration paths.
///
/// Under Kani verification, stacker uses FFI (psm crate) which Kani doesn't support,
/// so we bypass the stack check and call the closure directly.
///
/// Consolidates 4 previously divergent constant definitions (#2287).
/// Reference: lean5's `stack_safe()` at `lean5-kernel/src/expr/mod.rs`.
#[inline(always)]
pub fn stack_safe<R>(f: impl FnOnce() -> R) -> R {
    #[cfg(kani)]
    {
        f()
    }
    #[cfg(not(kani))]
    {
        stacker::maybe_grow(STACK_RED_ZONE, STACK_GROW_SIZE, f)
    }
}

// Part of #3962: Consolidated state-identity tracking into a single thread-local
// struct. Previously 6 separate thread_locals — each access was a separate
// `_tlv_get_addr` call. Now a single TLS access for all state-identity operations.
//
// Thread-local tracking of last seen state/next-state for cache invalidation.
// Part of #346 (Phase 4): Clear ZERO_ARG_OP_CACHE only when state changes.
// Fix #2364: Also track next-state pointer for SUBST_CACHE invalidation.
// Fix #3447: Monotonic generation counters for ABA-safe state-change detection.
struct StateIdentityTracking {
    last_state_ptr: usize,
    last_next_state_ptr: usize,
    state_generation: u64,
    last_state_gen: u64,
    next_state_generation: u64,
    last_next_state_gen: u64,
}

std::thread_local! {
    static STATE_IDENTITY: std::cell::RefCell<StateIdentityTracking> =
        const { std::cell::RefCell::new(StateIdentityTracking {
            last_state_ptr: 0,
            last_next_state_ptr: 0,
            state_generation: 0,
            last_state_gen: 0,
            next_state_generation: 0,
            last_next_state_gen: 0,
        }) };
}

/// Advance the state generation counter. Call on every logical state transition.
///
/// For callers without ctx access (RAII guards, Drop impls). Updates TLS only.
/// Prefer `advance_state_generation_with_ctx` when ctx is available.
#[allow(dead_code)] // Part of public API; internal callers now inline this
pub fn advance_state_generation() {
    STATE_IDENTITY.with(|c| {
        let mut s = c.borrow_mut();
        s.state_generation = s.state_generation.wrapping_add(1);
    });
}

/// Part of #3962: Ctx-aware variant that updates both TLS and the
/// `EvalRuntimeState` shadow. Eliminates 1 TLS read per `enter_eval_boundary`
/// call by keeping the shadow in sync with the canonical TLS counter.
#[inline]
#[allow(dead_code)] // Part of public API; internal callers now inline this
pub fn advance_state_generation_with_ctx(ctx: &EvalCtx) {
    STATE_IDENTITY.with(|c| {
        let mut s = c.borrow_mut();
        let new = s.state_generation.wrapping_add(1);
        s.state_generation = new;
        ctx.runtime_state.state_generation.set(new);
    });
}

/// Advance the next-state generation counter.
///
/// For callers without ctx access. Prefer `advance_next_state_generation_with_ctx`.
#[allow(dead_code)] // Part of public API; internal callers now inline this
pub fn advance_next_state_generation() {
    STATE_IDENTITY.with(|c| {
        let mut s = c.borrow_mut();
        s.next_state_generation = s.next_state_generation.wrapping_add(1);
    });
}

/// Part of #3962: Ctx-aware variant that updates both TLS and shadow.
#[inline]
#[allow(dead_code)] // Part of public API; internal callers now inline this
pub fn advance_next_state_generation_with_ctx(ctx: &EvalCtx) {
    STATE_IDENTITY.with(|c| {
        let mut s = c.borrow_mut();
        let new = s.next_state_generation.wrapping_add(1);
        s.next_state_generation = new;
        ctx.runtime_state.next_state_generation.set(new);
    });
}

/// Get the current state generation counter value.
///
/// Used by test code and callers without ctx access. Production hot paths
/// should prefer `current_state_gen_ctx`.
#[allow(dead_code)] // Used in tests (hoist_generation.rs) and by external crates
pub fn current_state_gen() -> u64 {
    STATE_IDENTITY.with(|c| c.borrow().state_generation)
}

/// Part of #3962: Read state generation from the `EvalRuntimeState` shadow
/// instead of TLS. Use when ctx is available and the shadow is known to be
/// in sync (i.e., callers use `advance_state_generation_with_ctx`).
#[inline]
pub fn current_state_gen_ctx(ctx: &EvalCtx) -> u64 {
    ctx.runtime_state.state_generation.get()
}

/// Get the current next-state generation counter value.
///
/// Used by test code. Production hot paths prefer `current_next_state_gen_ctx`.
#[allow(dead_code)] // Used in tests (hoist_generation.rs) and by external crates
pub fn current_next_state_gen() -> u64 {
    STATE_IDENTITY.with(|c| c.borrow().next_state_generation)
}

/// Part of #3962: Read next-state generation from shadow.
#[inline]
pub fn current_next_state_gen_ctx(ctx: &EvalCtx) -> u64 {
    ctx.runtime_state.next_state_generation.get()
}

/// Reset all generation counters to zero for test/run isolation.
pub fn reset_state_generation_counters() {
    STATE_IDENTITY.with(|c| {
        let mut s = c.borrow_mut();
        s.state_generation = 0;
        s.last_state_gen = 0;
        s.next_state_generation = 0;
        s.last_next_state_gen = 0;
    });
}

/// Synthetic "dirty" marker used to force the next `eval_entry` boundary even
/// when the current eval context has no array-backed state bindings (`0`/`0`).
///
/// Real slice pointers are never `usize::MAX`, so this remains distinguishable
/// from both legitimate identities and the clean "no arrays bound" snapshot.
const INVALIDATED_STATE_IDENTITY_PTR: usize = usize::MAX;

/// Forget the last-seen state identities used by `eval_entry`.
///
/// Some callers temporarily materialize short-lived state arrays whose backing
/// allocations can later be reused for a different logical state. Resetting the
/// thread-local identity cache to a synthetic dirty marker forces the next
/// `eval_entry` call to treat the incoming state as changed and clear
/// state-boundary caches conservatively, even for env-only paths where
/// `state_env`/`next_state_env` are both absent (`0`/`0`).
///
/// For callers without ctx access (RAII Drop impls, tests). Prefer
/// `invalidate_state_identity_tracking_with_ctx` when ctx is available.
pub fn invalidate_state_identity_tracking() {
    // Part of #3962: Single TLS access for pointer + generation invalidation.
    STATE_IDENTITY.with(|c| {
        let mut s = c.borrow_mut();
        s.last_state_ptr = INVALIDATED_STATE_IDENTITY_PTR;
        s.last_next_state_ptr = INVALIDATED_STATE_IDENTITY_PTR;
        // Fix #3447: Advance generation counters — primary invalidation mechanism
        s.state_generation = s.state_generation.wrapping_add(1);
        s.next_state_generation = s.next_state_generation.wrapping_add(1);
    });
    // Fix #3939/#3962: Clear CHOOSE caches on state transitions via SMALL_CACHES.
    crate::cache::small_caches::SMALL_CACHES.with(|sc| {
        let mut sc = sc.borrow_mut();
        sc.choose_cache.clear();
        sc.choose_deep_cache.clear();
    });
}

/// Part of #3962: Ctx-aware variant that also syncs generation counter
/// shadows on `EvalRuntimeState`. Saves 2 TLS reads per subsequent
/// `enter_eval_boundary` call by keeping shadows current.
///
/// Use from `EvalCtx` methods that have `&self` / `&mut self`.
pub fn invalidate_state_identity_tracking_with_ctx(ctx: &EvalCtx) {
    // Part of #3962: Single TLS access for pointer + generation invalidation.
    STATE_IDENTITY.with(|c| {
        let mut s = c.borrow_mut();
        s.last_state_ptr = INVALIDATED_STATE_IDENTITY_PTR;
        s.last_next_state_ptr = INVALIDATED_STATE_IDENTITY_PTR;
        // Fix #3447: Advance generation counters with shadow sync.
        let new_state_gen = s.state_generation.wrapping_add(1);
        s.state_generation = new_state_gen;
        ctx.runtime_state.state_generation.set(new_state_gen);
        let new_next_gen = s.next_state_generation.wrapping_add(1);
        s.next_state_generation = new_next_gen;
        ctx.runtime_state.next_state_generation.set(new_next_gen);
    });
    // Keep shadow pointers invalidated for defense-in-depth.
    ctx.runtime_state
        .last_state_ptr
        .set(INVALIDATED_STATE_IDENTITY_PTR);
    ctx.runtime_state
        .last_next_state_ptr
        .set(INVALIDATED_STATE_IDENTITY_PTR);
    // Fix #3939/#3962: Clear CHOOSE caches via SMALL_CACHES.
    crate::cache::small_caches::SMALL_CACHES.with(|sc| {
        let mut sc = sc.borrow_mut();
        sc.choose_cache.clear();
        sc.choose_deep_cache.clear();
    });
}

/// Invalidate only the next-state identity pointer.
///
/// Part of #3391: During successor enumeration, the working state (which is
/// bound as the "next state" via `bind_next_state_array_guard`) is mutated
/// in-place between Or-branches and EXISTS iterations via `unbind_to_no_invalidate`.
/// This in-place mutation reuses the same memory address, so the pointer-based
/// identity tracking (`LAST_NEXT_STATE_PTR`) can't detect that the logical
/// state has changed. Invalidating only the next-state pointer forces the next
/// `bind_next_state_array_guard` to treat the state as changed and clear
/// next-state-dependent caches, while preserving valid parent-state caches.
pub fn invalidate_next_state_identity_tracking() {
    STATE_IDENTITY.with(|c| {
        let mut s = c.borrow_mut();
        s.last_next_state_ptr = INVALIDATED_STATE_IDENTITY_PTR;
        // Fix #3447: Advance next-state generation counter
        s.next_state_generation = s.next_state_generation.wrapping_add(1);
    });
}

/// RAII guard that invalidates eval-entry state-identity tracking.
///
/// `new()` invalidates immediately and again on drop for mutable state-binding
/// APIs that switch the active state identity on entry and restore it on exit.
/// `restore_only()` skips the eager invalidation and only invalidates on drop
/// for restore paths like `scope_guard_with_next_state()`.
#[must_use = "if unused, the guard drops immediately and invalidates tracking too early"]
pub(crate) struct StateIdentityGuard;

impl StateIdentityGuard {
    /// Non-ctx version for callers without EvalCtx access (e.g., test helpers).
    /// Production code should prefer `new_with_ctx`.
    #[allow(dead_code)] // Used in tests
    #[inline(always)]
    pub(crate) fn new() -> Self {
        invalidate_state_identity_tracking();
        Self
    }

    /// Part of #3962: Ctx-aware constructor that keeps generation shadows in sync.
    /// Use when the caller has a reference to `EvalCtx`.
    #[inline(always)]
    pub(crate) fn new_with_ctx(ctx: &EvalCtx) -> Self {
        invalidate_state_identity_tracking_with_ctx(ctx);
        Self
    }

    #[inline(always)]
    pub(crate) fn restore_only() -> Self {
        Self
    }
}

impl Drop for StateIdentityGuard {
    fn drop(&mut self) {
        invalidate_state_identity_tracking();
    }
}

#[cfg(test)]
pub(crate) fn state_identity_tracking_snapshot() -> (usize, usize) {
    STATE_IDENTITY.with(|c| {
        let s = c.borrow();
        (s.last_state_ptr, s.last_next_state_ptr)
    })
}

/// Reset state-lookup mode and clear eval-scope caches for array-bound
/// state evaluation (invariants, property init predicates, implied actions).
///
/// This is the **checker-level** boundary helper. It does two things:
/// 1. Resets `state_lookup_mode` to `Current` (defensive — prevents stale
///    `Next` mode from leaking into invariant evaluation after successor gen).
/// 2. Delegates to `clear_for_eval_scope_boundary()` which clears all
///    scope-sensitive caches AND invalidates state-identity tracking.
///
/// Call this after `bind_state_array_guard()` / `bind_next_state_array_guard()`
/// whenever evaluation requires a fresh cache boundary.
///
/// The identity invalidation (inside `clear_for_eval_scope_boundary()`) forces
/// the next `eval_entry()` to detect a state change and fire
/// `CacheEvent::EvalEntry{state_changed=true}`, which clears additional
/// per-entry cache families (SUBST_CACHE trim, scope-id validation, etc.).
///
/// ## Boundary hierarchy
///
/// | Boundary                           | Clears                                |
/// |------------------------------------|---------------------------------------|
/// | `clear_for_state_boundary()`       | Per-state data, retains constants     |
/// | `clear_for_eval_scope_boundary()`  | State + scope + identity + module-ref |
/// | `clear_for_bound_state_eval_scope` | lookup-mode reset + eval-scope clear  |
/// | `clear_for_phase_boundary()`       | Full reset at safety/liveness switch  |
/// | `clear_for_run_reset()`            | Full reset between independent runs   |
///
/// Part of #3469: doc aligned with post-#3447/#3465 implementation.
pub fn clear_for_bound_state_eval_scope(ctx: &EvalCtx) {
    use crate::cache::dep_tracking::StateLookupMode;
    ctx.runtime_state
        .state_lookup_mode
        .set(StateLookupMode::Current);
    crate::cache::lifecycle::clear_for_eval_scope_boundary();
}

/// Clear runtime state for repeated top-level evaluations within an
/// already-bound array-state scope.
///
/// Use this inside per-invariant and per-property replay loops where the
/// arrays are already bound by a guard but each evaluation must start from
/// a clean runtime + cache state.
///
/// Contract:
/// 1. Reset `state_lookup_mode` to `Current` (prevents drift from shared
///    `Rc<EvalRuntimeState>` across cloned contexts).
/// 2. Debug-assert that `op_dep_stack` is empty — a non-empty stack at a
///    top-level replay boundary indicates a leaked dep-tracking frame.
/// 3. Clear eval-scope caches via `clear_for_eval_scope_boundary()`.
///
/// This is intentionally narrower than `clear_for_bound_state_eval_scope`:
/// it does NOT rebind arrays or replace the bound-state entry helper.
///
/// Part of #3465: fixes MCPaxosSmall false positive caused by
/// `state_lookup_mode` drift in same-state invariant replay loops.
pub fn clear_for_state_eval_replay(ctx: &EvalCtx) {
    use crate::cache::dep_tracking::StateLookupMode;
    ctx.runtime_state
        .state_lookup_mode
        .set(StateLookupMode::Current);
    debug_assert!(
        ctx.runtime_state.op_dep_stack.borrow().is_empty(),
        "op_dep_stack must be empty at top-level replay boundary (leaked dep frame)"
    );
    crate::cache::lifecycle::clear_for_eval_scope_boundary();
}

/// Establish the state-identity cache boundary without performing evaluation.
///
/// Extracted from `eval_entry_with()` (Part of #3416) so that clone-based
/// context constructors (`with_state_envs`, `with_next_state`) can establish
/// the same boundary for callers that use `eval()` directly instead of
/// `eval_entry()`.
///
/// Compares `state_env` / `next_state_env` pointer identities against the
/// thread-local last-seen values and dispatches `CacheEvent::EvalEntry` when
/// they differ.
pub(crate) fn enter_eval_boundary(ctx: &EvalCtx) {
    // Fix #3447: Use generation counters instead of pointer identity.
    // Pointer identity is ABA-unsound: allocator recycling reuses addresses
    // for different logical states, causing stale cache hits.
    //
    // Part of #3962: Read generation counters from EvalRuntimeState shadow.
    // Most writers use ctx-aware variants (advance_*_with_ctx) that keep
    // shadows in sync. For the few non-ctx writers (StateIdentityGuard::Drop),
    // we fall back to TLS when the shadow reports no change — this catches
    // stale shadows while avoiding TLS reads on the common (no-change) path.
    let shadow_gen = ctx.runtime_state.state_generation.get();
    let last_gen = ctx.runtime_state.last_state_gen.get();
    let shadow_next_gen = ctx.runtime_state.next_state_generation.get();
    let last_next_gen = ctx.runtime_state.last_next_state_gen.get();

    // Fast path: shadow says state changed — trust it (shadow is always >= TLS
    // because ctx-aware writers update shadow first, and non-ctx writers only
    // advance TLS which we'll catch on the fallback).
    let (state_changed, current_gen) = if shadow_gen != last_gen {
        (true, shadow_gen)
    } else {
        // Shadow says no change — verify against TLS for correctness.
        // This handles the rare case where a non-ctx writer (e.g.,
        // StateIdentityGuard::Drop) advanced TLS without syncing shadow.
        // Part of #3962: Single TLS access for the consolidated struct.
        let tls_gen = STATE_IDENTITY.with(|c| c.borrow().state_generation);
        if tls_gen != last_gen {
            // TLS was advanced by a non-ctx writer. Sync shadow.
            ctx.runtime_state.state_generation.set(tls_gen);
            (true, tls_gen)
        } else {
            (false, last_gen)
        }
    };

    let (next_state_changed, current_next_gen) = if shadow_next_gen != last_next_gen {
        (true, shadow_next_gen)
    } else {
        let tls_next_gen = STATE_IDENTITY.with(|c| c.borrow().next_state_generation);
        if tls_next_gen != last_next_gen {
            ctx.runtime_state.next_state_generation.set(tls_next_gen);
            (true, tls_next_gen)
        } else {
            (false, last_next_gen)
        }
    };

    on_cache_event(CacheEvent::EvalEntry {
        // Keep pointer values for diagnostics / CacheEvent consumers
        state_ptr: ctx.state_env.map_or(0, |s| s.identity()),
        next_state_ptr: ctx.next_state_env.map_or(0, |s| s.identity()),
        state_changed,
        next_state_changed,
    });

    if state_changed {
        ctx.runtime_state.last_state_gen.set(current_gen);
        // Keep pointer tracking in sync for defense-in-depth
        let state_id = ctx.state_env.map_or(0, |s| s.identity());
        ctx.runtime_state.last_state_ptr.set(state_id);
        // Sync TLS shadows for defense-in-depth (test observability)
        STATE_IDENTITY.with(|c| {
            let mut s = c.borrow_mut();
            s.last_state_gen = current_gen;
            s.last_state_ptr = state_id;
        });
    }
    if state_changed || next_state_changed {
        ctx.runtime_state.last_next_state_gen.set(current_next_gen);
        let next_id = ctx.next_state_env.map_or(0, |s| s.identity());
        ctx.runtime_state.last_next_state_ptr.set(next_id);
        // Sync TLS shadows for defense-in-depth (test observability)
        STATE_IDENTITY.with(|c| {
            let mut s = c.borrow_mut();
            s.last_next_state_gen = current_next_gen;
            s.last_next_state_ptr = next_id;
        });
    }
}

/// External entry point for non-AST evaluators that need `eval_entry()` cache lifecycle.
///
/// This is the generic form of [`eval_entry`]: it establishes the same cache
/// boundary and panic-safety guard, then delegates the actual evaluation to
/// `eval_fn`. Use this for alternate top-level evaluators like TIR named-op
/// execution that do not have an AST expression to pass to [`eval_entry`].
pub fn eval_entry_with<T>(ctx: &EvalCtx, eval_fn: impl FnOnce() -> EvalResult<T>) -> EvalResult<T> {
    enter_eval_boundary(ctx);

    // Fix #2260 / #2413: Arm a panic-safety guard for SUBST_CACHE.
    // If evaluation panics (caught by catch_unwind in parallel workers),
    // the guard clears stale substitution entries. On success we disarm
    // so that on_cache_event(EvalExit) handles the normal trim path.
    let mut subst_guard = SubstCacheGuard::new();

    let result = eval_fn();

    subst_guard.disarm();
    // Part of #3962: Use shadow eval_exit_count on EvalRuntimeState instead
    // of the EVAL_EXIT_COUNT thread-local. Saves 1 TLS access per eval_entry.
    // The trim interval (128) matches lifecycle.rs TRIM_INTERVAL.
    // Calls trim_eval_entry_caches() directly, bypassing on_cache_event(EvalExit)
    // which has its own redundant TLS-based counter.
    let count = ctx.runtime_state.eval_exit_count.get().wrapping_add(1);
    ctx.runtime_state.eval_exit_count.set(count);
    if count % 128 == 0 {
        trim_eval_entry_caches();
    }
    result
}

/// External entry point for evaluation. Manages cache lifecycle.
///
/// Part of #250: Eliminates IN_EVAL thread-local from hot path.
/// External callers (check.rs, enumerate.rs, liveness/checker.rs) use this.
/// Recursive calls within eval use eval() directly.
///
/// Call this from top-level evaluation entry points:
/// - Action evaluation (check.rs)
/// - Constraint evaluation (enumerate.rs)
/// - Property evaluation (liveness/checker.rs)
pub fn eval_entry(ctx: &EvalCtx, expr: &Spanned<tla_core::ast::Expr>) -> EvalResult<Value> {
    eval_entry_with(ctx, || eval(ctx, expr))
}

/// Lightweight external entry point for evaluation within a stable cache boundary.
///
/// Unlike [`eval_entry`], this skips state-identity tracking and lifecycle event
/// dispatch. Callers must only use it after they have already established the
/// correct cache boundary for the currently bound `state_env` / `next_state_env`.
///
/// Panic safety is still preserved for `SUBST_CACHE`: a single inline leaf eval
/// should not be able to leave stale substitution entries behind if evaluation
/// unwinds.
pub fn eval_entry_inline(ctx: &EvalCtx, expr: &Spanned<tla_core::ast::Expr>) -> EvalResult<Value> {
    let mut subst_guard = SubstCacheGuard::new();
    let result = eval(ctx, expr);
    subst_guard.disarm();
    result
}

/// Force a lazy thunk if the value is a zero-arg Closure (LET binding).
///
/// Fix #562: TLC uses LazyValue for zero-arg LET definitions, evaluated only when referenced.
/// TLA2 uses Value::Closure with empty params as the lazy thunk representation.
/// This function forces the thunk by evaluating it in its captured context.
///
/// Part of #607: TLC caches forced LazyValue results (Tool.java:612). We use OnceLock
/// to ensure the body is evaluated at most once per closure instance.
///
/// Fix #1498: When inside dep tracking, the thunk's deps are recorded in THUNK_DEP_CACHE
/// on first force, and propagated from the cache on subsequent hits. Without this,
/// a cache-hit thunk could report zero deps, causing incorrect constant
/// classification of the enclosing operator (Fix #2462: now validated in ZERO_ARG_OP_CACHE).
///
/// TLA+ syntax doesn't allow zero-arg LAMBDAs, so empty-params Closure is unambiguous.
///
/// Takes `Value` by value to avoid a redundant clone on the non-closure fast path.
/// When the value is NOT a zero-arg Closure (the overwhelmingly common case for
/// heap-allocated values like strings, sets, records), ownership passes through
/// without any cloning. Previously took `&Value` and cloned unconditionally on
/// the non-closure exit path — an unnecessary allocation for every non-closure
/// heap binding access.
#[inline]
pub(crate) fn force_lazy_thunk_if_needed(ctx: &EvalCtx, v: Value) -> EvalResult<Value> {
    if let Value::Closure(ref c) = v {
        if c.params().is_empty() {
            // Part of #607: Return cached value if already forced.
            // Fix #3447: Skip the OnceLock cache when stored deps indicate
            // INSTANCE lazy-read taint — the cached value may be state-dependent
            // and stale across BFS steps.
            if let Some(cached) = c.cached_value() {
                if !thunk_has_instance_lazy_taint(c.id()) {
                    propagate_thunk_deps(ctx, c.id());
                    return Ok(cached);
                }
                // Tainted: fall through to re-evaluate
            }

            // Build context from captured environment (mirrors build_closure_ctx)
            // Part of #2895/#2989: Restore captured BindingChain directly in O(1).
            // The chain is the sole source of truth for local bindings.
            let force_ctx = {
                let mut fctx = ctx.clone();
                {
                    let s = fctx.stable_mut();
                    s.env = Arc::clone(c.env_arc());
                    s.local_ops = c.local_ops().cloned();
                    // Part of #3099: Invalidate scope_ids.local_ops since we replaced
                    // local_ops with the closure's captured ops during lazy thunk forcing.
                    s.scope_ids.local_ops = crate::cache::scope_ids::INVALIDATED;
                }
                // Fix #2761: Reset BindingChain when forcing lazy thunks. Same rationale as
                // build_closure_ctx (Fix #2741) — the chain from the forcing site carries stale
                // bindings that shadow captured definition-site bindings.
                let (bindings, binding_depth) = restore_captured_binding_chain(
                    c.captured_chain(),
                    c.captured_chain_depth(),
                    "force_lazy_thunk_if_needed",
                    Some(c.body().span),
                )?;
                fctx.bindings = bindings;
                fctx.binding_depth = binding_depth;
                fctx
            };

            let tracking = is_dep_tracking_active(ctx);
            let guard = if tracking {
                let base_stack_len = force_ctx.binding_depth;
                Some(super::OpDepGuard::from_ctx(&force_ctx, base_stack_len))
            } else {
                None
            };

            let result = eval(&force_ctx, c.body());

            let mut has_instance_taint = false;
            if let Some(guard) = guard {
                let deps = guard.try_take_deps();
                if result.is_ok() {
                    let deps = deps.ok_or_else(|| EvalError::Internal {
                        message: "dep stack empty in thunk force".into(),
                        span: Some(c.body().span),
                    })?;
                    has_instance_taint = deps.instance_lazy_read;
                    store_thunk_deps(c.id(), &deps);
                    super::propagate_cached_deps(ctx, &deps);
                }
            }

            let result = result?;

            // Part of #607: Cache the result for subsequent accesses.
            // Fix #3447: Skip OnceLock caching when the thunk read INSTANCE lazy
            // bindings — the result is state-dependent and must be re-evaluated.
            // Fix #3465: Also skip caching when dep tracking was not active.
            // Without tracking, instance_lazy_read taint cannot be detected, so
            // has_instance_taint stays false even for INSTANCE-tainted thunks.
            // Caching such results causes false positives on INSTANCE-heavy specs
            // (MCPaxosSmall) when the stale value is reused in a different state.
            if tracking && !has_instance_taint {
                c.cache_value(result.clone());
            }

            return Ok(result);
        }
    }
    // Non-closure or non-thunk closure: pass through without cloning.
    Ok(v)
}
