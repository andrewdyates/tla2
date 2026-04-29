// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! INSTANCE substitution cache and recursion guards.
//!
//! Lifecycle class: PerState (cleared when state_env pointer changes).
//! Bounded: soft cap 10K (retain-half eviction in lifecycle.rs).
//! Panic-safe: SubstCacheGuard in eval_entry clears on unwind.
//!
//! Part of #2744 decomposition from eval_cache.rs.

use super::dep_tracking::OpEvalDeps;
use crate::EvalCtx;
use rustc_hash::FxHashMap;
use tla_core::name_intern::NameId;

// Thread-local cache for INSTANCE substitution evaluation within a single top-level `eval` call.
//
// INSTANCE substitutions like `inbox <- Node2Nat(EWD998ChanInbox)` can be referenced many times
// within a single action predicate evaluation (e.g., `inbox[0]`, `Len(inbox[0])`, ...). Without
// caching, we end up re-evaluating the substitution RHS repeatedly which can be extremely costly.
/// Cached INSTANCE substitution result with dependency tracking.
///
/// Fix #2364: Stores deps alongside the value so that SUBST_CACHE hits can
/// propagate dependencies to the enclosing dep tracking frame. Without this,
/// operators like `tpos` (which reads `inbox` via INSTANCE substitution) appear
/// to have no deps when the substitution result is cached, causing incorrect
/// classification as constant in ZERO_ARG_OP_CACHE.
#[derive(Clone)]
pub(crate) struct SubstCacheEntry {
    pub(crate) value: crate::value::Value,
    pub(crate) deps: OpEvalDeps,
}

/// Part of #3099: `local_ops_id` and `instance_subs_id` are now stable u64
/// content-based fingerprints computed at scope construction time, replacing
/// the previous `Arc::as_ptr() as usize` pattern that produced different keys
/// for logically identical scopes.
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub(crate) struct SubstCacheKey {
    pub(crate) is_next_state: bool,
    pub(crate) name_id: NameId,
    pub(crate) shared_id: u64,
    pub(crate) local_ops_id: u64,
    pub(crate) instance_subs_id: u64,
    pub(crate) chained_ref_eval: bool,
}

#[inline]
pub(crate) fn subst_cache_key(
    ctx: &EvalCtx,
    is_next_state: bool,
    name_id: NameId,
) -> SubstCacheKey {
    use super::scope_ids::{resolve_instance_subs_id, resolve_local_ops_id};
    let local_ops_id = resolve_local_ops_id(ctx.scope_ids.local_ops, &ctx.local_ops);
    let instance_subs_id = resolve_instance_subs_id(
        ctx.scope_ids.instance_substitutions,
        &ctx.instance_substitutions,
    );
    SubstCacheKey {
        is_next_state,
        name_id,
        shared_id: ctx.shared.id,
        local_ops_id,
        instance_subs_id,
        chained_ref_eval: ctx.chained_ref_eval,
    }
}

// Part of #3805: Consolidated SUBST_CACHE + SUBST_EVAL_GUARD into a single TLS
// struct. Previously 2 separate `thread_local!` declarations — each access was a
// separate `_tlv_get_addr` call on macOS. Now a single TLS access covers both
// the substitution cache and the recursion guard.
pub(crate) struct SubstState {
    pub(crate) cache: FxHashMap<SubstCacheKey, SubstCacheEntry>,
    /// Fix #2364: Recursion guard for substitution evaluation.
    /// Prevents infinite loops when evaluating a substitution RHS that references
    /// the same substituted variable.
    pub(crate) eval_guard: Vec<NameId>,
}

std::thread_local! {
    pub(crate) static SUBST_STATE: std::cell::RefCell<SubstState> =
        std::cell::RefCell::new(SubstState {
            cache: FxHashMap::default(),
            eval_guard: Vec::new(),
        });
}

// Legacy aliases for callers that reference SUBST_CACHE directly.
// These wrapper functions provide the same interface as the old thread_local.
// The actual data now lives inside SUBST_STATE.

/// Check if a name is in the substitution evaluation guard.
/// Part of #3805: Uses consolidated SUBST_STATE.
#[inline]
pub(crate) fn is_subst_guarded(name_id: NameId) -> bool {
    SUBST_STATE.with(|s| s.borrow().eval_guard.contains(&name_id))
}

/// RAII guard that pushes a name to the substitution evaluation guard on creation
/// and pops it on drop (including during panic unwind).
pub(crate) struct SubstGuardEntry {
    name_id: NameId,
}

impl SubstGuardEntry {
    #[inline]
    pub(crate) fn new(name_id: NameId) -> Self {
        SUBST_STATE.with(|s| s.borrow_mut().eval_guard.push(name_id));
        SubstGuardEntry { name_id }
    }
}

impl Drop for SubstGuardEntry {
    fn drop(&mut self) {
        SUBST_STATE.with(|s| {
            let mut state = s.borrow_mut();
            if let Some(pos) = state.eval_guard.iter().rposition(|id| *id == self.name_id) {
                state.eval_guard.remove(pos);
            }
        });
    }
}

/// Clear the substitution evaluation guard (for cache clearing / test isolation).
/// Part of #3805: Uses consolidated SUBST_STATE.
pub(crate) fn clear_subst_guard() {
    SUBST_STATE.with(|s| s.borrow_mut().eval_guard.clear());
}

/// RAII guard that clears `SUBST_CACHE` on panic unwind only.
///
/// Fix #2260: `eval_entry` delegates cache lifecycle to `on_cache_event`, but if `eval()`
/// panics and the panic is caught by `catch_unwind` in a parallel worker, `EvalExit` never
/// fires, leaving stale INSTANCE substitution results for the next top-level evaluation on
/// that thread — a soundness violation.
///
/// Semantics (per #2413 design):
/// 1. On creation: arm the guard (no cache clear — `on_cache_event(EvalEntry)` handles that).
/// 2. On success: caller calls `disarm()` to preserve intended cache persistence.
/// 3. On unwind (drop without disarm): clear `SUBST_CACHE` for panic safety.
///
/// Pattern mirrors `OpDepGuard` (fix #1548).
pub(crate) struct SubstCacheGuard {
    armed: bool,
}

impl SubstCacheGuard {
    /// Arm a guard that will clear SUBST_CACHE on drop (panic path only).
    pub(crate) fn new() -> Self {
        SubstCacheGuard { armed: true }
    }

    /// Disarm the guard on the success path. After this, drop is a no-op.
    pub(crate) fn disarm(&mut self) {
        self.armed = false;
    }
}

impl Drop for SubstCacheGuard {
    fn drop(&mut self) {
        if self.armed {
            // Panic-safety path: clear stale substitution cache entries.
            SUBST_STATE.with(|s| s.borrow_mut().cache.clear());
        }
    }
}

/// Clear only the INSTANCE substitution cache.
///
/// Use this when a caller needs to prevent stale substitution reuse across
/// explicit environment switches but must preserve other state caches for
/// performance.
/// Part of #3805: Uses consolidated SUBST_STATE.
pub fn clear_subst_cache() {
    SUBST_STATE.with(|s| s.borrow_mut().cache.clear());
}

/// Evict SUBST_CACHE entries that depend on next-state, retaining current-state entries.
///
/// Fix #2364: When only `next_state_changed` (not `state_changed`), entries with
/// `is_next_state=false` only depend on the current state_env, which hasn't changed.
/// Retaining them avoids re-evaluating INSTANCE substitution chains (e.g., 3-level
/// EWD998ChanID chains) on every transition from the same source state.
/// Part of #3805: Uses consolidated SUBST_STATE.
#[inline]
pub fn evict_next_state_subst_entries() {
    SUBST_STATE.with(|s| s.borrow_mut().cache.retain(|k, _| !k.is_next_state));
}
