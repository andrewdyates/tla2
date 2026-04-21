// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Cache infrastructure for module reference resolution.
//!
//! Contains cache types, thread-local statics, and lifecycle functions
//! for INSTANCE WITH substitution caching.
//!
//! Part of #1643 (module_ref.rs decomposition).
//!
//! ## Cache Lifecycle Contract (Part of #2376, #2413)
//!
//! All caches in this module follow the unified lifecycle contract from
//! `crates/tla-eval/src/cache/lifecycle.rs`. Events are dispatched via
//! `on_cache_event(CacheEvent)`.
//!
//! | Cache | Lifecycle | Clear trigger | Bound |
//! |---|---|---|---|
//! | `CHAINED_REF_CACHE` | PerRun | RunReset, TestReset, PhaseBoundary | 10K soft cap (cliff) |
//! | `MODULE_REF_SCOPE_CACHE` | PerRun | RunReset, TestReset, PhaseBoundary | 10K soft cap (cliff) |
//! | `EAGER_BINDINGS_CACHE` | PerState | State change (full), next-state change (selective) | 10K soft cap (cliff) |
//!
//! **Clear path:** `clear_run_reset_impl()` → `clear_module_ref_caches()` clears all three.
//! **Trim path:** `trim_eval_entry_caches()` → `trim_module_ref_caches()` on every EvalExit.
//! **Selective eviction:** `evict_next_state_eager_bindings()` retains `is_next_mode=false` entries.

use super::super::{
    current_state_lookup_mode, eval_with_dep_tracking, EvalCtx, EvalResult, InstanceInfo, OpEnv,
    OpEvalDeps, StateLookupMode, SubstGuardEntry,
};
use crate::binding_chain::BindingChain;
use crate::value::Value;
use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::sync::Arc;
use tla_core::ast::Substitution;
use tla_core::name_intern::{intern_name, NameId};

// === Cache Types ===

#[derive(Clone)]
pub(super) struct ChainedRefCacheEntry {
    pub(super) instance_info: InstanceInfo,
    pub(super) merged_local_ops: Arc<OpEnv>,
    /// Pre-wrapped Arc for instance_substitutions, reused across eval_entry calls.
    /// Stabilizes the Arc pointer so SUBST_CACHE keys match across calls.
    pub(super) instance_subs_arc: Arc<Vec<Substitution>>,
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub(super) struct ChainedRefCacheKey {
    shared_id: u64,
    local_ops_id: usize,
    instance_subs_id: usize,
    chain_key: String,
}

// Part of #3962: Consolidated CHAINED_REF_CACHE + MODULE_REF_SCOPE_CACHE +
// EAGER_BINDINGS_CACHE + PARAM_SUBS_CACHE into a single TLS struct.
// Previously 4 separate `thread_local!` declarations — each access was a
// separate `_tlv_get_addr` call on macOS (~5ns each). All four caches are
// cleared together in `clear_module_ref_caches()` and accessed during
// INSTANCE WITH resolution. Now 1 TLS access covers all four.
//
// Part of #3962: PARAM_SUBS_CACHE (previously in module_ref.rs) consolidated
// here. It stores pre-allocated Arc<Vec<Substitution>> for parametrized
// INSTANCE callsites, keyed by AST pointer identity. PerRun lifecycle.
pub(super) struct ModuleRefCaches {
    pub(super) chained_ref: FxHashMap<ChainedRefCacheKey, ChainedRefCacheEntry>,
    pub(super) module_ref_scope: FxHashMap<ModuleRefScopeKey, ModuleRefScopeEntry>,
    pub(super) eager_bindings: EagerBindingsMap,
    /// Part of #3962: Consolidated from standalone PARAM_SUBS_CACHE thread_local.
    /// Cache for parametrized INSTANCE substitution Arcs (Part of #2980).
    /// Key: param_exprs.as_ptr() as usize (AST Vec data pointer, stable per callsite).
    /// Value: pre-allocated Arc<Vec<Substitution>> reused across evaluations.
    /// Lifecycle: PerRun. Bounded: one entry per parametrized INSTANCE callsite.
    pub(super) param_subs: FxHashMap<usize, Arc<Vec<Substitution>>>,
}

std::thread_local! {
    #[allow(clippy::missing_const_for_thread_local)] // FxHashMap::default() is not const
    pub(super) static MODULE_REF_CACHES: RefCell<ModuleRefCaches> =
        RefCell::new(ModuleRefCaches {
            chained_ref: FxHashMap::default(),
            module_ref_scope: FxHashMap::default(),
            eager_bindings: FxHashMap::default(),
            param_subs: FxHashMap::default(),
        });
}

/// Cache for non-chained `eval_module_ref` scope construction.
///
/// Fix #2364: `eval_module_ref` calls `compose_substitutions` and creates a new
/// `Arc<Vec<Substitution>>` on every call, even when the result is identical.
/// This makes SUBST_CACHE keys unstable across eval_entry calls.
///
/// Cache key: (shared_id, instance_name hash, op_name hash, outer instance_subs_id)
/// Cache value: pre-wrapped Arc for the composed substitutions + merged local_ops
#[derive(Clone)]
pub(super) struct ModuleRefScopeEntry {
    pub(super) effective_subs_arc: Arc<Vec<Substitution>>,
    pub(super) local_ops_arc: Arc<OpEnv>,
}

#[derive(Clone, Hash, PartialEq, Eq)]
#[allow(clippy::struct_field_names)]
pub(super) struct ModuleRefScopeKey {
    pub(super) shared_id: u64,
    pub(super) instance_name_id: NameId,
    pub(super) outer_subs_id: usize,
    pub(super) outer_local_ops_id: usize,
}

/// Cache for eagerly-evaluated substitution bindings within the same state.
///
/// Fix #2364: `build_eager_subst_bindings` re-evaluates ALL substitution RHS expressions
/// on every `eval_module_ref` / `eval_chained_module_ref` call, even when the same
/// INSTANCE scope is accessed multiple times for the same state (e.g., checking
/// invariants, constraints, and properties all reference EWD998Chan!...).
///
/// Key: (subs_ptr, local_ops_ptr, state_ptr, next_state_ptr, is_next_mode)
/// Value: pre-evaluated eager bindings Arc
///
/// Uses Arc pointer identity for scope identification, which works for both
/// non-chained (MODULE_REF_SCOPE_CACHE-backed Arcs) and chained
/// (CHAINED_REF_CACHE-backed Arcs) paths. Both caches provide stable Arc
/// pointers across eval_entry calls.
///
/// Fix #2364: When `is_next_mode=false`, `next_state_ptr` is set to 0 because
/// substitution RHS expressions in Current mode only read current state variables.
/// This allows cache hits across transitions from the same source state, even when
/// the next_state changes. Combined with selective eviction (retaining
/// `is_next_mode=false` entries when only next_state_changed), this reduces
/// EAGER_BINDINGS_CACHE rebuilds from N_transitions to N_from_states.
#[derive(Clone, Hash, PartialEq, Eq)]
pub(super) struct EagerBindingsKey {
    /// Arc pointer identity for the effective substitutions.
    subs_ptr: usize,
    /// Arc pointer identity for the local_ops scope.
    local_ops_ptr: usize,
    /// Fix #3447: State generation counter — monotonically increasing, no ABA.
    /// Replaces `state_ptr: usize` which was vulnerable to allocator recycling.
    state_gen: u64,
    /// Fix #3447: Next-state generation counter. Set to 0 when `is_next_mode=false`
    /// because Current-mode substitutions don't depend on next_state.
    next_state_gen: u64,
    /// Current state lookup mode (Current vs Next). Substitution RHS expressions
    /// read state variables, which resolve differently depending on the mode.
    is_next_mode: bool,
    /// Part of #2980: Content hash of parametrized INSTANCE argument values.
    ///
    /// When a parametrized INSTANCE like `P(Succ) == INSTANCE M` is called via
    /// `\A Succ \in SuccSet : P(Succ)!Op`, the `PARAM_SUBS_CACHE` reuses the same
    /// Arc pointer across all iterations (for scope cache efficiency). This hash
    /// disambiguates cache entries by the actual argument values, preventing stale
    /// cache hits when the same callsite is invoked with different arguments.
    ///
    /// Zero when no parametrized INSTANCE is active (non-parametrized callers).
    param_args_hash: u64,
}

pub(super) type EagerBindingsMap = FxHashMap<EagerBindingsKey, Arc<Vec<(NameId, Value, OpEvalDeps)>>>;


// === Cache Key Helpers ===

/// Build an `EagerBindingsKey` with correct next-state handling.
///
/// Fix #3447: Uses monotonic generation counters instead of pointer identity.
/// Pointer identity is ABA-unsound: allocator recycling reuses addresses for
/// different logical states, causing stale cache hits.
///
/// Fix #2364: When `is_next_mode=false`, sets `next_state_gen` to 0 because
/// Current-mode substitution RHS expressions don't read next_state variables.
/// This enables cache hits across transitions from the same source state.
pub(super) fn eager_bindings_key(
    ctx: &EvalCtx,
    subs_ptr: usize,
    local_ops_ptr: usize,
) -> EagerBindingsKey {
    use crate::eval_cache_lifecycle::{current_next_state_gen_ctx, current_state_gen_ctx};
    let is_next_mode = current_state_lookup_mode(ctx) == StateLookupMode::Next;
    EagerBindingsKey {
        subs_ptr,
        local_ops_ptr,
        // Fix #3447: Use monotonic generation counters instead of pointer identity.
        // Part of #3962: Read from EvalRuntimeState shadow instead of TLS.
        state_gen: current_state_gen_ctx(ctx),
        // In Current mode, substitution RHS only reads current state.
        // Set next_state_gen=0 so the key doesn't vary with next_state transitions.
        next_state_gen: if is_next_mode {
            current_next_state_gen_ctx(ctx)
        } else {
            0
        },
        is_next_mode,
        // Part of #2980: Include parametrized arg hash for cache correctness.
        param_args_hash: ctx.stable.param_args_hash,
    }
}

pub(super) fn chained_ref_cache_key(ctx: &EvalCtx, chain_key: String) -> ChainedRefCacheKey {
    let local_ops_id = ctx
        .local_ops
        .as_ref()
        .map_or(0, |local_ops| Arc::as_ptr(local_ops) as usize);
    let instance_subs_id = ctx
        .instance_substitutions
        .as_ref()
        .map_or(0, |subs| Arc::as_ptr(subs) as usize);
    ChainedRefCacheKey {
        shared_id: ctx.shared.id,
        local_ops_id,
        instance_subs_id,
        chain_key,
    }
}

// === Cache Lifecycle ===

/// Selectively evict EAGER_BINDINGS_CACHE entries that depend on next_state.
///
/// Fix #2364: When only next_state_changed, retain entries with `is_next_mode=false`.
/// These entries only depend on current state (unchanged) and have `next_state_ptr=0`
/// in their key, so they're safe to keep.
pub fn evict_next_state_eager_bindings() {
    MODULE_REF_CACHES.with(|c| c.borrow_mut().eager_bindings.retain(|k, _| !k.is_next_mode));
}

/// Clear module reference scope caches for test isolation.
///
/// These caches store structural data (composed substitutions, merged local_ops)
/// that is independent of state values but may become stale between test runs
/// when shared_id is reused.
/// Part of #3962: Single TLS access clears all 4 caches (was 2 before —
/// MODULE_REF_CACHES + separate PARAM_SUBS_CACHE).
pub fn clear_module_ref_caches() {
    MODULE_REF_CACHES.with(|c| {
        let mut caches = c.borrow_mut();
        caches.chained_ref.clear();
        caches.module_ref_scope.clear();
        caches.eager_bindings.clear();
        // Part of #2980/#3962: Parametrized INSTANCE substitution Arc cache,
        // now consolidated into MODULE_REF_CACHES.
        caches.param_subs.clear();
    });
}

/// Clear only the eager bindings cache (state-dependent substitution results).
///
/// Called by `eval_entry` on state change to prevent unbounded growth.
/// Scope caches (chained_ref, module_ref_scope) are NOT cleared
/// because they are state-independent and provide stable Arc pointers.
pub fn clear_eager_bindings_cache() {
    MODULE_REF_CACHES.with(|c| c.borrow_mut().eager_bindings.clear());
}

// Part of #2413 U6: Soft caps for PerRun module-ref caches.
const CHAINED_REF_CACHE_SOFT_CAP: usize = 10_000;
const MODULE_REF_SCOPE_CACHE_SOFT_CAP: usize = 10_000;
const EAGER_BINDINGS_CACHE_SOFT_CAP: usize = 10_000;

/// Trim module-ref caches when they exceed soft caps.
///
/// Part of #2413: Called from `trim_eval_entry_caches` on every `EvalExit`.
/// Uses cliff eviction (full clear on exceeding cap). Note: main lifecycle
/// caches migrated to retain-half (#3025); module-ref caches not yet migrated.
pub fn trim_module_ref_caches() {
    MODULE_REF_CACHES.with(|c| {
        let caches = c.borrow();
        let chained_over = caches.chained_ref.len() > CHAINED_REF_CACHE_SOFT_CAP;
        let scope_over = caches.module_ref_scope.len() > MODULE_REF_SCOPE_CACHE_SOFT_CAP;
        let eager_over = caches.eager_bindings.len() > EAGER_BINDINGS_CACHE_SOFT_CAP;
        drop(caches);
        if chained_over || scope_over || eager_over {
            let mut caches = c.borrow_mut();
            if chained_over {
                caches.chained_ref.clear();
            }
            if scope_over {
                caches.module_ref_scope.clear();
            }
            if eager_over {
                caches.eager_bindings.clear();
            }
        }
    });
}

// === Eager Bindings Builder ===

/// Fix #2364: Eagerly evaluate substitution RHS values at INSTANCE scope entry.
///
/// Returns a Vec of (NameId, Value, OpEvalDeps) triples. eval_ident and eval_state_var
/// use these to bypass SUBST_CACHE entirely: matching names return the pre-computed
/// value directly, and deps are propagated for zero-arg op cache correctness.
///
/// Only used for chained INSTANCE refs (A!B!C). Non-chained INSTANCE uses lazy
/// substitution bindings via `build_lazy_subst_bindings` (#2991).
pub(super) fn build_eager_subst_bindings(
    ctx: &EvalCtx,
    subs: &[Substitution],
) -> EvalResult<Vec<(NameId, Value, OpEvalDeps)>> {
    let mut result = Vec::with_capacity(subs.len());
    for sub in subs {
        let name_id = intern_name(sub.from.node.as_str());
        // Use recursion guard to prevent self-reference while keeping
        // the parent Arc pointer stable for cache key consistency (fix #2364).
        let _guard = SubstGuardEntry::new(name_id);
        let mut c = ctx.clone();
        c.stable_mut().eager_subst_bindings = None;
        c.bindings = BindingChain::empty();
        let (value, deps) = eval_with_dep_tracking(&c, &sub.to)?;
        result.push((name_id, value, deps));
    }
    Ok(result)
}

#[cfg(test)]
#[path = "module_ref_cache_tests.rs"]
mod tests;
