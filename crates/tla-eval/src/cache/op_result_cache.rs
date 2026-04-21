// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! User-defined operator result cache with TLC-style subset validation.
//!
//! Contains CachedOpResult/op_cache_entry_valid (shared by NARY and ZERO_ARG caches)
//! and the N-ary operator result cache (NARY_OP_CACHE, NARY_PERSISTENT_CACHE).
//! Part of #3025: OP_RESULT_CACHE removed (zero insertions after Phase 1).
//!
//! Part of #2744 decomposition from eval_cache.rs.

use super::dep_tracking::{current_state_lookup_mode, OpEvalDeps, StateLookupMode};
use super::zero_arg_cache::deps_are_persistent;
use crate::value::Value;
use crate::var_index::VarIndex;
use crate::EvalCtx;
use rustc_hash::FxHashMap;
use std::sync::Arc;
use tla_core::name_intern::{intern_name, NameId};

// Specs like bosco have guards that call the same operator multiple times with the same arguments:
//   rcvd01(self) >= N - T /\ rcvd0(self) >= moreNplus3Tdiv2 /\ rcvd0(self) < moreNplus3Tdiv2
//
// Each call to `rcvd0(self)` evaluates `Cardinality({m \in rcvd'[self] : m[2] = "ECHO0"})` which
// iterates over all elements in rcvd'[self]. Caching avoids redundant evaluations.
//
// Baseline alignment:
// TLC caches evaluation results via LazyValue and validates cache hits with
// `TLCState.isSubset(s0, cachedS0)` / `TLCState.isSubset(s1, cachedS1)`, rather than requiring
// an exact match on the full state.
//
// In Rust we implement a *sound* subset-style cache by tracking the concrete dependencies
// (state vars, next-state vars, and captured locals) actually read during evaluation, and
// reusing a cached value only when all recorded dependencies still match the current context.

// Part of #3025: OpResultCacheKey removed — was only used by the dead OP_RESULT_CACHE.
// NaryOpCacheKey (below) is the active cache key type for n-ary operators.

/// Cached operator result with TLC-style subset validation.
#[derive(Clone)]
pub(crate) struct CachedOpResult {
    pub(crate) value: Value,
    pub(crate) deps: OpEvalDeps,
}

/// Part of #3579: Compact variant of `next_mode_dep_matches` that accepts
/// `&CompactValue` from the new VarDepMap storage, avoiding Value reconstruction.
fn next_mode_dep_matches_compact(
    ctx: &EvalCtx,
    idx: VarIndex,
    expected: &tla_value::CompactValue,
) -> bool {
    let name = ctx.var_registry().name(idx);
    let name_id = intern_name(name);

    if let Some((bv, source)) = ctx.bindings.lookup(name_id) {
        if bv.matches_compact(StateLookupMode::Current, source, expected) {
            return true;
        }
    }

    if let Some(sparse_env) = ctx.sparse_next_state_env {
        // SAFETY: idx bounded by VarRegistry.
        let slot = unsafe { sparse_env.get_unchecked(idx.as_usize()) };
        if let Some(actual) = slot {
            return expected.matches_value(actual);
        }
    }

    if let Some(state_env) = ctx.state_env {
        debug_assert!(idx.as_usize() < state_env.env_len());
        // SAFETY: dependency indices are recorded from validated VarRegistry lookups.
        return unsafe { state_env.slot_matches_compact(idx.as_usize(), expected) };
    }

    // Cold path: convert CompactValue to Value for env HashMap lookup.
    let expected_val = Value::from(expected);
    ctx.env
        .get(name)
        .is_some_and(|actual| actual == &expected_val)
}

pub(crate) fn op_cache_entry_valid(ctx: &EvalCtx, entry: &CachedOpResult) -> bool {
    if entry.deps.inconsistent {
        return false;
    }
    // Validate captured locals by NameId against the *current* BindingChain.
    // Part of #2955: Use BindingChain lookup instead of local_stack scan.
    for (name_id, expected) in &entry.deps.local {
        let matches = ctx.bindings.lookup(*name_id).is_some_and(|(bv, source)| {
            // Part of #3579: eager locals and recorded local deps are both
            // CompactValue, so cache validation can compare directly.
            bv.matches_compact(StateLookupMode::Current, source, expected)
        });
        if !matches {
            return false;
        }
    }
    // Validate state deps against the current state array.
    // Issue #73: Only require state_env if there are state dependencies — allows caching
    // pure operators (e.g., IsStronglyConnected) during Init where state_env is None.
    if !entry.deps.state.is_empty() {
        let Some(state_env) = ctx.state_env else {
            return false;
        };
        for (idx, expected) in entry.deps.state.iter() {
            debug_assert!(idx.as_usize() < state_env.env_len());
            // SAFETY: cached dependency indices originate from this model's VarRegistry.
            // Part of #3579: VarDepMap now stores CompactValue; slot_matches_compact
            // compares directly without Value materialization on either side.
            if !unsafe { state_env.slot_matches_compact(idx.as_usize(), expected) } {
                return false;
            }
        }
    }
    // Fix #3062: Validate TLCGet("level") dependency.
    // If the cached evaluation read TLCGet("level"), the cache entry is only valid
    // when the current BFS level matches the recorded level.
    if let Some(cached_level) = entry.deps.tlc_level {
        if ctx.tlc_level != cached_level {
            return false;
        }
    }
    // Validate next-state deps (if any) against whatever next-state context is available.
    if !entry.deps.next.is_empty() {
        if let Some(next_env) = ctx.next_state_env {
            for (idx, expected) in entry.deps.next.iter() {
                debug_assert!(idx.as_usize() < next_env.env_len());
                // SAFETY: dependency indices are recorded from validated VarRegistry lookups.
                // Part of #3579: slot_matches_compact for CompactValue dep storage.
                if !unsafe { next_env.slot_matches_compact(idx.as_usize(), expected) } {
                    return false;
                }
            }
        } else if let Some(next_state) = &ctx.next_state {
            for (idx, expected_cv) in entry.deps.next.iter() {
                let name = ctx.var_registry().name(idx);
                let Some(actual) = next_state.get(name) else {
                    return false;
                };
                // Cold path: convert CompactValue back to Value for HashMap comparison.
                if !expected_cv.matches_value(actual) {
                    return false;
                }
            }
        } else if current_state_lookup_mode(ctx) == StateLookupMode::Next {
            // eval_prime Next mode without next_state/next_state_env: rebinds through
            // BindingChain/sparse_next_state_env/state_env/env. Covers swapped-array path,
            // sparse overlays (ENABLED), partial next overlays, full env overlays,
            // quantifier fast-bindings. Sound: each dep index must match the exact value
            // observed during cached evaluation.
            // NOTE: do not shortcut to state_env only; that misses binding/overlay paths.
            for (idx, expected_cv) in entry.deps.next.iter() {
                if !next_mode_dep_matches_compact(ctx, idx, expected_cv) {
                    return false;
                }
            }
        } else {
            return false;
        }
    }
    true
}

// Part of #3025: OP_RESULT_CACHE thread-local removed. The cache had zero
// insertion points after Phase 1 (unified lazy args, #3000) but was still
// cleared on every state transition and ENABLED scope boundary. Removing it
// eliminates 3 unnecessary thread-local accesses per state boundary.
// OpResultCacheKey also removed (no remaining consumers).
// CachedOpResult and op_cache_entry_valid are still used by NARY_OP_CACHE
// and ZERO_ARG_OP_CACHE.

// ============================================================================
// N-ary operator result cache — Part of #2991
// ============================================================================
//
// Re-enables operator result caching after #3000 removed OP_RESULT_CACHE for the
// universal lazy arg path. Unlike the original OP_RESULT_CACHE, this cache:
//
// - Eagerly evaluates all arity-0 args to compute the cache key (cheap for
//   constant args like `Nodes` in `LimitedSeq(Nodes)`)
// - Falls back to the lazy path for higher-order params or arg eval errors
// - Uses dep validation (same as ZERO_ARG_OP_CACHE) for cache hits
// - Stores multiple entries per key with different dep contexts
//
// Target pattern: `LimitedSeq(Nodes)` called ~663K times in MCReachabilityTestAllGraphs.
// Without cache: ~100μs per eval → ~66s total. With cache: 1 eval + 663K hits → <1s.

/// Cache key for N-ary operator result caching.
///
/// Part of #3020: `args` moved from key to `NaryOpCacheEntry`
/// values, replaced by `args_hash: u64`. This avoids `Arc::from(args)` heap
/// allocation on every cache lookup — the hash is computed from `&[Value]`
/// without allocation. Actual arg values are validated after HashMap hit to
/// handle hash collisions.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub(crate) struct NaryOpCacheKey {
    pub(crate) shared_id: u64,
    // BUG FIX #3024: Include local_ops_id and instance_subs_id to distinguish different
    // INSTANCE contexts and LET-scoped operator environments. Without these, operators
    // with the same name and args but different local_ops or instance_substitutions
    // (e.g., different INSTANCE instantiations) can share cached results incorrectly.
    // Part of #3099: Changed from `usize` (Arc::as_ptr) to `u64` (content-based
    // fingerprint) for stable cross-reconstruction cache hits.
    pub(crate) local_ops_id: u64,
    pub(crate) instance_subs_id: u64,
    pub(crate) op_name: NameId,
    pub(crate) def_loc: u32,
    pub(crate) is_next_state: bool,
    /// Part of #3020: Hash of the args slice, replacing `Arc<[Value]>` to avoid
    /// per-lookup heap allocation. Collisions resolved by comparing actual args
    /// stored in cache entries.
    pub(crate) args_hash: u64,
    // Part of #2991: Include param_args_hash to distinguish different parametrized
    // INSTANCE argument values (defense in depth — mirrors OpResultCacheKey's BUG FIX #2986).
    // Without this, `P(Succ1)!Op(args)` and `P(Succ2)!Op(args)` can share cached results
    // when dep validation fails to detect the INSTANCE parameter change.
    pub(crate) param_args_hash: u64,
}

/// Cached operator result with args and dep validation.
/// Part of #3020: args stored here (not in key) to avoid Arc allocation on lookup.
#[derive(Clone)]
pub(crate) struct NaryOpCacheEntry {
    pub(crate) args: Arc<[Value]>,
    pub(crate) result: CachedOpResult,
}

/// Compute a deterministic hash of a `&[Value]` slice for use as `args_hash`.
/// Part of #4112: Uses FxHasher instead of SipHash for faster hashing.
pub(crate) fn hash_args(args: &[Value]) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = rustc_hash::FxHasher::default();
    args.hash(&mut hasher);
    hasher.finish()
}

/// Maximum entries per key in NARY_OP_CACHE.
pub(crate) const NARY_OP_CACHE_MAX_ENTRIES_PER_KEY: usize = 16;

// Part of #3805: Consolidated NARY_OP_CACHE + NARY_PERSISTENT_CACHE into a single
// TLS struct. Previously 2 separate `thread_local!` declarations — nary_lookup
// required 2 `_tlv_get_addr` calls on macOS (~5ns each). Now a single TLS access
// covers both partitions, saving ~5ns per nary_lookup on the BFS hot path.
// Same consolidation pattern as ZERO_ARG_CACHES (#4053/#3962).
pub(crate) struct NaryCaches {
    /// State partition: entries with non-empty deps, cleared on state boundary.
    pub(crate) state: FxHashMap<NaryOpCacheKey, Vec<NaryOpCacheEntry>>,
    /// Persistent partition: entries with empty deps, survive state boundaries.
    pub(crate) persistent: FxHashMap<NaryOpCacheKey, Vec<NaryOpCacheEntry>>,
}

impl NaryCaches {
    fn new() -> Self {
        NaryCaches {
            state: FxHashMap::default(),
            persistent: FxHashMap::default(),
        }
    }
}

std::thread_local! {
    pub(crate) static NARY_CACHES: std::cell::RefCell<NaryCaches> =
        std::cell::RefCell::new(NaryCaches::new());
}

/// Part of #3100: Insert into the appropriate n-ary partition based on deps.
/// Part of #3805: Single TLS access for consolidated NARY_CACHES.
#[inline]
pub(crate) fn nary_insert(key: NaryOpCacheKey, entry: NaryOpCacheEntry) {
    let is_persistent = deps_are_persistent(&entry.result.deps);
    NARY_CACHES.with(|caches| {
        let mut caches = caches.borrow_mut();
        let target = if is_persistent {
            &mut caches.persistent
        } else {
            &mut caches.state
        };
        let entries = target.entry(key).or_default();
        while entries.len() >= NARY_OP_CACHE_MAX_ENTRIES_PER_KEY {
            entries.remove(0);
        }
        entries.push(entry);
    });
}

/// Part of #3100: N-ary lookup probing state partition first, then persistent.
/// Part of #3805: Single TLS access for consolidated NARY_CACHES (was 2 accesses).
#[inline]
pub(crate) fn nary_lookup(
    key: &NaryOpCacheKey,
    args: &[Value],
    validator: impl Fn(&EvalCtx, &CachedOpResult) -> bool,
    ctx: &EvalCtx,
) -> Option<CachedOpResult> {
    NARY_CACHES.with(|caches| {
        let caches = caches.borrow();
        // Probe state partition first (more likely to have recent entries).
        if let Some(entries) = caches.state.get(key) {
            for entry in entries {
                if entry.args.as_ref() == args && validator(ctx, &entry.result) {
                    return Some(entry.result.clone());
                }
            }
        }
        // Then probe persistent partition.
        if let Some(entries) = caches.persistent.get(key) {
            for entry in entries {
                if entry.args.as_ref() == args && validator(ctx, &entry.result) {
                    return Some(entry.result.clone());
                }
            }
        }
        None
    })
}

/// Part of #3109: Constant-entry fallback lookup with flipped `is_next_state`.
/// Part of #3100: Probes persistent partition only (constant entries live there).
/// Part of #3805: Single TLS access via consolidated NARY_CACHES.
#[inline]
pub(crate) fn nary_constant_fallback(
    key: &NaryOpCacheKey,
    args: &[Value],
) -> Option<CachedOpResult> {
    let flipped_key = NaryOpCacheKey {
        is_next_state: !key.is_next_state,
        ..key.clone()
    };
    NARY_CACHES.with(|caches| {
        let caches = caches.borrow();
        let entries = caches.persistent.get(&flipped_key)?;
        for entry in entries {
            if entry.args.as_ref() == args && deps_are_persistent(&entry.result.deps) {
                return Some(entry.result.clone());
            }
        }
        None
    })
}

/// Part of #3100: Clear state partition only. Persistent entries survive.
/// Part of #3805: Single TLS access via consolidated NARY_CACHES.
#[inline]
pub(crate) fn clear_nary_state_partition() {
    NARY_CACHES.with(|c| c.borrow_mut().state.clear());
}

/// Part of #3100: Clear both partitions (run reset / test reset).
/// Part of #3805: Single TLS access via consolidated NARY_CACHES.
#[inline]
pub(crate) fn clear_nary_all_partitions() {
    NARY_CACHES.with(|c| {
        let mut c = c.borrow_mut();
        c.state.clear();
        c.persistent.clear();
    });
}
