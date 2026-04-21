// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Zero-argument operator caches with lifecycle partitioning.
//!
//! Part of #3100: Caches are split into two physical partitions by lifecycle:
//!   - state partition: entries with non-empty deps, cleared on state boundary
//!     via simple `.clear()`.
//!   - persistent partition: entries with empty deps, survive state boundaries.
//!     Cleared only on run/test reset.
//!
//! Part of #4053/#3962: Both partitions consolidated into a single TLS struct
//! (`ZERO_ARG_CACHES`). Previously two separate `thread_local!` declarations,
//! each requiring a separate `_tlv_get_addr` call on macOS (~5ns each).
//! `zero_arg_lookup` probed both partitions sequentially = 2 TLS accesses per
//! lookup. Now a single TLS access covers both partitions, saving ~5ns per
//! `zero_arg_lookup` on the BFS hot path.
//!
//! This eliminates the O(cache_size) retain scan that previously ran once per
//! BFS parent state during inline liveness (81K calls for Huang).
//!
//! Fix #2462: Both partitions use dep validation via op_cache_entry_valid().
//! No unvalidated constant cache — the persistent partition stores validated
//! entries that happen to have empty deps.
//!
//! Part of #2744 decomposition from eval_cache.rs.

use super::dep_tracking::OpEvalDeps;
use super::op_result_cache::CachedOpResult;
use crate::EvalCtx;
use rustc_hash::FxHashMap;
use tla_core::name_intern::NameId;

/// Cache key type for zero-arg caches.
///
/// Fields: (shared_id, local_ops_id, instance_subs_id, op_name, def_loc, is_next_state)
///
/// BUG FIX #3097: Includes `local_ops_id` and `instance_subs_id` to distinguish different
/// INSTANCE contexts and LET-scoped operator environments. Without these, operators with
/// the same name and definition location but different local_ops or instance_substitutions
/// (e.g., different INSTANCE instantiations) could share cached results incorrectly.
/// This matches the discrimination already accepted for OpResultCacheKey and NaryOpCacheKey.
///
/// BUG FIX #277: `def_loc` (span.start) distinguishes different LET blocks.
/// BUG FIX #295: `is_next_state` distinguishes primed vs unprimed lookups.
/// Part of #3099/#3157: `local_ops_id` and `instance_subs_id` are now stable u64
/// content-based fingerprints (matching SubstCacheKey and NaryOpCacheKey), replacing
/// the previous `Arc::as_ptr() as usize` pattern that produced different keys for
/// logically identical scopes.
pub(crate) type ZeroArgCacheKey = (u64, u64, u64, NameId, u32, bool);

// Part of #4053/#3962: Consolidated zero-arg cache struct holding both partitions
// in a single TLS entry. Previously two separate thread_local! declarations
// (ZERO_ARG_OP_CACHE + ZERO_ARG_PERSISTENT_CACHE) requiring 2 TLS accesses per
// zero_arg_lookup. Now 1 TLS access covers both.
//
// Key: (shared_id, local_ops_id, instance_subs_id, op_name, def_loc, is_next_state)
// Value: Vec of cached results per key with dep-based validation.
pub(crate) struct ZeroArgCaches {
    /// State partition: entries with non-empty deps, cleared on state boundary.
    pub(crate) state: FxHashMap<ZeroArgCacheKey, Vec<CachedOpResult>>,
    /// Persistent partition: entries with empty deps, survive state boundaries.
    /// Cleared only on run/test reset. Part of #3100.
    pub(crate) persistent: FxHashMap<ZeroArgCacheKey, Vec<CachedOpResult>>,
}

impl ZeroArgCaches {
    fn new() -> Self {
        ZeroArgCaches {
            state: FxHashMap::default(),
            persistent: FxHashMap::default(),
        }
    }
}

std::thread_local! {
    pub(crate) static ZERO_ARG_CACHES: std::cell::RefCell<ZeroArgCaches> =
        std::cell::RefCell::new(ZeroArgCaches::new());
}

/// Build a zero-arg cache key from the evaluation context.
///
/// Part of #3099/#3157: Uses content-based u64 fingerprints from `scope_ids`
/// for `local_ops_id` and `instance_subs_id`, matching `subst_cache_key()`
/// and `NaryOpCacheKey`. Replaces the previous `Arc::as_ptr` pointer-identity
/// convention which was vulnerable to allocator address reuse.
///
/// Part of #3097: Single helper ensures lookup and insert use the same key shape,
/// preventing drift between the three call sites in eval_ident_zero_arg.rs.
#[inline]
pub(crate) fn zero_arg_cache_key(
    ctx: &EvalCtx,
    name_id: NameId,
    def_loc: u32,
    is_next_state: bool,
) -> ZeroArgCacheKey {
    use super::scope_ids::{resolve_instance_subs_id, resolve_local_ops_id};
    let local_ops_id = resolve_local_ops_id(ctx.scope_ids.local_ops, &ctx.local_ops);
    let instance_subs_id = resolve_instance_subs_id(
        ctx.scope_ids.instance_substitutions,
        &ctx.instance_substitutions,
    );
    (
        ctx.shared.id,
        local_ops_id,
        instance_subs_id,
        name_id,
        def_loc,
        is_next_state,
    )
}

/// Maximum entries per key in zero-arg caches to prevent unbounded memory growth.
/// When exceeded, oldest entries are evicted.
pub(crate) const ZERO_ARG_CACHE_MAX_ENTRIES_PER_KEY: usize = 16;

// Part of #3805: Debug counters for zero-arg cache performance analysis.
// Enabled via TLA2_ZERO_ARG_CACHE_STATS=1 environment variable.
// Uses feature_flag! (not debug_flag!) to work in release mode.
feature_flag!(pub(crate) debug_zero_arg_stats, "TLA2_ZERO_ARG_CACHE_STATS");

pub(crate) struct ZeroArgCacheStats {
    pub(crate) primary_hits: u64,
    pub(crate) canonical_hits: u64,
    pub(crate) constant_fallback_hits: u64,
    pub(crate) misses: u64,
    /// Misses where deps were persistent (constant) — indicates canonical key
    /// should have caught this but didn't (first eval only).
    pub(crate) persistent_misses: u64,
    /// Misses where instance_lazy_read taint prevented persistent classification.
    pub(crate) instance_taint_misses: u64,
    /// Top miss operators by name.
    pub(crate) miss_names: std::collections::HashMap<String, u64>,
}

impl ZeroArgCacheStats {
    fn new() -> Self {
        Self {
            primary_hits: 0,
            canonical_hits: 0,
            constant_fallback_hits: 0,
            misses: 0,
            persistent_misses: 0,
            instance_taint_misses: 0,
            miss_names: std::collections::HashMap::new(),
        }
    }
}

std::thread_local! {
    pub(crate) static ZERO_ARG_STATS: std::cell::RefCell<ZeroArgCacheStats> =
        std::cell::RefCell::new(ZeroArgCacheStats::new());
}

#[inline]
pub(crate) fn record_zero_arg_primary_hit() {
    if debug_zero_arg_stats() {
        ZERO_ARG_STATS.with(|s| s.borrow_mut().primary_hits += 1);
    }
}

#[inline]
pub(crate) fn record_zero_arg_canonical_hit() {
    if debug_zero_arg_stats() {
        ZERO_ARG_STATS.with(|s| s.borrow_mut().canonical_hits += 1);
    }
}

#[inline]
pub(crate) fn record_zero_arg_constant_fallback_hit() {
    if debug_zero_arg_stats() {
        ZERO_ARG_STATS.with(|s| s.borrow_mut().constant_fallback_hits += 1);
    }
}

#[inline]
pub(crate) fn record_zero_arg_miss(name: &str, deps: &OpEvalDeps) {
    if debug_zero_arg_stats() {
        ZERO_ARG_STATS.with(|s| {
            let mut s = s.borrow_mut();
            s.misses += 1;
            if deps_are_persistent(deps) {
                s.persistent_misses += 1;
            }
            if deps.instance_lazy_read {
                s.instance_taint_misses += 1;
            }
            *s.miss_names.entry(name.to_string()).or_default() += 1;
        });
    }
}

/// Print cache stats summary. Called at end of model checking run.
pub(crate) fn print_zero_arg_cache_stats() {
    if !debug_zero_arg_stats() {
        return;
    }
    ZERO_ARG_STATS.with(|s| {
        let s = s.borrow();
        let total = s.primary_hits + s.canonical_hits + s.constant_fallback_hits + s.misses;
        if total == 0 {
            return;
        }
        eprintln!("\n=== Zero-Arg Cache Stats ===");
        eprintln!("Total lookups:          {}", total);
        eprintln!("Primary hits:           {} ({:.1}%)", s.primary_hits, s.primary_hits as f64 / total as f64 * 100.0);
        eprintln!("Canonical hits:         {} ({:.1}%)", s.canonical_hits, s.canonical_hits as f64 / total as f64 * 100.0);
        eprintln!("Constant fallback hits: {} ({:.1}%)", s.constant_fallback_hits, s.constant_fallback_hits as f64 / total as f64 * 100.0);
        eprintln!("Misses:                 {} ({:.1}%)", s.misses, s.misses as f64 / total as f64 * 100.0);
        eprintln!("  Persistent misses:    {} (first eval of constant ops)", s.persistent_misses);
        eprintln!("  Instance taint:       {} (instance_lazy_read prevented persistent)", s.instance_taint_misses);
        eprintln!("\nTop miss operators:");
        let mut miss_vec: Vec<_> = s.miss_names.iter().collect();
        miss_vec.sort_by(|a, b| b.1.cmp(a.1));
        for (name, count) in miss_vec.iter().take(20) {
            eprintln!("  {:>8}  {}", count, name);
        }
        eprintln!("============================\n");
    });
}

/// Part of #3100: Check if deps qualify for the persistent partition (empty deps).
/// Fix #3447: Also rejects deps tainted by INSTANCE lazy binding reads.
#[inline]
pub(crate) fn deps_are_persistent(deps: &OpEvalDeps) -> bool {
    !deps.inconsistent
        && !deps.instance_lazy_read
        && deps.state.is_empty()
        && deps.next.is_empty()
        && deps.local.is_empty()
        && deps.tlc_level.is_none()
}

/// Part of #3100/#4053: Insert into the appropriate partition based on deps.
/// Empty deps -> persistent partition, non-empty deps -> state partition.
/// Part of #4053: Single TLS access for both partitions.
#[inline]
pub(crate) fn zero_arg_insert(key: ZeroArgCacheKey, entry: CachedOpResult) {
    ZERO_ARG_CACHES.with(|caches| {
        let mut caches = caches.borrow_mut();
        let target = if deps_are_persistent(&entry.deps) {
            &mut caches.persistent
        } else {
            &mut caches.state
        };
        let entries = target.entry(key).or_default();
        while entries.len() >= ZERO_ARG_CACHE_MAX_ENTRIES_PER_KEY {
            entries.remove(0);
        }
        entries.push(entry);
    });
}

/// Part of #3100/#4053: Lookup probing state partition first, then persistent.
/// Returns the first entry for which `validator` returns true.
/// Part of #4053: Single TLS access for both partitions (was 2 before).
#[inline]
pub(crate) fn zero_arg_lookup(
    key: &ZeroArgCacheKey,
    validator: impl Fn(&CachedOpResult) -> bool,
) -> Option<CachedOpResult> {
    ZERO_ARG_CACHES.with(|caches| {
        let caches = caches.borrow();
        // Probe state partition first (hot entries for current state)
        if let Some(entries) = caches.state.get(key) {
            for entry in entries {
                if validator(entry) {
                    return Some(entry.clone());
                }
            }
        }
        // Probe persistent partition
        if let Some(entries) = caches.persistent.get(key) {
            for entry in entries {
                if validator(entry) {
                    return Some(entry.clone());
                }
            }
        }
        None
    })
}

/// Get total number of stored entries across both partitions.
#[cfg(test)]
pub(crate) fn zero_arg_op_cache_entry_count() -> usize {
    ZERO_ARG_CACHES.with(|caches| {
        let caches = caches.borrow();
        let state_count: usize = caches.state.values().map(std::vec::Vec::len).sum();
        let persistent_count: usize = caches.persistent.values().map(std::vec::Vec::len).sum();
        state_count + persistent_count
    })
}

/// Clear both partitions for test isolation.
#[cfg(test)]
pub(crate) fn zero_arg_op_cache_clear() {
    ZERO_ARG_CACHES.with(|caches| {
        let mut caches = caches.borrow_mut();
        caches.state.clear();
        caches.persistent.clear();
    });
}

/// Part of #3109: Constant-entry fallback lookup with flipped `is_next_state`.
///
/// During ENABLED scope, `current_state_lookup_mode` may differ from when the
/// entry was cached during BFS. For constant operators (empty deps), the
/// `is_next_state` flag doesn't affect correctness — constant results are
/// state-independent. This function retries the lookup with the opposite
/// `is_next_state` value, accepting only constant entries.
///
/// Part of #3100: Probes persistent partition only (constant entries live there).
/// Part of #4053: Single TLS access via consolidated struct.
#[inline]
pub(crate) fn zero_arg_constant_fallback(key: &ZeroArgCacheKey) -> Option<super::CachedOpResult> {
    let flipped_key = (key.0, key.1, key.2, key.3, key.4, !key.5);
    ZERO_ARG_CACHES.with(|caches| {
        let caches = caches.borrow();
        let entries = caches.persistent.get(&flipped_key)?;
        for entry in entries {
            if deps_are_persistent(&entry.deps) {
                return Some(entry.clone());
            }
        }
        None
    })
}

/// Part of #3100/#4053: Clear state partition only. Persistent entries survive.
/// Replaces the old retain_only_zero_arg_constant_entries() retain scan.
#[inline]
pub(crate) fn clear_zero_arg_state_partition() {
    ZERO_ARG_CACHES.with(|c| c.borrow_mut().state.clear());
}

/// Part of #3100/#4053: Clear both partitions (run reset / test reset).
#[inline]
pub(crate) fn clear_zero_arg_all_partitions() {
    ZERO_ARG_CACHES.with(|c| {
        let mut c = c.borrow_mut();
        c.state.clear();
        c.persistent.clear();
    });
}

/// Build a scope-normalized "canonical" cache key for constant operators.
///
/// When `local_ops` contains recursive operators, `compute_local_ops_scope_id`
/// falls back to `Arc` pointer identity, producing a different scope id every
/// time `with_outer_resolution_scope()` is called. This prevents persistent
/// (constant) cache entries from being found on subsequent lookups.
///
/// The canonical key sets `local_ops_id = 0` and `instance_subs_id = 0`,
/// making it scope-independent. This is safe ONLY for persistent entries
/// (empty deps) because constant operators produce the same value regardless
/// of the local_ops or instance_substitutions scope.
#[inline]
pub(crate) fn zero_arg_canonical_key(
    shared_id: u64,
    name_id: NameId,
    def_loc: u32,
    is_next_state: bool,
) -> ZeroArgCacheKey {
    (shared_id, 0, 0, name_id, def_loc, is_next_state)
}

/// Lookup a constant operator using the scope-normalized canonical key.
///
/// Only probes the persistent partition and only accepts entries with
/// persistent deps. This is the fallback path when the scope-discriminated
/// lookup fails due to unstable `local_ops_id` from recursive operator
/// environments (e.g., `RECURSIVE PublicKeyOf(_)` in INSTANCE Nano).
#[inline]
pub(crate) fn zero_arg_canonical_lookup(
    canonical_key: &ZeroArgCacheKey,
) -> Option<CachedOpResult> {
    ZERO_ARG_CACHES.with(|caches| {
        let caches = caches.borrow();
        let entries = caches.persistent.get(canonical_key)?;
        for entry in entries {
            if deps_are_persistent(&entry.deps) {
                return Some(entry.clone());
            }
        }
        None
    })
}

/// Insert a constant operator result under the canonical key.
///
/// Only call this for entries with persistent deps (caller must verify).
/// Routes directly to the persistent partition.
#[inline]
pub(crate) fn zero_arg_canonical_insert(key: ZeroArgCacheKey, entry: CachedOpResult) {
    debug_assert!(
        deps_are_persistent(&entry.deps),
        "canonical insert must only be used for persistent entries"
    );
    ZERO_ARG_CACHES.with(|caches| {
        let mut caches = caches.borrow_mut();
        let entries = caches.persistent.entry(key).or_default();
        // Canonical keys have at most 1 entry per key (constant value is unique).
        if entries.is_empty() {
            entries.push(entry);
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_deps_are_persistent_rejects_instance_lazy_read() {
        let mut deps = OpEvalDeps::default();
        assert!(
            deps_are_persistent(&deps),
            "empty deps should be persistent"
        );

        deps.instance_lazy_read = true;
        assert!(
            !deps_are_persistent(&deps),
            "deps with instance_lazy_read taint must NOT be persistent"
        );
    }

    #[test]
    fn test_deps_are_persistent_rejects_inconsistent() {
        let mut deps = OpEvalDeps::default();
        deps.inconsistent = true;
        assert!(!deps_are_persistent(&deps));
    }

    #[test]
    fn test_deps_are_persistent_accepts_clean_empty() {
        let deps = OpEvalDeps::default();
        assert!(deps_are_persistent(&deps));
    }
}
