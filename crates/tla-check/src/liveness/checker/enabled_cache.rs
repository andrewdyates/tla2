// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Thread-local ENABLED evaluation cache for liveness checking.
//!
//! Extracted from `checker/mod.rs`. Provides caching of `ENABLED(action)(state)`
//! booleans to avoid redundant evaluation during consistency and SCC checking.
//! No dependency on `LivenessChecker` — clean extraction boundary.

use super::cache_stats::{record_enabled_eviction, record_enabled_hit, record_enabled_miss};
use crate::error::EvalResult;
use crate::eval::EvalCtx;
use crate::state::Fingerprint;
use rustc_hash::FxHashMap;
use std::cell::{Cell, RefCell};

// Thread-local cache for ENABLED evaluation results.
//
// TLC pre-computes ENABLED(action)(state) booleans once per state during BFS
// graph construction and stores them in GraphNode BitVectors. TLA2 previously
// re-evaluated ENABLED for every (state, tableau_node) pair during consistency
// checking, causing O(states × tableau_nodes × enumeration_cost) work instead
// of O(states × unique_enabled_tags × enumeration_cost).
//
// This cache stores `(state_fingerprint, enabled_tag) -> bool` and is shared
// across both consistency checking (explore_bfs) and SCC constraint checking.
// The `tag` field on `LiveExpr::Enabled` uniquely identifies each expanded
// ENABLED expression (including bindings from quantified fairness).
//
// Clear this cache at the start of each `check_liveness_property` call.
//
// Soft cap: 5M entries with retain-half eviction (#4083). Without a cap,
// this cache grows linearly with the number of states visited during liveness
// checking, which can reach millions for large specs. Entries are lightweight
// ((Fingerprint, u32) -> bool = ~13 bytes each), so 5M entries ≈ 65MB.
//
// The previous 200K cap caused severe thrashing on specs with many fairness
// tags. AllocatorImplementation has 122 ENABLED checks × 17,701 states =
// 2.16M entries; at the old cap, 2M evictions occurred. The cache must hold
// at least (states × enabled_tags) entries to avoid re-evaluation.
const ENABLED_CACHE_SOFT_CAP: usize = 5_000_000;

thread_local! {
    pub(crate) static ENABLED_CACHE: RefCell<FxHashMap<(Fingerprint, u32), bool>> =
        RefCell::new(FxHashMap::default());
    /// Track whether we have already emitted the first-eviction warning.
    static ENABLED_EVICTION_WARNED: Cell<bool> = const { Cell::new(false) };
}

/// Clear the thread-local ENABLED cache.
///
/// Must be called at the start of each liveness property check to avoid
/// stale results from a previous property's formula (different tag space).
pub(crate) fn clear_enabled_cache() {
    ENABLED_CACHE.with(|c| c.borrow_mut().clear());
    ENABLED_EVICTION_WARNED.with(|warned| warned.set(false));
}

/// Trim ENABLED_CACHE if it exceeds the soft cap (#4083).
/// Uses retain-half eviction: keeps ~half the entries using FxHashMap's
/// pseudo-random iteration order, same pattern as eval-layer caches
/// (see `crates/tla-eval/src/cache/lifecycle_trim.rs`).
fn trim_enabled_cache_if_needed() {
    ENABLED_CACHE.with(|c| {
        let mut cache = c.borrow_mut();
        let len = cache.len();
        if len > ENABLED_CACHE_SOFT_CAP {
            // Log a warning on first eviction for monitoring (#4083).
            ENABLED_EVICTION_WARNED.with(|warned| {
                if !warned.get() {
                    eprintln!(
                        "[liveness] ENABLED_CACHE exceeded soft cap ({} > {}), evicting",
                        len, ENABLED_CACHE_SOFT_CAP
                    );
                    warned.set(true);
                }
            });
            let target = ENABLED_CACHE_SOFT_CAP / 2;
            let mut kept = 0;
            cache.retain(|_, _| {
                if kept < target {
                    kept += 1;
                    true
                } else {
                    false
                }
            });
            record_enabled_eviction(len.saturating_sub(cache.len()) as u64);
        }
    });
}

fn get_enabled_cached_internal(state_fp: Fingerprint, tag: u32) -> Option<bool> {
    ENABLED_CACHE.with(|c| {
        let result = c.borrow().get(&(state_fp, tag)).copied();
        if result.is_some() {
            record_enabled_hit();
        } else {
            record_enabled_miss();
        }
        result
    })
}

/// Evaluate ENABLED with shared thread-local caching.
///
/// Caching is enabled only when `VarRegistry` is populated (production path).
/// In empty-registry fallback mode, ENABLED can depend on checker-local successor
/// maps, so `(state_fingerprint, tag)` is not a stable cache key across checker
/// instances.
///
/// Part of #2998: Enters ENABLED evaluation scope via `enter_enabled_scope()`,
/// which clears PerState evaluator caches at scope boundaries. This matches TLC's
/// `EvalControl.Enabled` bitflag that disables LazyValue caching within ENABLED
/// (EvalControl.java:22-25, Tool.java:1949-1953). The scope guard is a no-op
/// when already inside an ENABLED scope (nested calls from array path).
pub(crate) fn eval_enabled_cached<F>(
    ctx: &EvalCtx,
    state_fp: Fingerprint,
    tag: u32,
    eval_uncached: F,
) -> EvalResult<bool>
where
    F: FnOnce() -> EvalResult<bool>,
{
    let use_enabled_cache = !ctx.var_registry().is_empty();
    if use_enabled_cache {
        if let Some(result) = get_enabled_cached_internal(state_fp, tag) {
            return Ok(result);
        }
    }

    // Part of #2998: Enter ENABLED scope — clears PerState caches on first entry
    // to prevent non-ENABLED cache entries from contaminating ENABLED evaluation.
    // Returns None (no-op) if already in scope (e.g., called from within
    // ea_precompute's array path which enters the scope for the entire Phase A).
    // Part of #3962: Use ctx-aware variant to sync in_enabled_scope shadow.
    let _enabled_guard = crate::eval::enter_enabled_scope_with_ctx(ctx);

    let result = eval_uncached()?;

    if use_enabled_cache {
        trim_enabled_cache_if_needed();
        ENABLED_CACHE.with(|c| c.borrow_mut().insert((state_fp, tag), result));
    }

    Ok(result)
}

/// Mutable variant of [`eval_enabled_cached`] for array-native callers that
/// need to update `next_state` / `next_state_env` while computing ENABLED.
pub(crate) fn eval_enabled_cached_mut<F>(
    ctx: &mut EvalCtx,
    state_fp: Fingerprint,
    tag: u32,
    eval_uncached: F,
) -> EvalResult<bool>
where
    F: FnOnce(&mut EvalCtx) -> EvalResult<bool>,
{
    let use_enabled_cache = !ctx.var_registry().is_empty();
    if use_enabled_cache {
        if let Some(result) = get_enabled_cached_internal(state_fp, tag) {
            return Ok(result);
        }
    }

    // Part of #3962: Use ctx-aware variant to sync in_enabled_scope shadow.
    let _enabled_guard = crate::eval::enter_enabled_scope_with_ctx(ctx);
    let result = eval_uncached(ctx)?;

    if use_enabled_cache {
        trim_enabled_cache_if_needed();
        ENABLED_CACHE.with(|c| c.borrow_mut().insert((state_fp, tag), result));
    }

    Ok(result)
}

/// Check if an ENABLED result is already in the thread-local cache.
pub(crate) fn is_enabled_cached(state_fp: Fingerprint, tag: u32) -> bool {
    get_enabled_cached_internal(state_fp, tag).is_some()
}

/// Get an ENABLED result from the thread-local cache if present.
///
/// Part of #3100: Used by the batched ENABLED evaluator to check cache
/// before entering the successor iteration loop.
pub(crate) fn get_enabled_cached(state_fp: Fingerprint, tag: u32) -> Option<bool> {
    get_enabled_cached_internal(state_fp, tag)
}

/// Insert an ENABLED result into the thread-local cache.
/// Trims the cache via retain-half eviction if it exceeds the soft cap (#4083).
pub(crate) fn set_enabled_cache(state_fp: Fingerprint, tag: u32, result: bool) {
    trim_enabled_cache_if_needed();
    ENABLED_CACHE.with(|c| c.borrow_mut().insert((state_fp, tag), result));
}
