// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Cache capacity management: soft-cap constants and trim functions.
//!
//! Extracted from lifecycle.rs as part of #3442. The trim subsystem is a capacity
//! policy concern orthogonal to lifecycle event routing. `trim_eval_entry_caches()`
//! only reads thread-locals from cache storage modules — it doesn't reference any
//! lifecycle types (CacheEvent, EnabledScopeGuard).

use super::op_result_cache::NARY_CACHES;
use super::small_caches::SMALL_CACHES;
use super::subst_cache::SUBST_STATE;
use super::zero_arg_cache::ZERO_ARG_CACHES;

// Part of #3025: OP_RESULT_CACHE_SOFT_CAP removed — cache had zero insertions.
const SUBST_CACHE_SOFT_CAP: usize = 10_000;

// Part of #2413 U6: Soft caps for PerRun caches that were previously unbounded.
// Part of #3025: Cliff-clear replaced with retain-half to avoid pathological thrash.
const LITERAL_CACHE_SOFT_CAP: usize = 50_000;
// Part of #2955: Soft cap for constant LET expression cache.
const CONST_LET_CACHE_SOFT_CAP: usize = 50_000;
// Soft cap for ZERO_ARG_OP_CACHE total key count. Per-key entries are already capped at
// ZERO_ARG_CACHE_MAX_ENTRIES_PER_KEY (16), but total keys were unbounded.
const ZERO_ARG_OP_CACHE_SOFT_CAP: usize = 10_000;
// Part of #2991: Soft caps for N-ary operator result caches.
// Fix #3070: Raised soft cap since NARY_OP_CONST_CACHE entries are now merged here.
const NARY_OP_CACHE_SOFT_CAP: usize = 50_000;
const RAW_SUBST_SCOPE_CACHE_SOFT_CAP: usize = 10_000;
// Part of #3392: Soft caps for param-LET caches (Tier 1.5 LET bodies with local-only deps).
// Bounded by AST structure in practice, but cap prevents unbounded growth in pathological
// multi-instance specs. Recommended by Prover audit (commit 8c9b126).
const PARAM_LET_CACHE_SOFT_CAP: usize = 10_000;
const PARAM_LET_DEPS_SOFT_CAP: usize = 10_000;
// Soft caps for persistent cache partitions. These are long-lived (survive state
// transitions) and were previously unbounded. During long model-checking runs with
// many unique operator/argument combinations, persistent caches can grow without
// limit, contributing to OOM under multi-instance workloads.
const ZERO_ARG_PERSISTENT_CACHE_SOFT_CAP: usize = 50_000;
const NARY_PERSISTENT_CACHE_SOFT_CAP: usize = 50_000;

/// Part of #3025: Retain approximately `target` entries, evicting the rest.
/// Uses HashMap's pseudo-random iteration order for unbiased eviction.
/// Replaces cliff-clear (`clear()`) which caused pathological re-fill cycles
/// when working set slightly exceeded the soft cap.
#[inline]
fn retain_half_hashmap<K, V, S: std::hash::BuildHasher>(
    map: &mut std::collections::HashMap<K, V, S>,
    target: usize,
) {
    let mut kept = 0;
    map.retain(|_, _| {
        if kept < target {
            kept += 1;
            true
        } else {
            false
        }
    });
}

/// Part of #3962: Made pub(crate) so eval_cache_lifecycle.rs can call it
/// directly from the shadow-counter eval exit path, bypassing the
/// EVAL_EXIT_COUNT thread-local in on_cache_event(EvalExit).
#[inline]
pub(crate) fn trim_eval_entry_caches() {
    // Part of #3025: OP_RESULT_CACHE trim removed — cache had zero insertions.
    // Part of #3025: All soft-cap trims use retain-half instead of cliff-clear.

    // Part of #3805: Uses consolidated SUBST_STATE.
    SUBST_STATE.with(|s| {
        let len = s.borrow().cache.len();
        if len > SUBST_CACHE_SOFT_CAP {
            retain_half_hashmap(&mut s.borrow_mut().cache, SUBST_CACHE_SOFT_CAP / 2);
        }
    });

    // Part of #3962: Single TLS access to trim all SMALL_CACHES fields.
    SMALL_CACHES.with(|sc| {
        let mut sc = sc.borrow_mut();
        // Part of #2413 U6: PerRun caches — trim to prevent unbounded growth.
        if sc.literal_cache.len() > LITERAL_CACHE_SOFT_CAP {
            retain_half_hashmap(&mut sc.literal_cache, LITERAL_CACHE_SOFT_CAP / 2);
        }
        // Part of #2955: PerRun cache — trim constant LET expression cache.
        if sc.const_let_cache.len() > CONST_LET_CACHE_SOFT_CAP {
            retain_half_hashmap(&mut sc.const_let_cache, CONST_LET_CACHE_SOFT_CAP / 2);
        }
        if sc.raw_subst_scope_cache.len() > RAW_SUBST_SCOPE_CACHE_SOFT_CAP {
            retain_half_hashmap(
                &mut sc.raw_subst_scope_cache,
                RAW_SUBST_SCOPE_CACHE_SOFT_CAP / 2,
            );
        }
        // Part of #3392: Trim param-LET caches (Tier 1.5 local-only-dep LET bodies).
        if sc.param_let_deps.len() > PARAM_LET_DEPS_SOFT_CAP {
            retain_half_hashmap(&mut sc.param_let_deps, PARAM_LET_DEPS_SOFT_CAP / 2);
        }
        if sc.param_let_cache.len() > PARAM_LET_CACHE_SOFT_CAP {
            retain_half_hashmap(&mut sc.param_let_cache, PARAM_LET_CACHE_SOFT_CAP / 2);
        }
    });

    // Fix #2462: ZERO_ARG_OP_CONST_CACHE removed — constant entries now in ZERO_ARG_OP_CACHE.

    // Part of #3100: Trim state partitions.
    // Part of #3025: Retain-half instead of full clear.
    // Part of #4053: Single TLS access for both zero-arg partitions (was 2 before).
    ZERO_ARG_CACHES.with(|caches| {
        let mut caches = caches.borrow_mut();
        if caches.state.len() > ZERO_ARG_OP_CACHE_SOFT_CAP {
            retain_half_hashmap(&mut caches.state, ZERO_ARG_OP_CACHE_SOFT_CAP / 2);
        }
        // Persistent partitions: long-lived entries that survive state transitions.
        // Previously unbounded; soft-capped to prevent OOM under long runs with
        // many unique operator/argument combinations (multi-instance workloads).
        if caches.persistent.len() > ZERO_ARG_PERSISTENT_CACHE_SOFT_CAP {
            retain_half_hashmap(&mut caches.persistent, ZERO_ARG_PERSISTENT_CACHE_SOFT_CAP / 2);
        }
    });

    // Part of #3805: Single TLS access for both nary partitions (was 2 before).
    NARY_CACHES.with(|caches| {
        let mut caches = caches.borrow_mut();
        if caches.state.len() > NARY_OP_CACHE_SOFT_CAP {
            retain_half_hashmap(&mut caches.state, NARY_OP_CACHE_SOFT_CAP / 2);
        }
        if caches.persistent.len() > NARY_PERSISTENT_CACHE_SOFT_CAP {
            retain_half_hashmap(&mut caches.persistent, NARY_PERSISTENT_CACHE_SOFT_CAP / 2);
        }
    });

    // Module-ref PerRun caches are trimmed via the helpers module.
    crate::helpers::trim_module_ref_caches();
}
