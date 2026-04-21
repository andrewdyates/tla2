// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Subscript expression evaluation and caching for liveness checking.
//!
//! Provides both the subscript value cache and the `eval_subscript_changed`
//! function that determines whether a subscript expression changed between two
//! states. Co-locating cache and evaluation eliminates redundant evaluations
//! across transitions that share the same state. For EWD998ChanID with WF_vars(A),
//! all fairness conditions share the same subscript expression `vars`, so each
//! unique state is evaluated once instead of once per transition × check. This
//! keeps SUBST_CACHE warm for ActionPred evaluations by avoiding state_env=None
//! context switches from with_explicit_env (#2364).

use super::cache_stats::{record_subscript_eviction, record_subscript_hit, record_subscript_miss};
use crate::error::EvalResult;
use crate::eval::{BindingChain, EvalCtx};
use crate::state::{ArrayState, Fingerprint, State};
use crate::Value;
use rustc_hash::FxHashMap;
use std::cell::{Cell, RefCell};
use std::sync::Arc;

/// Soft cap for SUBSCRIPT_VALUE_CACHE entries. When exceeded, retain-half
/// eviction removes roughly half the entries using HashMap's pseudo-random
/// iteration order. Prevents unbounded linear growth with state count (#4083).
///
/// Set to 5M to avoid cache thrashing on specs with many fairness tags.
/// AllocatorImplementation has 115 WF conditions × 17,701 states = ~2M entries;
/// at the old 50K cap, 24M evictions caused 59s overhead (>95% of liveness time).
/// Entries share Values via Arc, so 5M entries ≈ 100-200MB actual memory.
/// The precompute phase fills the cache for all (state, tag) pairs, and
/// subsequent lookups during the eval loop must find them without eviction.
const SUBSCRIPT_VALUE_CACHE_SOFT_CAP: usize = 5_000_000;

thread_local! {
    static SUBSCRIPT_VALUE_CACHE: RefCell<FxHashMap<(Fingerprint, u32), Value>> =
        RefCell::new(FxHashMap::default());
    /// Track whether we have already emitted the first-eviction warning.
    static SUBSCRIPT_EVICTION_WARNED: Cell<bool> = const { Cell::new(false) };
}

/// Clear the subscript value cache. Called at the start of populate_node_check_masks
/// and by `reset_global_state()` for between-run isolation.
pub(crate) fn clear_subscript_value_cache() {
    SUBSCRIPT_VALUE_CACHE.with(|cache| cache.borrow_mut().clear());
    SUBSCRIPT_EVICTION_WARNED.with(|warned| warned.set(false));
}

/// Trim SUBSCRIPT_VALUE_CACHE if it exceeds the soft cap (#4083).
/// Uses retain-half eviction: keeps ~half the entries using FxHashMap's
/// pseudo-random iteration order, same pattern as eval-layer caches.
fn trim_subscript_value_cache_if_needed() {
    SUBSCRIPT_VALUE_CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        let len = cache.len();
        if len > SUBSCRIPT_VALUE_CACHE_SOFT_CAP {
            // Log a warning on first eviction for monitoring (#4083).
            SUBSCRIPT_EVICTION_WARNED.with(|warned| {
                if !warned.get() {
                    eprintln!(
                        "[liveness] SUBSCRIPT_VALUE_CACHE exceeded soft cap ({} > {}), evicting",
                        len, SUBSCRIPT_VALUE_CACHE_SOFT_CAP
                    );
                    warned.set(true);
                }
            });
            let target = SUBSCRIPT_VALUE_CACHE_SOFT_CAP / 2;
            let mut kept = 0;
            cache.retain(|_, _| {
                if kept < target {
                    kept += 1;
                    true
                } else {
                    false
                }
            });
            record_subscript_eviction(len.saturating_sub(cache.len()) as u64);
        }
    });
}

/// Insert a pre-computed subscript value into the cache.
/// Trims the cache via retain-half eviction if it exceeds the soft cap (#4083).
pub(super) fn set_subscript_value_cache(fp: Fingerprint, tag: u32, value: Value) {
    trim_subscript_value_cache_if_needed();
    SUBSCRIPT_VALUE_CACHE.with(|cache| {
        cache.borrow_mut().insert((fp, tag), value);
    });
}

/// Check if subscript values differ between two states using the pre-computed cache.
///
/// Returns `Some(true)` if values differ, `Some(false)` if equal, `None` if either
/// value is not in the cache (caller should fall back to expression evaluation).
pub(super) fn check_subscript_changed_cached(
    fp1: Fingerprint,
    fp2: Fingerprint,
    tag: u32,
) -> Option<bool> {
    SUBSCRIPT_VALUE_CACHE.with(|cache| {
        let c = cache.borrow();
        let v1 = c.get(&(fp1, tag));
        let v2 = c.get(&(fp2, tag));
        match (v1, v2) {
            (Some(v1), Some(v2)) => {
                record_subscript_hit();
                record_subscript_hit();
                Some(v1 != v2)
            }
            _ => {
                if v1.is_some() {
                    record_subscript_hit();
                } else {
                    record_subscript_miss();
                }
                if v2.is_some() {
                    record_subscript_hit();
                } else {
                    record_subscript_miss();
                }
                None
            }
        }
    })
}

/// Retrieve a cached subscript value for a given state fingerprint and tag.
///
/// Returns `None` if the value is not in the cache.
pub(super) fn get_subscript_value_cached(fp: Fingerprint, tag: u32) -> Option<Value> {
    SUBSCRIPT_VALUE_CACHE.with(|cache| {
        let result = cache.borrow().get(&(fp, tag)).cloned();
        if result.is_some() {
            record_subscript_hit();
        } else {
            record_subscript_miss();
        }
        result
    })
}

/// Evaluate whether the subscript expression changed between two states.
/// Returns true iff subscript(s1) ≠ subscript(s2)
///
/// When `cache_tag` is Some, caches individual subscript values by
/// (fingerprint, tag), eliminating redundant evaluations across transitions
/// that share the same state (#2364). This also preserves SUBST_CACHE
/// warmth for subsequent ActionPred evaluations by avoiding state_env=None
/// context switches when both values are cache hits.
pub(super) fn eval_subscript_changed(
    ctx: &EvalCtx,
    s1: &State,
    s2: &State,
    subscript: &tla_core::Spanned<tla_core::ast::Expr>,
    cache_tag: Option<u32>,
) -> EvalResult<bool> {
    let debug = super::debug_subscript();
    if debug {
        eprintln!(
            "[DEBUG SUBSCRIPT] Evaluating subscript: {:?}",
            subscript.node
        );
        eprintln!(
            "[DEBUG SUBSCRIPT] s1 vars: {:?}",
            s1.vars()
                .map(|(k, v)| (k.to_string(), v.clone()))
                .collect::<Vec<_>>()
        );
        eprintln!(
            "[DEBUG SUBSCRIPT] s2 vars: {:?}",
            s2.vars()
                .map(|(k, v)| (k.to_string(), v.clone()))
                .collect::<Vec<_>>()
        );
    }

    let fp1 = s1.fingerprint();
    let fp2 = s2.fingerprint();

    // Try cache for val1
    let val1 = if let Some(v) = cache_tag.and_then(|tag| get_subscript_value_cached(fp1, tag)) {
        v
    } else {
        // Fix #2780: Clear SUBST_CACHE before evaluating val1 via with_explicit_env
        // (state_env=None, pointer 0). A prior call's val2 evaluation may have left
        // entries keyed on the same pointer 0, causing stale hits here.
        crate::eval::clear_subst_cache();
        // Build environment from s1 (current state).
        //
        // Preserve base env bindings (constants/config overrides like `Node`) and
        // overlay state vars for this concrete state.
        let mut env1 = ctx.env().clone();
        for (name, value) in s1.vars() {
            // Part of #2144: skip state vars that shadow local bindings.
            if !ctx.has_local_binding(name.as_ref()) {
                env1.insert(Arc::clone(name), value.clone());
            }
        }
        let ctx1 = ctx.with_explicit_env(env1);
        let v = crate::eval::eval_entry(&ctx1, subscript)?;
        if let Some(tag) = cache_tag {
            set_subscript_value_cache(fp1, tag, v.clone());
        }
        v
    };

    // Try cache for val2
    let val2 = if let Some(v) = cache_tag.and_then(|tag| get_subscript_value_cached(fp2, tag)) {
        v
    } else {
        // Clear SUBST_CACHE before evaluating val2 via with_explicit_env (state_env=None).
        // Required when val1 was also evaluated via with_explicit_env (both have pointer
        // identity 0, so eval_entry's pointer-based invalidation sees "same state").
        // Also clear defensively when val1 was cached but val2 is not: the SUBST_CACHE
        // may contain entries from a prior with_explicit_env call (same pointer 0),
        // and the pre-population invariant (all fps cached) is not enforced here.
        crate::eval::clear_subst_cache();
        // Build environment from s2 (next state) with the same base-env preservation.
        let mut env2 = ctx.env().clone();
        for (name, value) in s2.vars() {
            // Part of #2144: skip state vars that shadow local bindings.
            if !ctx.has_local_binding(name.as_ref()) {
                env2.insert(Arc::clone(name), value.clone());
            }
        }
        let ctx2 = ctx.with_explicit_env(env2);
        let v = crate::eval::eval_entry(&ctx2, subscript)?;
        if let Some(tag) = cache_tag {
            set_subscript_value_cache(fp2, tag, v.clone());
        }
        v
    };

    if debug {
        eprintln!(
            "[DEBUG SUBSCRIPT] val1={}, val2={}, changed={}",
            val1,
            val2,
            val1 != val2
        );
    }

    // Compare values
    Ok(val1 != val2)
}

/// Get-or-eval a subscript value for the array-native inline BFS path.
///
/// Checks the `(Fingerprint, tag)` subscript cache first. On cache miss,
/// evaluates the subscript expression with the same binding contract as
/// `eval_subscript_changed_array_uncached` in `inline_leaf_eval.rs`:
/// 1. Apply liveness bindings if present (#2116 contract)
/// 2. Bind the array state via `bind_state_array_guard`
/// 3. Clear next_state_env (subscript evaluates current state only)
/// 4. Clear SUBST_CACHE (prevent stale entries from prior state)
/// 5. Evaluate with `eval_entry`
///
/// Part of #3100 Phase A0: inline subscript value caching.
fn get_or_eval_subscript_value_array(
    ctx: &EvalCtx,
    fp: Fingerprint,
    array: &ArrayState,
    subscript: &Arc<tla_core::Spanned<tla_core::ast::Expr>>,
    bindings: Option<&BindingChain>,
    tag: u32,
) -> EvalResult<Value> {
    // Fast path: cache hit
    if let Some(v) = get_subscript_value_cached(fp, tag) {
        return Ok(v);
    }

    // Slow path: evaluate and cache.
    let mut eval_ctx = match bindings {
        Some(chain) => ctx.with_liveness_bindings(chain),
        None => ctx.clone(),
    };
    let _state_guard = eval_ctx.bind_state_env_guard(array.env_ref());
    let _ = eval_ctx.next_state_mut().take();
    let _next_guard = eval_ctx.take_next_state_env_guard();
    crate::eval::clear_subst_cache();
    let v = crate::eval::eval_entry(&eval_ctx, subscript)?;

    set_subscript_value_cache(fp, tag, v.clone());
    Ok(v)
}

/// Cached subscript change comparison for the array-native inline BFS path.
///
/// Replaces `eval_subscript_changed_array_uncached` by caching individual
/// subscript values by `(Fingerprint, tag)`. Reduces subscript evaluations
/// from two per comparison to one per previously unseen `(Fingerprint, tag)`.
///
/// The cache is shared with the post-BFS liveness path and cleared at the
/// start of `populate_node_check_masks` via `clear_subscript_value_cache`.
///
/// Part of #3100 Phase A0: inline subscript value caching.
#[allow(clippy::too_many_arguments)]
pub(crate) fn eval_subscript_changed_array_cached(
    ctx: &EvalCtx,
    current_fp: Fingerprint,
    current_array: &ArrayState,
    next_fp: Fingerprint,
    next_array: &ArrayState,
    subscript: &Arc<tla_core::Spanned<tla_core::ast::Expr>>,
    bindings: Option<&BindingChain>,
    tag: u32,
) -> EvalResult<bool> {
    let val1 = get_or_eval_subscript_value_array(
        ctx,
        current_fp,
        current_array,
        subscript,
        bindings,
        tag,
    )?;
    let val2 =
        get_or_eval_subscript_value_array(ctx, next_fp, next_array, subscript, bindings, tag)?;
    Ok(val1 != val2)
}
