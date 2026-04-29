// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Zero-arg LET cache classification, replay, and dep hashing.
//!
//! Owns `CONST_LET_CACHE`, `PARAM_LET_CACHE`, and `NON_CONST_LET_SET`
//! lookup/insertion logic including the `instance_lazy_read` guards (#3465).
//!
//! Extracted from `eval_let.rs` for file size compliance (#3474).

use crate::cache::{
    eval_with_dep_tracking_unpropagated, is_dep_tracking_active, propagate_cached_deps,
    small_caches::{let_scope_key, LetScopeKey},
    OpEvalDeps, StateLookupMode, SMALL_CACHES,
};
use crate::error::EvalResult;
use crate::eval;
use crate::value::Value;
use crate::EvalCtx;
use std::hash::{Hash, Hasher};
use tla_core::ast::Expr;
use tla_core::name_intern::NameId;
use tla_core::Spanned;

/// Tier 1.5 param-only cache: lookup by dep hash + equality, eval on miss.
///
/// Part of #3034: Uses hash for fast filtering, then verifies structural equality
/// of dep values to prevent silent correctness bugs from 64-bit hash collisions.
///
/// Returns `Some(Ok(val))` on cache hit, `Some(Err(...))` on eval error,
/// `None` if deps can't be hashed (unforced lazy bindings).
fn param_cache_lookup_or_eval(
    ctx: &EvalCtx,
    body: &Spanned<Expr>,
    cache_key: LetScopeKey,
    dep_names: &[NameId],
) -> Option<EvalResult<Value>> {
    let (dep_hash, dep_vals) = compute_dep_hash_and_values(ctx, dep_names)?;
    // Part of #3962: Access param_let_cache via consolidated SMALL_CACHES.
    let cached = SMALL_CACHES.with(|sc| {
        sc.borrow()
            .param_let_cache
            .get(&cache_key)
            .and_then(|entries| {
                entries.iter().find_map(|(h, stored_deps, v)| {
                    if *h == dep_hash && *stored_deps == dep_vals {
                        Some(v.clone())
                    } else {
                        None
                    }
                })
            })
    });
    if let Some(val) = cached {
        propagate_param_cache_hit_deps(dep_names, &dep_vals, ctx);
        return Some(Ok(val));
    }

    // Re-run dep tracking on misses so branch-sensitive LET bodies can widen
    // their local dep key set if a later evaluation reads additional locals.
    // If the miss reveals state/next deps, declassify the entry to Tier 2.
    let (val, deps) = match eval_zero_arg_let_with_deps(ctx, body) {
        Ok(result) => result,
        Err(e) => return Some(Err(e)),
    };
    if param_cacheable_deps(&deps) {
        let widened_dep_names = merge_param_dep_names(dep_names, &deps);
        if widened_dep_names != dep_names {
            // Part of #3962: Single TLS access for widened dep update.
            SMALL_CACHES.with(|sc| {
                let mut sc = sc.borrow_mut();
                sc.param_let_deps
                    .insert(cache_key, widened_dep_names.clone());
                sc.param_let_cache.remove(&cache_key);
            });
        }
        if force_lazy_deps(ctx, &widened_dep_names).is_err() {
            return Some(Ok(val));
        }
        if let Some((dep_hash, dep_vals)) = compute_dep_hash_and_values(ctx, &widened_dep_names) {
            SMALL_CACHES.with(|sc| {
                let mut sc = sc.borrow_mut();
                let entries = sc.param_let_cache.entry(cache_key).or_insert_with(Vec::new);
                if entries.len() < 256 {
                    entries.push((dep_hash, dep_vals, val.clone()));
                }
            });
        }
        return Some(Ok(val));
    }

    // Part of #3962: Single TLS access for declassification to Tier 2.
    SMALL_CACHES.with(|sc| {
        let mut sc = sc.borrow_mut();
        sc.param_let_deps.remove(&cache_key);
        sc.param_let_cache.remove(&cache_key);
        sc.non_const_let_set.insert(cache_key);
    });
    Some(Ok(val))
}

#[inline]
fn propagate_param_cache_hit_deps(dep_names: &[NameId], dep_vals: &[Value], ctx: &EvalCtx) {
    debug_assert_eq!(
        dep_names.len(),
        dep_vals.len(),
        "param LET cache hit deps must keep names and values aligned"
    );
    if dep_names.is_empty() || dep_names.len() != dep_vals.len() {
        return;
    }
    let mut deps = OpEvalDeps::default();
    for (name_id, value) in dep_names.iter().zip(dep_vals.iter()) {
        deps.record_local(*name_id, value);
    }
    propagate_cached_deps(ctx, &deps);
}

#[inline]
fn finalize_zero_arg_let_deps(ctx: &EvalCtx, mut deps: OpEvalDeps) -> OpEvalDeps {
    deps.strip_internal_locals(&ctx.bindings, ctx.binding_depth);
    deps
}

#[inline]
fn eval_zero_arg_let_with_deps(
    ctx: &EvalCtx,
    body: &Spanned<Expr>,
) -> EvalResult<(Value, OpEvalDeps)> {
    let (val, deps) = eval_with_dep_tracking_unpropagated(ctx, body)?;
    let deps = finalize_zero_arg_let_deps(ctx, deps);
    propagate_cached_deps(ctx, &deps);
    Ok((val, deps))
}

/// Evaluate a zero-arg LET body with four-tier constant caching.
///
/// Part of #2955: Avoids redundant re-evaluation of LET expressions.
///
/// Tier 1 (CONST_LET_CACHE): Fully constant (no deps) → cached permanently.
/// Tier 1.5 (PARAM_LET_CACHE): Local-only deps (no state/next) → cached by dep values.
///           For GameOfLife `points`, reduces 1M evaluations to 16 (one per unique `p`).
/// Tier 2 (NON_CONST_LET_SET): Has state deps → plain eval, no caching.
/// Tier 3 (first encounter): Probe with dep tracking to classify.
///
/// Fix #3095, Fix #3114: Cache key is now a LetScopeKey (body_ptr + local_ops_id +
/// instance_subs_id) to prevent cross-scope aliasing. Previously body_ptr alone.
pub(super) fn eval_zero_arg_let_body(ctx: &EvalCtx, body: &Spanned<Expr>) -> EvalResult<Value> {
    let body_ptr = body as *const Spanned<Expr> as usize;
    let cache_key = let_scope_key(ctx, body_ptr);

    // Part of #3962: Single TLS access for Tier 1 + Tier 1.5 + Tier 2 lookups.
    // Returns: (const_hit, param_deps, is_non_const)
    let (const_hit, param_deps, is_non_const) = SMALL_CACHES.with(|sc| {
        let sc = sc.borrow();
        if let Some(val) = sc.const_let_cache.get(&cache_key) {
            return (Some(val.clone()), None, false);
        }
        if let Some(dep_names) = sc.param_let_deps.get(&cache_key) {
            return (None, Some(dep_names.clone()), false);
        }
        if sc.non_const_let_set.contains(&cache_key) {
            return (None, None, true);
        }
        (None, None, false)
    });

    // Tier 1: Constant cache hit.
    if let Some(val) = const_hit {
        return Ok(val);
    }

    // Tier 1.5: Check param-only cache (local deps, no state deps).
    // Part of #2955: Force any unforced lazy deps before cache lookup.
    if let Some(dep_names) = param_deps {
        force_lazy_deps(ctx, &dep_names)?;
        return match param_cache_lookup_or_eval(ctx, body, cache_key, &dep_names) {
            Some(result) => result,
            None => eval(ctx, body), // Unreachable after forcing, but safe fallback
        };
    }

    // Tier 2: Known non-constant (has state deps) — skip dep tracking, use plain eval.
    if is_non_const {
        if is_dep_tracking_active(ctx) {
            let (val, _deps) = eval_zero_arg_let_with_deps(ctx, body)?;
            return Ok(val);
        }
        return eval(ctx, body);
    }

    // Tier 3: First encounter — probe with dep tracking.
    let (val, deps) = eval_zero_arg_let_with_deps(ctx, body)?;
    // Part of #3109: Skip all LET cache insertions during ENABLED scope.
    // Dep tracking may misclassify state-dependent results as constant when
    // state_env is None (ENABLED evaluation). TLC never caches during ENABLED.
    // Part of #3962: Read from EvalRuntimeState shadow instead of TLS.
    if crate::cache::lifecycle::in_enabled_scope_ctx(ctx) {
        // No-op: don't cache, don't mark as non-constant.
    } else if !deps.inconsistent
        && deps.local.is_empty()
        && deps.state.is_empty()
        && deps.next.is_empty()
        && deps.tlc_level.is_none()
        && !deps.instance_lazy_read
        // Fix #4145: LazyFuncValues that capture state are NOT constant even when
        // dep tracking shows no state reads during construction. FuncDef evaluation
        // creates the function value (O(1), no state reads) but the function BODY
        // reads state when later applied. If we cache the LazyFunc as constant,
        // subsequent LET evaluations in different states reuse the stale captured
        // state, and the LazyFunc's memo table accumulates entries across different
        // enclosing operator invocations, causing memo hits to bypass dep tracking.
        // VoteProof: SafeAt(b,v) contains LET SA[bb] = ... (recursive, reads maxBal/votes).
        // Without this guard: SA cached as constant → stale state → 4180 instead of 6962.
        && !value_captures_state(&val)
    {
        // Fix #3465: INSTANCE lazy deps are not constant.
        // Part of #3962: Access const_let_cache via consolidated SMALL_CACHES.
        SMALL_CACHES.with(|sc| {
            sc.borrow_mut()
                .const_let_cache
                .insert(cache_key, val.clone());
        });
    } else if !deps.inconsistent
        && !deps.state_next_inconsistent
        && deps.state.is_empty()
        && deps.next.is_empty()
        && !deps.local.is_empty()
        && !deps.instance_lazy_read
        // Fix #4145: Same guard as Tier 1 — LazyFunc with captured state must not
        // be stored in the param cache. The captured state makes it state-dependent
        // beyond what local dep tracking can capture.
        && !value_captures_state(&val)
    {
        // Fix #3465: INSTANCE lazy deps invalidate param cache.
        // Local-only deps: register in param cache (Tier 1.5)
        let mut dep_names: Vec<NameId> = deps.local.iter().map(|(k, _)| *k).collect();
        dep_names.sort_unstable();
        if let Some((dep_hash, dep_vals)) = compute_dep_hash_and_values(ctx, &dep_names) {
            // Part of #3962: Single TLS access for Tier 1.5 registration.
            SMALL_CACHES.with(|sc| {
                let mut sc = sc.borrow_mut();
                sc.param_let_deps.insert(cache_key, dep_names);
                sc.param_let_cache
                    .entry(cache_key)
                    .or_insert_with(Vec::new)
                    .push((dep_hash, dep_vals, val.clone()));
            });
        }
    } else {
        // Part of #3962: Access non_const_let_set via consolidated SMALL_CACHES.
        SMALL_CACHES.with(|sc| {
            sc.borrow_mut().non_const_let_set.insert(cache_key);
        });
    }
    Ok(val)
}

/// Force unforced lazy bindings in the dep list so they can be hashed.
/// Part of #2955: Without forcing, Tier 1.5 cache returns None on every call.
#[inline]
fn force_lazy_deps(ctx: &EvalCtx, dep_names: &[NameId]) -> EvalResult<()> {
    for name_id in dep_names {
        if let Some((bv, source)) = ctx.bindings.lookup(*name_id) {
            if bv.get_if_ready(StateLookupMode::Current, source).is_none() {
                if let Some(lazy) = bv.as_lazy() {
                    let mut eval_ctx = ctx.clone();
                    eval_ctx.bindings = lazy.enclosing.clone();
                    let value = eval(&eval_ctx, lazy.expr())?;
                    if !matches!(source, crate::binding_chain::BindingSourceRef::Instance(_)) {
                        lazy.set_cached(value, StateLookupMode::Current);
                    }
                }
            }
        }
    }
    Ok(())
}

#[inline]
fn param_cacheable_deps(deps: &crate::cache::OpEvalDeps) -> bool {
    !deps.inconsistent
        && !deps.state_next_inconsistent
        && deps.state.is_empty()
        && deps.next.is_empty()
        && !deps.local.is_empty()
        && !deps.instance_lazy_read
}

/// Fix #4145: Check if a value captures state and should not be treated as constant.
///
/// LazyFuncValues created from FuncDef expressions capture the current state via
/// `snapshot_state_envs()` at definition time. The function body reads state when
/// applied, but dep tracking during FuncDef construction sees no state reads (only
/// a pointer copy). This means the CONST_LET_CACHE would incorrectly classify such
/// values as constant, allowing a stale LazyFunc (with captured state from a
/// previous BFS state) to be reused. The stale memo table causes memo hits that
/// bypass dep tracking, leading to incomplete deps for enclosing N-ary cached
/// operators.
#[inline]
fn value_captures_state(val: &Value) -> bool {
    match val {
        Value::LazyFunc(f) => f.captured_state().is_some() || f.captured_next_state().is_some(),
        _ => false,
    }
}

#[inline]
fn merge_param_dep_names(dep_names: &[NameId], deps: &crate::cache::OpEvalDeps) -> Vec<NameId> {
    let mut merged = dep_names.to_vec();
    for (name_id, _) in &deps.local {
        if !merged.contains(name_id) {
            merged.push(*name_id);
        }
    }
    merged.sort_unstable();
    merged
}

/// Compute dep hash + values for Tier 1.5 param cache (Part of #3034).
/// Returns `None` if any dep is an unforced lazy binding (Part of #3030).
#[inline]
fn compute_dep_hash_and_values(ctx: &EvalCtx, dep_names: &[NameId]) -> Option<(u64, Vec<Value>)> {
    let mut hasher = rustc_hash::FxHasher::default();
    let mut dep_values = Vec::with_capacity(dep_names.len());
    for name_id in dep_names {
        name_id.hash(&mut hasher);
        match ctx.bindings.lookup(*name_id) {
            Some((bv, source)) => match bv.get_if_ready(StateLookupMode::Current, source) {
                Some(val) => {
                    val.hash(&mut hasher);
                    dep_values.push(val);
                }
                None => return None, // Un-forced lazy: cannot hash, skip cache
            },
            None => return None, // Absent: cannot hash, skip cache
        }
    }
    Some((hasher.finish(), dep_values))
}
