// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Quantifier evaluation (`\A`, `\E`, `CHOOSE`) and hoist/subset-fast-path helpers.
//!
//! Reusable bound-variable binding helpers are in `bound_bindings.rs`.
//! Set builder/filter functions are in `set_construction.rs`.
//! Extracted from `helpers/mod.rs` as part of #1669.
//! Binding helpers extracted to `bound_bindings.rs` as part of #3425.

// Re-export binding helpers so existing sibling imports don't need changes.
pub use super::bound_bindings::push_bound_var_mut;
pub(crate) use super::bound_bindings::{
    into_bind_local_bound_var, into_bind_local_bound_var_cached, push_bound_var_mut_preinterned,
    push_bound_var_owned_preinterned, PreInternedBound,
};

use super::super::{eval, EvalCtx, EvalError, EvalResult};
use super::bound_var_ops::{BoundVarOps, PreparedBound};
use super::set_semantics::{eval_iter_set, eval_iter_set_tlc_normalized_inline, try_stream_setpred};
use crate::cache::{
    enter_quantifier_hoist_scope, mark_hoistable, OpDepGuard, QuantifierHoistScopeGuard,
};
use crate::eval_sets::value_subseteq;
use crate::value::Value;
use num_traits::Zero;
use rustc_hash::FxHashSet;
use tla_core::ast::{BoundPattern, BoundVar, Expr};
use tla_core::name_intern::NameId;
use tla_core::{Span, Spanned};

/// Part of #3128, #3364: Quantifier subexpression hoisting.
///
/// DISABLED: Hoisting causes correctness bugs when TIR-level hoist scopes
/// (from outer Exists/Forall) interact with AST-level evaluation of nested
/// user-defined operators containing CHOOSE with universally-quantified
/// uniqueness checks (e.g., SlidingPuzzles ChooseOne). The hoist shield-frame
/// mechanism was intended to prevent cross-scope cache contamination, but
/// a subtle interaction causes CHOOSE to incorrectly fail.
///
/// TLC has zero quantifier subexpression hoisting (Tool.java:2201-2232 is a
/// simple loop), so disabling this matches TLC's evaluation model exactly.
/// Performance impact is negligible — the interpreter overhead (2-8x TLC) is
/// inherent and not addressable by expression-level caching.
pub(crate) const HOIST_ENABLED: bool = false;

/// Collect all bound variable names from a slice of BoundVar, including pattern names.
fn collect_all_bound_names(bounds: &[BoundVar]) -> FxHashSet<&str> {
    let mut names = FxHashSet::default();
    for b in bounds {
        names.insert(b.name.node.as_str());
        if let Some(BoundPattern::Tuple(vars)) = &b.pattern {
            for v in vars {
                names.insert(v.node.as_str());
            }
        } else if let Some(BoundPattern::Var(v)) = &b.pattern {
            names.insert(v.node.as_str());
        }
    }
    names
}

fn simple_bound_name(bound: &BoundVar) -> Option<&str> {
    match &bound.pattern {
        Some(BoundPattern::Tuple(_)) => None,
        Some(BoundPattern::Var(var)) => Some(var.node.as_str()),
        None => Some(bound.name.node.as_str()),
    }
}

fn simple_bound_name_id(pre: &PreInternedBound) -> Option<NameId> {
    pre.simple.as_ref().map(|(_, id)| *id)
}

fn try_eval_forall_subset_fast_path(
    ctx: &mut EvalCtx,
    first: &BoundVar,
    pre: &PreInternedBound,
    domain_value: &Value,
    domain_span: Span,
    body: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    let Some(bound_name) = simple_bound_name(first) else {
        return Ok(None);
    };
    let Some(bound_name_id) = simple_bound_name_id(pre) else {
        return Ok(None);
    };
    let Expr::In(elem_expr, set_expr) = &body.node else {
        return Ok(None);
    };
    let Expr::Ident(name, _) = &elem_expr.node else {
        return Ok(None);
    };
    if name != bound_name {
        return Ok(None);
    }

    // Preserve vacuous-truth semantics: `\A x \in {} : body` must return TRUE
    // without evaluating `body`, even when the RHS set expression would error.
    let Some(domain_len) = domain_value.set_len() else {
        return Ok(None);
    };
    if domain_len.is_zero() {
        return Ok(Some(Value::Bool(true)));
    }

    let mut domain_iter = eval_iter_set(ctx, domain_value, Some(domain_span))?;
    let Some(first_elem) = domain_iter.next() else {
        return Ok(Some(Value::Bool(true)));
    };

    let mark = ctx.mark_stack();
    push_bound_var_mut_preinterned(ctx, first, &first_elem, span, Some(pre))?;
    // Track reads locally so we can detect whether the RHS closes over the
    // current bound variable without merging those deps into any outer cache frame.
    let dep_guard = OpDepGuard::from_ctx(ctx, ctx.binding_depth);
    let rhs_eval = eval(ctx, set_expr);
    let rhs_deps = dep_guard.try_take_deps();
    ctx.pop_to_mark(&mark);

    let (rhs_value, rhs_deps) = match (rhs_eval, rhs_deps) {
        (Ok(value), Some(deps)) => (value, deps),
        (Err(error), Some(_)) => return Err(error),
        (Ok(_), None) => {
            return Err(EvalError::Internal {
                message: "subset fast path dependency tracking stack unexpectedly empty".into(),
                span: Some(set_expr.span),
            });
        }
        (Err(error), None) => return Err(error),
    };
    if rhs_deps.inconsistent
        || crate::cache::dep_tracking::dep_map_contains_key(&rhs_deps.local, &bound_name_id)
    {
        return Ok(None);
    }

    Ok(Some(Value::Bool(value_subseteq(
        ctx,
        domain_value,
        &rhs_value,
        Some(domain_span),
        Some(set_expr.span),
    )?)))
}

/// Compute and enter a quantifier hoist scope for the given body and bounds.
/// Returns the scope guard (if any hoistable expressions were found).
///
/// Part of #3128: Cache key is (body_ptr, bounds_ptr). The bounds_ptr changes
/// for recursive eval_forall/eval_exists calls (bounds[1..] has a different
/// slice address), ensuring the cache correctly distinguishes different
/// bound variable sets for the same body expression.
pub(crate) fn enter_hoist_scope(
    body: &Expr,
    bounds: &[BoundVar],
) -> Option<QuantifierHoistScopeGuard> {
    if !HOIST_ENABLED {
        return None;
    }
    let bound_names = collect_all_bound_names(bounds);
    let cache_key = (body as *const Expr as usize, bounds.as_ptr() as usize);
    let hoistable = mark_hoistable(body, &bound_names, cache_key);
    enter_quantifier_hoist_scope(hoistable)
}

/// Shared forall/exists evaluation for a single bound variable.
pub(crate) fn eval_quantifier_single<
    B: BoundVarOps,
    E: FnMut(&mut EvalCtx) -> EvalResult<Value>,
>(
    ctx: &mut EvalCtx,
    var: &B,
    domain: &Value,
    eval_body: &mut E,
    body_span: Option<Span>,
    span: Option<Span>,
    short_circuit_on: bool,
) -> EvalResult<Value> {
    // Part of #3978: Try streaming SetPred iteration to enable short-circuit
    // without full materialization. For EXISTS over `{f \in [S->S] : P(f)}`,
    // this avoids evaluating P(f) for all f when a match is found early.
    //
    // Note: Streaming SetPred yields elements in source order (not TLC-normalized).
    // This is correct for EXISTS and FORALL which are order-independent. CHOOSE
    // uses eval_choose_single which does NOT call this function.
    //
    // On error, fall through to the materializing path which will produce the
    // same error (both paths do context restoration). On Ok(None), the value
    // is not a SetPred or has special optimizations that require materialization.
    if matches!(domain, Value::SetPred(_)) {
        if let Some(stream_iter) = try_stream_setpred(ctx, domain, var.domain_span())? {
            return eval_quantifier_single_streaming(
                ctx,
                var,
                stream_iter,
                eval_body,
                body_span,
                span,
                short_circuit_on,
            );
        }
        // Ok(None): SetPred has special optimizations (SUBSET filter, K-subset,
        // funcset partition) that require full materialization. Fall through.
    }

    let mark = ctx.mark_stack();

    if var.is_simple() {
        let mut first_iter = true;
        // Part of #3364: Use inline iterator to avoid Box<dyn Iterator> heap allocation.
        for elem in eval_iter_set_tlc_normalized_inline(ctx, domain, var.domain_span())? {
            if first_iter {
                var.push_binding_owned(ctx, elem, span)?;
                first_iter = false;
            } else {
                ctx.update_last_binding_value(elem);
            }
            let result = eval_body(ctx)?;
            let b = result
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", &result, body_span))?;
            if b == short_circuit_on {
                ctx.pop_to_mark(&mark);
                return Ok(Value::Bool(short_circuit_on));
            }
        }
        ctx.pop_to_mark(&mark);
    } else {
        for elem in eval_iter_set_tlc_normalized_inline(ctx, domain, var.domain_span())? {
            var.push_binding(ctx, &elem, span)?;
            let result = eval_body(ctx)?;
            ctx.pop_to_mark(&mark);
            let b = result
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", &result, body_span))?;
            if b == short_circuit_on {
                return Ok(Value::Bool(short_circuit_on));
            }
        }
    }

    Ok(Value::Bool(!short_circuit_on))
}

/// Streaming variant of `eval_quantifier_single` for SetPred domains.
///
/// Part of #3978: Uses a `SetPredStreamIter` that evaluates the SetPred predicate
/// on-demand per source element, enabling short-circuit exit without materializing
/// the full filtered set. The streaming iterator yields `EvalResult<Value>` to
/// propagate predicate evaluation errors.
fn eval_quantifier_single_streaming<
    B: BoundVarOps,
    E: FnMut(&mut EvalCtx) -> EvalResult<Value>,
>(
    ctx: &mut EvalCtx,
    var: &B,
    mut stream_iter: super::set_semantics::SetPredStreamIter,
    eval_body: &mut E,
    body_span: Option<Span>,
    span: Option<Span>,
    short_circuit_on: bool,
) -> EvalResult<Value> {
    let mark = ctx.mark_stack();

    if var.is_simple() {
        let mut first_iter = true;
        while let Some(elem_result) = stream_iter.next() {
            let elem = elem_result?;
            if first_iter {
                var.push_binding_owned(ctx, elem, span)?;
                first_iter = false;
            } else {
                ctx.update_last_binding_value(elem);
            }
            let result = eval_body(ctx)?;
            let b = result
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", &result, body_span))?;
            if b == short_circuit_on {
                ctx.pop_to_mark(&mark);
                return Ok(Value::Bool(short_circuit_on));
            }
        }
        ctx.pop_to_mark(&mark);
    } else {
        while let Some(elem_result) = stream_iter.next() {
            let elem = elem_result?;
            var.push_binding(ctx, &elem, span)?;
            let result = eval_body(ctx)?;
            ctx.pop_to_mark(&mark);
            let b = result
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", &result, body_span))?;
            if b == short_circuit_on {
                return Ok(Value::Bool(short_circuit_on));
            }
        }
    }

    Ok(Value::Bool(!short_circuit_on))
}

/// Shared CHOOSE evaluation for a single bound variable.
pub(crate) fn eval_choose_single<B: BoundVarOps, E: FnMut(&mut EvalCtx) -> EvalResult<Value>>(
    ctx: &mut EvalCtx,
    var: &B,
    domain: &Value,
    eval_body: &mut E,
    body_span: Option<Span>,
    span: Option<Span>,
) -> EvalResult<Value> {
    let mark = ctx.mark_stack();

    if var.is_simple() {
        let mut first_iter = true;
        // Part of #3364: Use inline iterator to avoid Box<dyn Iterator> heap allocation.
        for elem in eval_iter_set_tlc_normalized_inline(ctx, domain, var.domain_span())? {
            if first_iter {
                var.push_binding(ctx, &elem, span)?;
                first_iter = false;
            } else {
                ctx.update_last_binding_value(elem.clone());
            }
            let result = eval_body(ctx)?;
            let b = result
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", &result, body_span))?;
            if b {
                ctx.pop_to_mark(&mark);
                return Ok(elem);
            }
        }
        ctx.pop_to_mark(&mark);
    } else {
        for elem in eval_iter_set_tlc_normalized_inline(ctx, domain, var.domain_span())? {
            var.push_binding(ctx, &elem, span)?;
            let result = eval_body(ctx)?;
            ctx.pop_to_mark(&mark);
            let b = result
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", &result, body_span))?;
            if b {
                return Ok(elem);
            }
        }
    }

    Err(EvalError::ChooseFailed { span })
}

/// Evaluate \A bounds : body
/// Uses O(1) mutable stack binding instead of O(n) context cloning per element.
///
/// Part of #3063 Phase E: For simple (non-tuple) bindings, reuses the binding
/// node across iterations via `update_last_binding_value` (1 allocation for N
/// elements instead of N allocations). Tuple patterns still push/pop per element.
pub(crate) fn eval_forall(
    ctx: &mut EvalCtx,
    bounds: &[BoundVar],
    body: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Value> {
    if bounds.is_empty() {
        return eval(ctx, body);
    }

    let first = &bounds[0];
    let domain = first.domain.as_ref().ok_or_else(|| EvalError::Internal {
        message: "Forall requires bounded quantification".into(),
        span,
    })?;
    let prepared = PreparedBound::new(first);
    let dv = prepared.eval_domain(ctx, "Forall", span)?;

    if let Some(result) =
        try_eval_forall_subset_fast_path(ctx, first, prepared.pre(), &dv, domain.span, body, span)?
    {
        return Ok(result);
    }

    // Part of #3128: Hoist bound-variable-invariant subexpressions.
    // Compute once before the loop; the guard pops on scope exit.
    let _hoist_guard = enter_hoist_scope(&body.node, bounds);
    // Sync hoist shadow flag so eval_expr checks the shadow instead of TLS.
    ctx.runtime_state
        .hoist_active
        .set(crate::cache::is_hoist_active());

    eval_quantifier_single(
        ctx,
        &prepared,
        &dv,
        &mut |local_ctx| eval_forall(local_ctx, &bounds[1..], body, span),
        Some(body.span),
        span,
        false,
    )
}

/// Evaluate \E bounds : body
/// Uses O(1) mutable stack binding instead of O(n) context cloning per element.
///
/// Part of #3063 Phase E: For simple (non-tuple) bindings, reuses the binding
/// node across iterations via `update_last_binding_value`.
pub(crate) fn eval_exists(
    ctx: &mut EvalCtx,
    bounds: &[BoundVar],
    body: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Value> {
    if bounds.is_empty() {
        return eval(ctx, body);
    }

    let first = &bounds[0];
    let prepared = PreparedBound::new(first);
    let dv = prepared.eval_domain(ctx, "Exists", span)?;

    // Part of #3128: Hoist bound-variable-invariant subexpressions.
    let _hoist_guard = enter_hoist_scope(&body.node, bounds);
    ctx.runtime_state
        .hoist_active
        .set(crate::cache::is_hoist_active());

    eval_quantifier_single(
        ctx,
        &prepared,
        &dv,
        &mut |local_ctx| eval_exists(local_ctx, &bounds[1..], body, span),
        Some(body.span),
        span,
        true,
    )
}

/// Evaluate CHOOSE x \in S : P
///
/// Part of #2955: Takes `&EvalCtx` instead of `&mut EvalCtx`. The CHOOSE TRUE fast
/// path (GameOfLife: ~8.4M calls) needs no mutable context — the ctx.clone() from
/// the dispatch site was pure waste. The general path clones internally only when needed.
///
/// Per-state CHOOSE memoization (two tiers):
/// - Tier 1 (shallow): `binding_depth == 0` — cache by (expr_ptr, instance_subs_id).
///   Same as before: no bindings in scope, so expression identity suffices.
/// - Tier 2 (deep, Part of #3905): `binding_depth > 0` — cache by
///   (expr_ptr, instance_subs_id, domain_hash, bindings_hash). Enables CHOOSE caching
///   inside quantifiers for specs like MultiPaxos (29.4x → <5x vs TLC).
///   For CHOOSE TRUE, bindings_hash is 0 (predicate is trivially true, result depends
///   only on domain).
///
/// Both tiers are cleared at every state boundary by `clear_state_boundary_core_impl`.
pub(crate) fn eval_choose(
    ctx: &EvalCtx,
    bound: &BoundVar,
    body: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Value> {
    let expr_ptr = body as *const Spanned<Expr> as usize;
    let instance_subs_id = crate::cache::scope_ids::resolve_instance_subs_id(
        ctx.scope_ids.instance_substitutions,
        &ctx.instance_substitutions,
    );
    let state_identity = ctx.state_env.map_or(0, |s| s.identity());

    // Tier 1 (shallow): binding_depth == 0 — check existing cache.
    // Defense-in-depth: state_identity (state_env pointer) is included in the
    // key so stale entries from a different state never match (#3939).
    let shallow_cacheable = ctx.binding_depth == 0;
    if shallow_cacheable {
        if let Some(cached) =
            crate::cache::choose_cache_lookup(expr_ptr, instance_subs_id, state_identity)
        {
            return Ok(cached);
        }
    }

    let domain = bound
        .domain
        .as_ref()
        .ok_or(EvalError::ChooseUnbounded { span })?;

    let dv = eval(ctx, domain)?;

    // Part of #2955: Fast path for CHOOSE x \in S : TRUE — find TLC-minimum element
    // in O(n) instead of O(n log n) full sort. Saves ~66% of comparisons for small sets.
    // No ctx mutation needed — avoids ~8.4M ctx.clone() calls on GameOfLife.
    if matches!(&body.node, Expr::Bool(true)) {
        // Part of #3905: For CHOOSE TRUE at any depth, check deep cache with bindings_hash=0
        // (predicate is trivially true, doesn't depend on outer bindings).
        if !shallow_cacheable {
            let domain_hash = crate::cache::hash_value_for_choose(&dv);
            let deep_key = crate::cache::ChooseDeepKey {
                expr_ptr,
                instance_subs_id,
                domain_hash,
                bindings_hash: 0,
                state_identity,
            };
            if let Some(cached) = crate::cache::choose_deep_cache_lookup(&deep_key) {
                return Ok(cached);
            }
            // Part of #3978: For SetPred domains, tlc_first_element() fails because
            // Value::iter_set() returns None for SetPred (needs eval context).
            // Materialize via eval_iter_set and find TLC-minimum.
            let result = if matches!(dv, Value::SetPred(_)) {
                eval_choose_true_setpred_streaming(ctx, &dv, domain.span, span)?
            } else {
                dv
                    .tlc_first_element()?
                    .ok_or(EvalError::ChooseFailed { span })?
            };
            crate::cache::choose_deep_cache_store(deep_key, result.clone());
            return Ok(result);
        }
        // Part of #3978: For SetPred domains, use streaming TLC-minimum scan.
        let result = if matches!(dv, Value::SetPred(_)) {
            eval_choose_true_setpred_streaming(ctx, &dv, domain.span, span)?
        } else {
            dv
                .tlc_first_element()?
                .ok_or(EvalError::ChooseFailed { span })?
        };
        crate::cache::choose_cache_store(expr_ptr, instance_subs_id, state_identity, result.clone());
        return Ok(result);
    }

    // Part of #3905: Tier 2 (deep) cache for general CHOOSE at binding_depth > 0.
    // Key includes domain_hash + bindings_hash to distinguish different binding contexts.
    let deep_key = if !shallow_cacheable {
        let domain_hash = crate::cache::hash_value_for_choose(&dv);
        let bindings_hash = crate::cache::hash_bindings_for_choose(ctx);
        let key = crate::cache::ChooseDeepKey {
            expr_ptr,
            instance_subs_id,
            domain_hash,
            bindings_hash,
            state_identity,
        };
        if let Some(cached) = crate::cache::choose_deep_cache_lookup(&key) {
            return Ok(cached);
        }
        Some(key)
    } else {
        None
    };

    // General path: need mutable context for push_binding/pop_to_mark
    let mut local_ctx = ctx.clone();
    let prepared = PreparedBound::new(bound);

    // Part of #3128: Hoist bound-variable-invariant subexpressions in CHOOSE.
    let _hoist_guard = enter_hoist_scope(&body.node, std::slice::from_ref(bound));
    local_ctx
        .runtime_state
        .hoist_active
        .set(crate::cache::is_hoist_active());

    let result = eval_choose_single(
        &mut local_ctx,
        &prepared,
        &dv,
        &mut |eval_ctx| eval(eval_ctx, body),
        Some(body.span),
        span,
    )?;

    if shallow_cacheable {
        crate::cache::choose_cache_store(expr_ptr, instance_subs_id, state_identity, result.clone());
    } else if let Some(key) = deep_key {
        crate::cache::choose_deep_cache_store(key, result.clone());
    }

    Ok(result)
}

/// Find the TLC-first element for `CHOOSE x \in SetPred : TRUE`.
///
/// Part of #3978: `Value::tlc_first_element()` fails for SetPred domains because
/// `Value::iter_set()` returns `None` for SetPred (it needs an eval context to
/// evaluate the predicate). This function materializes the SetPred via
/// `eval_iter_set`, builds a concrete `Value::Set`, and delegates to
/// `tlc_first_element()` which finds the TLC-minimum in O(n) time.
///
/// CHOOSE TRUE must see all elements to find the minimum (it can't short-circuit),
/// so the main benefit here is correctness (avoiding SetTooLarge error) rather
/// than avoiding materialization.
fn eval_choose_true_setpred_streaming(
    ctx: &EvalCtx,
    dv: &Value,
    domain_span: Span,
    span: Option<Span>,
) -> EvalResult<Value> {
    // Materialize via eval_iter_set (handles SetPred predicate evaluation),
    // build a concrete Value::Set, and delegate to tlc_first_element for the
    // O(n) TLC-minimum scan.
    let elements: Vec<Value> = eval_iter_set(ctx, dv, Some(domain_span))?.collect();
    let materialized = Value::set(elements);
    materialized
        .tlc_first_element()?
        .ok_or(EvalError::ChooseFailed { span })
}
