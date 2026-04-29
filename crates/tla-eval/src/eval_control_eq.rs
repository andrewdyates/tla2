// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Control flow (IF, CASE), equality, inequality, negation, range,
//! ENABLED, and nonempty-set optimization.
//!
//! Part of #3214: Split from eval_expr_helpers.rs.
//! Part of #3387: ENABLED result cache for per-state memoization.

use super::core::EvalCtx;
use super::hooks::enabled_hook;
use super::{eval, eval_iter_set, push_bound_var_mut, values_equal, EvalError, EvalResult};
use crate::binding_chain::BindingValueRef;
use crate::eval_cache_lifecycle::current_state_gen_ctx;
use crate::value::{range_set, Value};
use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use tla_core::{Span, Spanned};

// Part of #3387: ENABLED result cache for per-state memoization.
//
// ENABLED(Action) depends only on the action expression (AST pointer identity),
// the current state (identified by monotonic generation counter), and local
// bindings visible at the call site (e.g., quantifier variable `e`). It does
// NOT depend on the next-state (it existentially quantifies over successors).
// Fix #4055: State identity now uses centralized generation counter instead
// of raw pointer identity to avoid ABA vulnerability.

#[derive(Clone, PartialEq, Eq, Hash)]
struct EnabledCacheKey {
    action_ptr: usize,
    bindings_hash: u64,
}

/// Part of #3962: Consolidate 4 ENABLED_CACHE thread-locals into a single
/// struct to reduce TLS overhead. Previously each field was a separate
/// thread_local! — 4 TLS accesses per enabled_op call. Now consolidated
/// into 1 TLS access.
///
/// Fix #4055: Replaced `state_ptr: usize` with `last_state_gen: u64` to use
/// the centralized monotonic generation counter from `eval_cache_lifecycle`.
/// Raw pointer identity was vulnerable to ABA (allocator recycling addresses).
struct EnabledCacheState {
    cache: FxHashMap<EnabledCacheKey, bool>,
    /// Monotonic generation counter from centralized state identity tracking.
    /// Replaces `state_ptr: usize` which was vulnerable to ABA (#3447 series).
    last_state_gen: u64,
}

thread_local! {
    static ENABLED_CACHE_STATE: RefCell<EnabledCacheState> = RefCell::new(EnabledCacheState {
        cache: FxHashMap::default(),
        last_state_gen: u64::MAX,
    });
}

/// Clear the ENABLED result cache. Called from cache lifecycle management.
pub(crate) fn clear_enabled_result_cache() {
    ENABLED_CACHE_STATE.with(|c| {
        let mut s = c.borrow_mut();
        s.cache.clear();
        // Force re-check on next access by setting to sentinel.
        s.last_state_gen = u64::MAX;
    });
}

/// Compute a hash of the local (eager) bindings in the binding chain.
fn hash_local_bindings(ctx: &EvalCtx) -> u64 {
    let mut hasher = rustc_hash::FxHasher::default();
    let mut count: u32 = 0;
    for (name_id, value, source) in ctx.bindings.iter() {
        match source {
            crate::binding_chain::BindingSourceRef::Local(_)
            | crate::binding_chain::BindingSourceRef::Liveness(_) => {}
            _ => continue,
        }
        if let BindingValueRef::Eager(cv) = value {
            name_id.hash(&mut hasher);
            cv.hash(&mut hasher);
            count += 1;
        }
    }
    count.hash(&mut hasher);
    hasher.finish()
}

/// Evaluate the ENABLED operator: true iff the action has at least one successor.
///
/// Part of #3387: Results are cached per (action_ptr, bindings) within the
/// same state. Fix #4055: Uses monotonic state generation counter for
/// invalidation instead of raw pointer identity (ABA-vulnerable).
pub(super) fn eval_enabled_op(
    ctx: &EvalCtx,
    action: &Spanned<tla_core::ast::Expr>,
) -> EvalResult<Value> {
    // Part of #3962: All ENABLED cache state in a single TLS access.
    // Fix #4055: Use centralized monotonic generation counter instead of
    // raw state pointer identity, which is vulnerable to ABA (allocator
    // recycling the same address for a different state).
    let state_gen = current_state_gen_ctx(ctx);
    let action_ptr = &action.node as *const tla_core::ast::Expr as usize;
    let bindings_hash = hash_local_bindings(ctx);
    let key = EnabledCacheKey {
        action_ptr,
        bindings_hash,
    };

    let cached = ENABLED_CACHE_STATE.with(|cell| {
        let mut s = cell.borrow_mut();
        // Detect state change via monotonic generation counter.
        if s.last_state_gen != state_gen {
            s.last_state_gen = state_gen;
            s.cache.clear();
        }
        s.cache.get(&key).copied()
    });
    if let Some(result) = cached {
        return Ok(Value::Bool(result));
    }

    let hook = enabled_hook()?;
    let vars: Vec<Arc<str>> = ctx.shared.var_registry.names().to_vec();
    let mut eval_ctx = ctx.clone();
    eval_ctx.stable_mut().next_state = None;
    let result = hook(&mut eval_ctx, action, &vars)?;

    ENABLED_CACHE_STATE.with(|cell| {
        cell.borrow_mut().cache.insert(key, result);
    });

    Ok(Value::Bool(result))
}

/// Evaluate IF-THEN-ELSE.
#[inline]
pub(super) fn eval_if(
    ctx: &EvalCtx,
    cond: &Spanned<tla_core::ast::Expr>,
    then_branch: &Spanned<tla_core::ast::Expr>,
    else_branch: &Spanned<tla_core::ast::Expr>,
) -> EvalResult<Value> {
    let cv = eval(ctx, cond)?;
    let cb = cv
        .as_bool()
        .ok_or_else(|| EvalError::type_error("BOOLEAN", &cv, Some(cond.span)))?;
    if cb {
        eval(ctx, then_branch)
    } else {
        eval(ctx, else_branch)
    }
}

/// Evaluate a CASE expression with optional OTHER default.
pub(super) fn eval_case(
    ctx: &EvalCtx,
    arms: &[tla_core::ast::CaseArm],
    other: Option<&Spanned<tla_core::ast::Expr>>,
    span: Option<Span>,
) -> EvalResult<Value> {
    for arm in arms {
        let gv = eval(ctx, &arm.guard)?;
        let gb = gv
            .as_bool()
            .ok_or_else(|| EvalError::type_error("BOOLEAN", &gv, Some(arm.guard.span)))?;
        if gb {
            return eval(ctx, &arm.body);
        }
    }
    if let Some(default) = other {
        eval(ctx, default)
    } else {
        Err(EvalError::CaseNoMatch { span })
    }
}

/// Returns true if the value is a function-like variant (Func, IntFunc, LazyFunc).
fn is_func_like(v: &Value) -> bool {
    matches!(v, Value::Func(_) | Value::IntFunc(_) | Value::LazyFunc(_))
}

/// Evaluate equality.
#[inline]
pub(super) fn eval_eq(
    ctx: &EvalCtx,
    a: &Spanned<tla_core::ast::Expr>,
    b: &Spanned<tla_core::ast::Expr>,
    span: Option<Span>,
) -> EvalResult<Value> {
    let av = eval(ctx, a)?;
    let bv = eval(ctx, b)?;
    let eq = values_equal(ctx, &av, &bv, span)?;
    #[cfg(debug_assertions)]
    if !eq && {
        static DEBUG_IMPLIED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        *DEBUG_IMPLIED.get_or_init(|| std::env::var("TLA2_DEBUG_IMPLIED").is_ok())
    } {
        eprintln!("[EQ_FALSE] lhs={av} rhs={bv}");
        eprintln!("[EQ_FALSE]   lhs_debug={av:?}");
        eprintln!("[EQ_FALSE]   rhs_debug={bv:?}");
        eprintln!(
            "[EQ_FALSE]   lhs_expr={:?} rhs_expr={:?}",
            std::mem::discriminant(&a.node),
            std::mem::discriminant(&b.node)
        );
    }
    // #3147 debug instrumentation: print details when function-like values compare unequal.
    // Gated on TLA2_DEBUG_3147 env var. Works in both debug and release builds.
    if !eq && (is_func_like(&av) || is_func_like(&bv)) {
        static DEBUG_3147: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        let enabled = *DEBUG_3147.get_or_init(|| std::env::var("TLA2_DEBUG_3147").is_ok());
        if enabled {
            eprintln!("[DEBUG_3147] === Function equality returned FALSE ===");
            eprintln!(
                "[DEBUG_3147]   lhs discriminant: {:?}",
                std::mem::discriminant(&av)
            );
            eprintln!(
                "[DEBUG_3147]   rhs discriminant: {:?}",
                std::mem::discriminant(&bv)
            );
            eprintln!("[DEBUG_3147]   lhs display: {av}");
            eprintln!("[DEBUG_3147]   rhs display: {bv}");
            eprintln!("[DEBUG_3147]   lhs debug: {av:?}");
            eprintln!("[DEBUG_3147]   rhs debug: {bv:?}");
            eprintln!("[DEBUG_3147]   result: {eq}");
            eprintln!("[DEBUG_3147] ==========================================");
        }
    }
    Ok(Value::Bool(eq))
}

/// Evaluate inequality with optimization for `S /= {}`.
pub(super) fn eval_neq(
    ctx: &EvalCtx,
    a: &Spanned<tla_core::ast::Expr>,
    b: &Spanned<tla_core::ast::Expr>,
    span: Option<Span>,
) -> EvalResult<Value> {
    if is_empty_set_expr(&b.node) {
        return eval_is_nonempty_set(ctx, a, span);
    }
    if is_empty_set_expr(&a.node) {
        return eval_is_nonempty_set(ctx, b, span);
    }
    let av = eval(ctx, a)?;
    let bv = eval(ctx, b)?;
    Ok(Value::Bool(!values_equal(ctx, &av, &bv, span)?))
}

/// Evaluate unary negation with SmallInt fast path.
pub(super) fn eval_neg(ctx: &EvalCtx, a: &Spanned<tla_core::ast::Expr>) -> EvalResult<Value> {
    let av = eval(ctx, a)?;
    if let Value::SmallInt(n) = av {
        if let Some(result) = n.checked_neg() {
            return Ok(Value::SmallInt(result));
        }
    }
    let an = av
        .to_bigint()
        .ok_or_else(|| EvalError::type_error("Int", &av, Some(a.span)))?;
    Ok(Value::big_int(-an))
}

/// Evaluate integer range `a..b`.
pub(super) fn eval_range(
    ctx: &EvalCtx,
    a: &Spanned<tla_core::ast::Expr>,
    b: &Spanned<tla_core::ast::Expr>,
) -> EvalResult<Value> {
    let av = eval(ctx, a)?;
    let bv = eval(ctx, b)?;
    let an = av
        .to_bigint()
        .ok_or_else(|| EvalError::type_error("Int", &av, Some(a.span)))?;
    let bn = bv
        .to_bigint()
        .ok_or_else(|| EvalError::type_error("Int", &bv, Some(b.span)))?;
    Ok(range_set(&an, &bn))
}

/// Check if an expression is the empty set literal {}.
/// Part of #343 optimization for S /= {} patterns.
pub(super) fn is_empty_set_expr(expr: &tla_core::ast::Expr) -> bool {
    matches!(expr, tla_core::ast::Expr::SetEnum(elems) if elems.is_empty())
}

/// Evaluate whether a set expression is non-empty without building the full set.
/// This is an optimization for `S /= {}` patterns common in CONSTRAINTs.
///
/// For set comprehensions like `{x \in D : P(x)}`, this becomes `\E x \in D : P(x)`,
/// allowing early termination after finding the first satisfying element.
///
/// Part of #343: MCCheckpointCoordination performance fix.
pub(super) fn eval_is_nonempty_set(
    ctx: &EvalCtx,
    expr: &Spanned<tla_core::ast::Expr>,
    span: Option<Span>,
) -> EvalResult<Value> {
    match &expr.node {
        // Set comprehension: {x \in D : P(x)} /= {} <==> \E x \in D : P(x)
        tla_core::ast::Expr::SetFilter(bound, pred) => {
            let domain = bound.domain.as_ref().ok_or_else(|| EvalError::Internal {
                message: "Set filter requires bounded variable".into(),
                span,
            })?;

            let dv = eval(ctx, domain)?;
            // #1828: Use eval_iter_set for SetPred-aware iteration.
            // Fall back to full evaluation only for truly non-enumerable domains.
            let iter = match eval_iter_set(ctx, &dv, span) {
                Ok(it) => it,
                Err(EvalError::TypeError { .. }) => {
                    // Non-enumerable domain - fall back to full evaluation
                    let result = eval(ctx, expr)?;
                    return match result.is_empty_set() {
                        Some(empty) => Ok(Value::Bool(!empty)),
                        None => Err(EvalError::type_error("Set", &result, Some(expr.span))),
                    };
                }
                Err(e) => return Err(e),
            };

            // Check if any element satisfies the predicate (existential)
            let mut local_ctx = ctx.clone();
            let mark = local_ctx.mark_stack();
            for elem in iter {
                push_bound_var_mut(&mut local_ctx, bound, &elem, span)?;
                // TLC propagates eval errors (SetPredValue.member → Assert.fail).
                // Do NOT silently convert NotInDomain/IndexOutOfBounds to false.
                let pv = eval(&local_ctx, pred)?;
                let result = pv
                    .as_bool()
                    .ok_or_else(|| EvalError::type_error("BOOLEAN", &pv, Some(pred.span)))?;
                local_ctx.pop_to_mark(&mark);
                if result {
                    return Ok(Value::Bool(true)); // Found one element - set is non-empty
                }
            }
            Ok(Value::Bool(false)) // No elements found - set is empty
        }

        // Enumerated set: check if any elements
        tla_core::ast::Expr::SetEnum(elems) => Ok(Value::Bool(!elems.is_empty())),

        // For other expressions, evaluate and check
        _ => {
            let result = eval(ctx, expr)?;
            match result.is_empty_set() {
                Some(empty) => Ok(Value::Bool(!empty)),
                None => Err(EvalError::type_error("Set", &result, Some(expr.span))),
            }
        }
    }
}
