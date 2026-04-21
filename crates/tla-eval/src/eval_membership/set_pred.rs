// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SetPred membership checking and context restoration.
//!
//! Extracted from `eval_membership.rs` as part of #3463.

use super::super::{
    eval, into_bind_local_bound_var_cached, EvalCtx, EvalError, EvalResult, SetPredValue, Span,
    StateEnvRef, Value,
};
use crate::helpers::restore_captured_binding_chain;
use std::sync::Arc;

/// Check membership in a SetPred value: v \in {x \in S : P(x)}
///
/// This is true iff: v \in S AND P(v) is TRUE
///
/// The predicate P is evaluated with the bound variable bound to v,
/// using the SetPred's captured environment merged with the current context.
/// Issue #418: Made pub(crate) for use in compiled_guard.rs
pub fn check_set_pred_membership(
    ctx: &EvalCtx,
    value: &Value,
    spv: &SetPredValue,
    span: Option<Span>,
) -> EvalResult<bool> {
    // First check: is value in the source set?
    // Part of #3979: Use set_contains_with_ctx as fallback when set_contains returns
    // None. This handles sources that are composite sets (SetCup, SetCap, SetDiff)
    // containing SetPred operands, or sources that are themselves SetPred values.
    // Previously, only direct SetPred sources were handled recursively; other
    // indeterminate sources would error.
    let in_source = if let Some(contains) = spv.source().set_contains(value) {
        contains
    } else {
        crate::set_contains_with_ctx(ctx, value, spv.source(), span)?
    };

    if !in_source {
        return Ok(false);
    }

    // Second check: does the predicate hold for this value?
    // Part of #2990: O(1) chain restore when available, O(n) fallback otherwise.
    let pred_ctx = restore_setpred_ctx(ctx, spv)?;

    // Issue #418: Use captured state_env/next_state_env if present (TLC parity).
    // TLC captures state at definition time; fall back to caller's state if not captured.
    let pred_ctx = if spv.captured_state().is_some() || spv.captured_next_state().is_some() {
        let state_env = spv
            .captured_state()
            .map(StateEnvRef::from_slice)
            .or(pred_ctx.state_env);
        let next_state_env = spv
            .captured_next_state()
            .map(StateEnvRef::from_slice)
            .or(pred_ctx.next_state_env);
        // Part of #3416: establish cache boundary for direct eval() path
        pred_ctx.with_state_envs_for_eval(state_env, next_state_env)
    } else {
        pred_ctx
    };

    // Bind the variable to the value being tested
    // Part of #1383: pred_ctx is owned and last-use here, avoid clone
    let bound_ctx = into_bind_local_bound_var_cached(
        pred_ctx,
        spv.bound(),
        value,
        spv.cached_simple_bound_name(),
        spv.cached_tuple_bound_names(),
        span,
    )?;

    // Evaluate the predicate
    let pred = spv.pred();
    let pred_result = eval(&bound_ctx, pred)?;
    let pred_bool = pred_result
        .as_bool()
        .ok_or_else(|| EvalError::type_error("BOOLEAN", &pred_result, Some(pred.span)))?;

    Ok(pred_bool)
}

/// Part of #2990: Restore an EvalCtx from a SetPredValue's captured environment.
///
/// When a captured BindingChain is available, restores the chain + env in O(1)
/// instead of rebuilding from the flat env HashMap in O(n). Falls back to
/// the O(n) rebuild only when no chain is captured (legacy SetPredValues).
///
/// This replaces the pattern:
///   `spv.env().iter().fold(ctx.clone(), |acc, (k, v)| acc.into_bind_local(k.clone(), v.clone()))`
pub fn restore_setpred_ctx(ctx: &EvalCtx, spv: &SetPredValue) -> EvalResult<EvalCtx> {
    if let Some(captured) = spv.captured_chain() {
        let (chain, binding_depth) = restore_captured_binding_chain(
            Some(captured),
            spv.captured_chain_depth(),
            "restore_setpred_ctx",
            Some(spv.pred().span),
        )?;
        // O(1) restore: set env + chain directly from captured state.
        let mut new_ctx = ctx.clone();
        new_ctx.stable_mut().env = Arc::clone(spv.env_arc());
        new_ctx.bindings = chain;
        new_ctx.binding_depth = binding_depth;
        return Ok(new_ctx);
    }
    // Fallback: O(n) rebuild from flat env HashMap.
    Ok(spv.env().iter().fold(ctx.clone(), |acc, (k, v)| {
        acc.into_bind_local(k.clone(), v.clone())
    }))
}
