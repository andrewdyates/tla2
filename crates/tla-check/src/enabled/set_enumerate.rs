// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Set enumeration for the ENABLED constraint propagation context.
//!
//! Provides `enumerate_set_in_ctx` which enumerates set elements using the
//! current `EvalCtx` rather than restoring captured state. This is critical
//! for `SetPred` values in the ENABLED scope where LET bindings and local_ops
//! are attached to the current ctx via `bind_mut` / `local_ops_mut`.
//!
//! Fix for #3030: MCYoYoPruning's nested SetPred references parameterized LET
//! defs (`senders(v)`) that exist only in the ENABLED context's local_ops.

use crate::eval::{eval, eval_iter_set, EvalCtx};
use std::sync::Arc;
use tla_value::error::{EvalError, EvalResult};
use tla_value::SetPredValue;
use tla_value::Value;

/// Enumerate set elements using the current evaluation context.
///
/// For most set types, delegates to `iter_set()`. For `SetPred` (lazy
/// predicate-filtered sets), enumerates the source set and evaluates the
/// predicate in the CURRENT ctx rather than restoring the SetPred's captured
/// context. This is critical in the ENABLED scope where LET bindings and
/// local_ops are attached to the current ctx via `bind_mut` / `local_ops_mut`,
/// and the SetPred's `restore_setpred_ctx` would lose these bindings.
///
/// Fix for #3030: MCYoYoPruning's `\E keep \in {f \in [valsRcvd -> incoming[n]] :
/// \A v \in valsRcvd : f[v] \in senders(v)} : ...` produces a SetPred whose
/// predicate references `senders(v)` (a parameterized LET def in local_ops)
/// and `valsRcvd` (a zero-arg LET def in env).
pub(super) fn enumerate_set_in_ctx(
    ctx: &EvalCtx,
    value: &Value,
    span: Option<tla_core::Span>,
) -> EvalResult<Vec<Value>> {
    // Fast path: directly iterable sets (Set, Interval, FuncSet, etc.)
    if let Some(iter) = value.iter_set() {
        return Ok(iter.collect());
    }

    // SetPred: enumerate source set, evaluate predicate in current ctx.
    if let Value::SetPred(spv) = value {
        return enumerate_setpred_in_ctx(ctx, spv, span);
    }

    // Other non-iterable sets: delegate to eval_iter_set which handles
    // composite types (SetCup/SetCap/SetDiff with SetPred children).
    Ok(eval_iter_set(ctx, value, span)?.collect())
}

/// Enumerate a SetPred in the current context without restoring captured state.
///
/// Iterates the source set, binds the bound variable, evaluates the predicate,
/// and collects matching elements — all using the passed-in `ctx`.
fn enumerate_setpred_in_ctx(
    ctx: &EvalCtx,
    spv: &SetPredValue,
    span: Option<tla_core::Span>,
) -> EvalResult<Vec<Value>> {
    let source = spv.source();
    // Recursively enumerate source (may itself be a SetPred).
    let source_elements = enumerate_set_in_ctx(ctx, source, span)?;

    let bound = spv.bound();
    let pred = spv.pred();
    let bound_name: Arc<str> = Arc::from(bound.name.node.as_str());

    let mut result = Vec::new();
    for elem in source_elements {
        let mut local_ctx = ctx.clone();
        let _guard = local_ctx.scope_guard();
        local_ctx.bind_mut(Arc::clone(&bound_name), elem.clone());
        let pred_val = eval(&local_ctx, pred)?;
        match pred_val.as_bool() {
            Some(true) => result.push(elem),
            Some(false) => {}
            None => {
                return Err(EvalError::type_error("BOOLEAN", &pred_val, span));
            }
        }
    }
    Ok(result)
}
