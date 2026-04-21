// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::{
    check_set_pred_membership, eval, eval_iter_set, EvalCtx, EvalError, EvalResult, Expr,
    SetBuilder, SetCapValue, SetDiffValue, SortedSet, Span, Spanned, UnionValue, Value,
};
use super::membership::set_contains_with_ctx;
use crate::value::big_union;
use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};

pub(crate) fn value_subseteq(
    ctx: &EvalCtx,
    av: &Value,
    bv: &Value,
    lhs_span: Option<Span>,
    rhs_span: Option<Span>,
) -> EvalResult<bool> {
    // Fast path: when both are Value::Set(OrdSet), check subset relationship
    if let (Value::Set(sa), Value::Set(sb)) = (av, bv) {
        // Quick rejection: if A is larger than B, A cannot be a subset of B
        if sa.len() > sb.len() {
            return Ok(false);
        }
        // Empty set is subset of any set
        if sa.is_empty() {
            return Ok(true);
        }
        // For small sets, use contains() loop which avoids iterator overhead
        // The im crate's is_subset() creates iterators that traverse B-tree nodes
        // For sets with <= 16 elements, linear contains() checks are faster
        if sa.len() <= 16 {
            for elem in sa.as_ref() {
                if !sb.contains(elem) {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        // For larger sets, use the bulk is_subset operation
        return Ok(sa.is_subset(sb));
    }

    // Fast path: when av is an Interval and bv is Set(OrdSet)
    // Check interval bounds against set membership
    if let (Value::Interval(iv), Value::Set(sb)) = (av, bv) {
        // For small intervals, check each element
        if let Some(len) = iv.len().to_usize() {
            if len <= 32 {
                for v in iv.iter_values() {
                    if !sb.contains(&v) {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
        }
        // Fall through to general case for large intervals
    }

    // Part of #3978: Streaming SetPred LHS for subseteq. When the left side is a
    // SetPred, use streaming iteration to evaluate the predicate on-demand and
    // short-circuit on the first element not in the RHS. This avoids materializing
    // the full filtered set into a Vec when the first non-member is found early.
    if matches!(av, Value::SetPred(_)) {
        if let Some(stream_iter) =
            crate::helpers::try_stream_setpred(ctx, av, lhs_span)?
        {
            for elem_result in stream_iter {
                let elem = elem_result?;
                let in_b = match bv {
                    Value::ModelValue(name) => match name.as_ref() {
                        "Nat" => match &elem {
                            Value::SmallInt(n) => *n >= 0,
                            Value::Int(n) => **n >= BigInt::zero(),
                            _ => false,
                        },
                        "Int" => matches!(&elem, Value::SmallInt(_) | Value::Int(_)),
                        "Real" => matches!(&elem, Value::SmallInt(_) | Value::Int(_)),
                        _ => {
                            return Err(EvalError::type_error("Set", bv, rhs_span));
                        }
                    },
                    Value::SetPred(spv) => {
                        check_set_pred_membership(ctx, &elem, spv, lhs_span)?
                    }
                    _ => match bv.set_contains(&elem) {
                        Some(c) => c,
                        None => set_contains_with_ctx(ctx, &elem, bv, lhs_span)?,
                    },
                };
                if !in_b {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        // Fall through: special optimizations active, use materializing path.
    }

    // TLC requires the left side to be enumerable; the right side only needs membership.
    // #1828: Use eval_iter_set to handle SetPred domains transparently.
    for elem in eval_iter_set(ctx, av, lhs_span)? {
        let in_b = match bv {
            Value::ModelValue(name) => match name.as_ref() {
                "Nat" => match &elem {
                    Value::SmallInt(n) => *n >= 0,
                    Value::Int(n) => **n >= BigInt::zero(),
                    _ => false,
                },
                "Int" => matches!(&elem, Value::SmallInt(_) | Value::Int(_)),
                "Real" => matches!(&elem, Value::SmallInt(_) | Value::Int(_)),
                _ => {
                    return Err(EvalError::type_error("Set", bv, rhs_span));
                }
            },
            Value::SetPred(spv) => check_set_pred_membership(ctx, &elem, spv, lhs_span)?,
            _ => match bv.set_contains(&elem) {
                Some(c) => c,
                None => set_contains_with_ctx(ctx, &elem, bv, lhs_span)?,
            },
        };
        if !in_b {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Evaluate subset-or-equal (`A \subseteq B`).
///
/// Fast paths for OrdSet-OrdSet and Interval-OrdSet comparisons.
/// General case enumerates the LHS and checks membership in RHS
/// (which may be infinite/SetPred/concrete).
pub(crate) fn eval_subseteq(
    ctx: &EvalCtx,
    a: &Spanned<Expr>,
    b: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Value> {
    let av = eval(ctx, a)?;
    let bv = eval(ctx, b)?;
    Ok(Value::Bool(value_subseteq(
        ctx,
        &av,
        &bv,
        span,
        Some(b.span),
    )?))
}

/// Evaluate set intersection (`A \cap B`).
///
/// Special handling for SetPred operands (requires evaluation context).
/// Falls back to eager OrdSet intersection or lazy SetCap.
pub(crate) fn eval_intersect(
    ctx: &EvalCtx,
    a: &Spanned<Expr>,
    b: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Value> {
    let av = eval(ctx, a)?;
    let bv = eval(ctx, b)?;
    intersect_values(ctx, av, bv, Some(a.span), Some(b.span), span)
}

pub(crate) fn intersect_values(
    ctx: &EvalCtx,
    av: Value,
    bv: Value,
    left_span: Option<Span>,
    right_span: Option<Span>,
    span: Option<Span>,
) -> EvalResult<Value> {
    // Check that both operands are sets
    if !av.is_set() {
        return Err(EvalError::type_error("Set", &av, left_span));
    }
    if !bv.is_set() {
        return Err(EvalError::type_error("Set", &bv, right_span));
    }

    // Special handling for SetPred - compute intersection eagerly if possible
    // SetPred requires evaluation context for membership checks, so we handle it here
    match (&av, &bv) {
        // Case: any set ∩ SetPred - iterate left (via eval_iter_set for SetPred support),
        // filter by SetPred membership. #1896: eval_iter_set handles SetPred-on-both-sides.
        (_, Value::SetPred(spv)) => {
            let mut result = SetBuilder::new();
            for elem in eval_iter_set(ctx, &av, span)? {
                if check_set_pred_membership(ctx, &elem, spv, span)? {
                    result.insert(elem);
                }
            }
            return Ok(result.build_value());
        }
        // Case: SetPred ∩ any set - iterate right (via eval_iter_set for SetPred support),
        // filter by SetPred membership. #1896: eval_iter_set handles SetPred-on-both-sides.
        (Value::SetPred(spv), _) => {
            let mut result = SetBuilder::new();
            for elem in eval_iter_set(ctx, &bv, span)? {
                if check_set_pred_membership(ctx, &elem, spv, span)? {
                    result.insert(elem);
                }
            }
            return Ok(result.build_value());
        }
        _ => {}
    }

    // Try eager evaluation if both operands are enumerable
    match (av.to_sorted_set(), bv.to_sorted_set()) {
        (Some(sa), Some(sb)) => Ok(Value::from_sorted_set(sa.intersection(&sb))),
        // Otherwise, return lazy SetCap (can still enumerate if at least one is enumerable)
        _ => Ok(Value::SetCap(SetCapValue::new(av, bv))),
    }
}

/// Evaluate set difference (`A \ B`).
///
/// Special handling for SetPred on RHS (requires evaluation context).
/// Falls back to eager filtering or lazy SetDiff.
pub(crate) fn eval_set_minus(
    ctx: &EvalCtx,
    a: &Spanned<Expr>,
    b: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Value> {
    // Part of #2955: Singleton set fast path — bypass set construction for S \ {x}.
    //
    // GameOfLife's RECURSIVE Sum does `S \ {x}` ~67M times. The normal path constructs
    // {x} as a SortedSet (via intern_set_array → DashMap lookup, ~100-200ns per call)
    // then immediately destructures it in the singleton check at line 595.
    //
    // This fast path detects `SetMinus(S, SetEnum([single_expr]))` at the AST level,
    // evaluates S and x directly, and calls `sa.without(&x)` — avoiding all singleton
    // set construction, interning, and DashMap lock overhead.
    if let Expr::SetEnum(elems) = &b.node {
        if elems.len() == 1 {
            let av = eval(ctx, a)?;
            if let Value::Set(sa) = &av {
                let xv = eval(ctx, &elems[0])?;
                return Ok(Value::from_sorted_set(sa.without(&xv)));
            }
            // LHS is not a SortedSet (Interval, SubsetValue, etc.) —
            // fall through to the normal evaluation path below.
        }
    }

    let av = eval(ctx, a)?;
    let bv = eval(ctx, b)?;
    set_minus_values(ctx, av, bv, Some(a.span), Some(b.span), span)
}

pub(crate) fn set_minus_values(
    ctx: &EvalCtx,
    av: Value,
    bv: Value,
    left_span: Option<Span>,
    right_span: Option<Span>,
    span: Option<Span>,
) -> EvalResult<Value> {
    // Check that both operands are sets
    if !av.is_set() {
        return Err(EvalError::type_error("Set", &av, left_span));
    }
    if !bv.is_set() {
        return Err(EvalError::type_error("Set", &bv, right_span));
    }

    // Special handling for SetPred on RHS - check membership via predicate evaluation.
    // #1896: Use eval_iter_set so LHS SetPred values are materialized correctly.
    if let Value::SetPred(spv) = &bv {
        let mut result = SetBuilder::new();
        for elem in eval_iter_set(ctx, &av, span)? {
            // Keep elements NOT in the SetPred
            if !check_set_pred_membership(ctx, &elem, spv, span)? {
                result.insert(elem);
            }
        }
        return Ok(result.build_value());
    }

    // Fast path: both sides are SortedSets — use direct set operations.
    // Avoids per-element set_contains dispatch and intern_set_array overhead.
    // Part of #2955: GameOfLife calls S \ {x} ~8.4M times (128 per state × 65,536 states).
    // TLC uses the same O(n) approach (SetEnumValue.diff) but without dispatch overhead.
    if let (Value::Set(sa), Value::Set(sb)) = (&av, &bv) {
        if sb.len() == 1 {
            // Singleton subtraction: binary search + copy two halves. O(log n + n).
            // Avoids n membership checks and interning overhead.
            return Ok(Value::from_sorted_set(sa.without(&sb.as_slice()[0])));
        }
        // General SortedSet difference: O(n + m) sorted merge.
        return Ok(Value::from_sorted_set(sa.difference(sb)));
    }

    // Generic path for non-SortedSet operands (Interval, SubsetValue, lazy sets, etc.)
    match av.to_sorted_set() {
        Some(sa) => {
            // Can compute eagerly - filter by non-membership in RHS.
            // If set_contains returns None for any element (SetPred inside SetCup/SetCap),
            // fall back to lazy SetDiff.
            let mut kept = Vec::new();
            let mut indeterminate = false;
            for v in &sa {
                match bv.set_contains(v) {
                    Some(true) => {} // exclude
                    Some(false) => {
                        kept.push(v.clone());
                    }
                    None => {
                        indeterminate = true;
                        break;
                    }
                }
            }
            if indeterminate {
                Ok(Value::SetDiff(SetDiffValue::new(av, bv)))
            } else {
                Ok(Value::from_sorted_set(SortedSet::from_sorted_vec(kept)))
            }
        }
        // LHS not enumerable, return lazy SetDiff
        None => Ok(Value::SetDiff(SetDiffValue::new(av, bv))),
    }
}

/// Evaluate generalized union (`UNION S`).
///
/// Syntactic fast paths for `UNION { X } == X` and `UNION {} == {}`.
/// For small enumerable inner sets, computes eagerly; otherwise returns lazy UnionValue.
pub(crate) fn eval_big_union(
    ctx: &EvalCtx,
    a: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Value> {
    // Issue #284 fix: Fast path for UNION { X } == X, UNION {} == {}
    // This is a SYNTACTIC optimization - check AST before evaluating.
    // Avoids expensive FuncSet enumeration for singleton UNION expressions
    // like UNION { [0..N -> SUBSET(S)] } in Disruptor_SPMC TypeOk.
    //
    // Mathematically: UNION { X } = X for any set X
    //                 UNION {} = {}
    if let Expr::SetEnum(elems) = &a.node {
        match elems.as_slice() {
            [] => return Ok(Value::empty_set()),
            [only] => {
                let v = eval(ctx, only)?;
                if !v.is_set() {
                    return Err(EvalError::type_error("Set", &v, Some(a.span)));
                }
                return Ok(v);
            }
            _ => {} // Fall through to normal evaluation
        }
    }

    let av = eval(ctx, a)?;
    // Accept any set-like value
    if !av.is_set() {
        return Err(EvalError::type_error("Set", &av, Some(a.span)));
    }
    // For small, fully enumerable sets, compute eagerly for efficiency
    // For large or non-enumerable sets, return lazy UnionValue
    if let Some(sa) = av.to_sorted_set() {
        // Check if all inner sets are enumerable and total size is reasonable.
        // Use set_len() instead of to_ord_set() to avoid wasteful materialization
        // of inner sets just for size checking. For FuncSets, set_len() computes
        // |codomain|^|domain| arithmetically — O(1) vs O(n) for to_ord_set().
        // This matters for specs like MCBinarySearch where inner FuncSets contain
        // up to 390K elements that were being fully materialized and discarded.
        let mut can_eager = true;
        let mut total_size = 0usize;
        for elem in &sa {
            if let Some(len) = elem.set_len() {
                // set_len returns BigInt; cap at usize for threshold comparison
                let len_usize = len.try_into().unwrap_or(usize::MAX);
                total_size = total_size.saturating_add(len_usize);
                if total_size > 10000 {
                    can_eager = false;
                    break;
                }
            } else {
                can_eager = false;
                break;
            }
        }
        if can_eager {
            // Eager evaluation for small sets
            return big_union(&sa).ok_or(EvalError::TypeError {
                expected: "Set of Sets",
                got: "Set containing non-Set",
                span,
            });
        }
    }
    // Lazy evaluation - return UnionValue
    Ok(Value::BigUnion(UnionValue::new(av)))
}
