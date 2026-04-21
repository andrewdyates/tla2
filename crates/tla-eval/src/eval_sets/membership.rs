// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::{
    check_set_pred_membership, eval, eval_iter_set, eval_membership_lazy, needs_lazy_membership,
    EvalCtx, EvalError, EvalResult, Expr, Span, Spanned, Value,
};
use num_bigint::BigInt;
use num_traits::Zero;

/// Evaluate set membership (`a \in B`).
///
/// Handles multiple RHS forms:
/// - Lazy membership for FuncSet, Powerset, Seq, RecordSet (avoids enumeration)
/// - Infinite sets (Nat, Int, Real) via ModelValue
/// - SetPred via predicate evaluation
/// - Concrete sets via `set_contains`
pub(crate) fn eval_in(
    ctx: &EvalCtx,
    a: &Spanned<Expr>,
    b: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Value> {
    let av = eval(ctx, a)?;

    // Use lazy membership check for FuncSet, Powerset, Seq, and RecordSet
    // This avoids enumerating large/infinite sets.
    //
    // Part of #3792: When the RHS is a zero-arg operator (like `Messages`), evaluate it
    // to a Value and use Value-level set_contains() instead of AST-walking
    // eval_membership_lazy(). Combined with RecordSetValue's cardinality-ordered
    // field checking, this gives ~3-4x speedup on message-union invariants by:
    // (1) evaluating the operator once (cached) instead of re-resolving the AST, and
    // (2) checking singleton "type" fields first for early rejection.
    //
    // Fix #3802: Exclude SetFilter bodies from this fast path. SetFilter with
    // non-reducible domains (e.g., SUBSET SUBSET S) produces SetPred values that
    // the zero-arg cache materializes via materialize_setpred_to_vec, causing
    // exponential enumeration. Fall through to eval_membership_lazy which checks
    // membership lazily (source-set check + predicate evaluation).
    if needs_lazy_membership(ctx, b) {
        if let Expr::Ident(name, _) = &b.node {
            let resolved_name = ctx.resolve_op_name(name);
            if let Some(def) = ctx.get_op(resolved_name) {
                if def.params.is_empty() && !matches!(def.body.node, Expr::SetFilter(_, _)) {
                    let bv = eval(ctx, b)?;
                    let contains = match bv.set_contains(&av) {
                        Some(c) => c,
                        None => set_contains_with_ctx(ctx, &av, &bv, span)?,
                    };
                    return Ok(Value::Bool(contains));
                }
            }
        }
        let result = eval_membership_lazy(ctx, &av, b)?;
        return Ok(Value::Bool(result));
    }

    let bv = eval(ctx, b)?;

    // Handle membership in infinite sets (Nat, Int, Real)
    if let Value::ModelValue(name) = &bv {
        return match name.as_ref() {
            "Nat" => match &av {
                Value::SmallInt(n) => Ok(Value::Bool(*n >= 0)),
                Value::Int(n) => Ok(Value::Bool(**n >= BigInt::zero())),
                _ => Ok(Value::Bool(false)),
            },
            "Int" => Ok(Value::Bool(matches!(
                &av,
                Value::SmallInt(_) | Value::Int(_)
            ))),
            "Real" => Ok(Value::Bool(matches!(
                &av,
                Value::SmallInt(_) | Value::Int(_)
            ))), // Int ⊆ Real
            _ => Err(EvalError::type_error("Set", &bv, Some(b.span))),
        };
    }

    // Handle SetPred: check source membership, then evaluate predicate
    if let Value::SetPred(spv) = &bv {
        return Ok(Value::Bool(check_set_pred_membership(ctx, &av, spv, span)?));
    }

    // Handle both Set and Interval using set_contains.
    // If set_contains returns None (e.g. SetPred inside SetCup/SetDiff/SetCap),
    // fall back to context-aware recursive decomposition.
    let contains = match bv.set_contains(&av) {
        Some(c) => c,
        None => set_contains_with_ctx(ctx, &av, &bv, span)?,
    };
    Ok(Value::Bool(contains))
}

/// Evaluate set non-membership (`a \notin B`).
///
/// Mirrors `eval_in` with negated results.
pub(crate) fn eval_not_in(
    ctx: &EvalCtx,
    a: &Spanned<Expr>,
    b: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Value> {
    let av = eval(ctx, a)?;

    // Use lazy membership check for FuncSet, Powerset, Seq, and RecordSet
    // This avoids enumerating large/infinite sets.
    // Part of #3792: Same zero-arg operator fast path as eval_in — see comment there.
    if needs_lazy_membership(ctx, b) {
        if let Expr::Ident(name, _) = &b.node {
            let resolved_name = ctx.resolve_op_name(name);
            if let Some(def) = ctx.get_op(resolved_name) {
                if def.params.is_empty() && !matches!(def.body.node, Expr::SetFilter(_, _)) {
                    let bv = eval(ctx, b)?;
                    let contains = match bv.set_contains(&av) {
                        Some(c) => c,
                        None => set_contains_with_ctx(ctx, &av, &bv, span)?,
                    };
                    return Ok(Value::Bool(!contains));
                }
            }
        }
        return Ok(Value::Bool(!eval_membership_lazy(ctx, &av, b)?));
    }

    let bv = eval(ctx, b)?;

    // Handle membership in infinite sets (Nat, Int, Real)
    if let Value::ModelValue(name) = &bv {
        return match name.as_ref() {
            "Nat" => match &av {
                Value::SmallInt(n) => Ok(Value::Bool(*n < 0)),
                Value::Int(n) => Ok(Value::Bool(**n < BigInt::zero())),
                _ => Ok(Value::Bool(true)),
            },
            "Int" => Ok(Value::Bool(!matches!(
                &av,
                Value::SmallInt(_) | Value::Int(_)
            ))),
            "Real" => Ok(Value::Bool(!matches!(
                &av,
                Value::SmallInt(_) | Value::Int(_)
            ))), // Int ⊆ Real
            _ => Err(EvalError::type_error("Set", &bv, Some(b.span))),
        };
    }

    // Handle SetPred: check source membership, then evaluate predicate
    if let Value::SetPred(spv) = &bv {
        return Ok(Value::Bool(!check_set_pred_membership(
            ctx, &av, spv, span,
        )?));
    }

    // Handle both Set and Interval using set_contains.
    // If set_contains returns None (e.g. SetPred inside SetCup/SetDiff/SetCap),
    // fall back to context-aware recursive decomposition.
    let contains = match bv.set_contains(&av) {
        Some(c) => c,
        None => set_contains_with_ctx(ctx, &av, &bv, span)?,
    };
    Ok(Value::Bool(!contains))
}

/// Context-aware membership check for values where `set_contains` returns None.
///
/// When a lazy set operation (SetCup, SetCap, SetDiff) contains a SetPred operand,
/// `Value::set_contains` returns None because SetPred requires an evaluation context.
/// This function recursively decomposes the set operation and uses
/// `check_set_pred_membership` for the SetPred leaves.
pub fn set_contains_with_ctx(
    ctx: &EvalCtx,
    elem: &Value,
    set: &Value,
    span: Option<Span>,
) -> EvalResult<bool> {
    match set {
        Value::SetPred(spv) => check_set_pred_membership(ctx, elem, spv, span),
        Value::SetCup(cup) => {
            let in1 = set_contains_or_ctx(ctx, elem, cup.set1(), span)?;
            if in1 {
                return Ok(true);
            }
            set_contains_or_ctx(ctx, elem, cup.set2(), span)
        }
        Value::SetCap(cap) => {
            let in1 = set_contains_or_ctx(ctx, elem, cap.set1(), span)?;
            if !in1 {
                return Ok(false);
            }
            set_contains_or_ctx(ctx, elem, cap.set2(), span)
        }
        Value::SetDiff(diff) => {
            let in1 = set_contains_or_ctx(ctx, elem, diff.set1(), span)?;
            if !in1 {
                return Ok(false);
            }
            Ok(!set_contains_or_ctx(ctx, elem, diff.set2(), span)?)
        }
        // Compound set types whose contains() returned None due to SetPred in base/codomain
        Value::Subset(subset) => {
            // v \in SUBSET S iff v is a set and v \subseteq S
            // Use eval_iter_set for SetPred-aware iteration (Part of #1828/#1830).
            // Without this, SetPred elements would return false for SUBSET membership
            // because Value::iter_set() returns None for SetPred.
            match eval_iter_set(ctx, elem, span) {
                Ok(iter) => {
                    for e in iter {
                        if !set_contains_or_ctx(ctx, &e, subset.base(), span)? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                }
                Err(EvalError::TypeError {
                    expected: "Set", ..
                }) => {
                    // Element is not a set — cannot be in SUBSET S
                    Ok(false)
                }
                Err(e) => Err(e),
            }
        }
        Value::FuncSet(func_set) => {
            contains_funcset_with_ctx(ctx, elem, func_set.domain(), func_set.codomain(), span)
        }
        Value::KSubset(k_subset) => {
            if let Some(ss) = elem.to_sorted_set() {
                if ss.len() != k_subset.k() {
                    return Ok(false);
                }
                for e in &ss {
                    if !set_contains_or_ctx(ctx, e, k_subset.base(), span)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            } else {
                Ok(false)
            }
        }
        Value::RecordSet(rs) => {
            let Value::Record(rec) = elem else {
                return Ok(false);
            };
            if rec.len() != rs.fields_len() {
                return Ok(false);
            }
            // Part of #3792: Use check-order iteration (ascending cardinality)
            // to match RecordSetValue::contains() and maximize early rejection.
            for (field, field_set) in rs.fields_check_order_iter() {
                let Some(field_val) = rec.get(field.as_ref()) else {
                    return Ok(false);
                };
                if !set_contains_or_ctx(ctx, field_val, field_set, span)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Value::TupleSet(ts) => {
            let Value::Tuple(elems_vec) = elem else {
                return Ok(false);
            };
            if elems_vec.len() != ts.components_len() {
                return Ok(false);
            }
            for (e, comp_set) in elems_vec.iter().zip(ts.components_iter()) {
                if !set_contains_or_ctx(ctx, e, comp_set, span)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        // #1500: SeqSet membership — v ∈ Seq(S) iff v is a sequence and all elements ∈ S.
        // SeqSetValue::contains returns None when base membership is indeterminate.
        Value::SeqSet(seq_set) => contains_seqset_with_ctx(ctx, elem, seq_set.base(), span),
        // #1500: BigUnion membership — v ∈ UNION S iff ∃ s ∈ S : v ∈ s.
        // UnionValue::contains returns None when inner set membership is indeterminate.
        // #1828: Use eval_iter_set so SetPred-wrapped union domains materialize correctly.
        Value::BigUnion(uv) => {
            for inner_set in eval_iter_set(ctx, uv.set(), span)? {
                if set_contains_or_ctx(ctx, elem, &inner_set, span)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        _ => Err(EvalError::type_error("Set", set, span)),
    }
}

/// Context-aware SeqSet membership check.
/// Replicates SeqSetValue::contains logic but uses set_contains_or_ctx for base checks.
fn contains_seqset_with_ctx(
    ctx: &EvalCtx,
    elem: &Value,
    base: &Value,
    span: Option<Span>,
) -> EvalResult<bool> {
    match elem {
        Value::Seq(seq) => {
            for e in seq.iter() {
                if !set_contains_or_ctx(ctx, e, base, span)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Value::Tuple(elems) => {
            for e in elems.iter() {
                if !set_contains_or_ctx(ctx, e, base, span)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Value::IntFunc(f) => {
            if tla_value::IntIntervalFunc::min(f) != 1 {
                return Ok(false);
            }
            for val in f.values() {
                if !set_contains_or_ctx(ctx, val, base, span)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Value::Func(f) => {
            let n = f.domain_len();
            if n == 0 {
                return Ok(true);
            }
            for (i, k) in f.domain_iter().enumerate() {
                let expected = Value::SmallInt((i + 1) as i64);
                if k != &expected {
                    return Ok(false);
                }
            }
            for val in f.mapping_values() {
                if !set_contains_or_ctx(ctx, val, base, span)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        _ => Ok(false),
    }
}

/// Context-aware FuncSet membership check.
/// Replicates FuncSetValue::contains logic but uses set_contains_or_ctx for codomain checks.
fn contains_funcset_with_ctx(
    ctx: &EvalCtx,
    elem: &Value,
    domain: &Value,
    codomain: &Value,
    span: Option<Span>,
) -> EvalResult<bool> {
    match elem {
        Value::Func(f) => {
            let domain_set = match domain.to_sorted_set() {
                Some(s) => s,
                None => return Ok(false),
            };
            if !f.domain_eq_sorted_set(&domain_set) {
                return Ok(false);
            }
            for val in f.mapping_values() {
                if !set_contains_or_ctx(ctx, val, codomain, span)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Value::IntFunc(f) => {
            let domain_set = match domain.to_sorted_set() {
                Some(s) => s,
                None => return Ok(false),
            };
            if !domain_set.equals_integer_interval(
                tla_value::IntIntervalFunc::min(f),
                tla_value::IntIntervalFunc::max(f),
            ) {
                return Ok(false);
            }
            for val in f.values() {
                if !set_contains_or_ctx(ctx, val, codomain, span)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Value::Tuple(elems) => {
            let domain_set = match domain.to_sorted_set() {
                Some(s) => s,
                None => return Ok(false),
            };
            if !domain_set.equals_sequence_domain(elems.len()) {
                return Ok(false);
            }
            for e in elems.iter() {
                if !set_contains_or_ctx(ctx, e, codomain, span)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Value::Seq(seq) => {
            let domain_set = match domain.to_sorted_set() {
                Some(s) => s,
                None => return Ok(false),
            };
            if !domain_set.equals_sequence_domain(seq.len()) {
                return Ok(false);
            }
            for e in seq.iter() {
                if !set_contains_or_ctx(ctx, e, codomain, span)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        _ => Ok(false),
    }
}

/// Try `set_contains` first; fall back to `set_contains_with_ctx` on None.
fn set_contains_or_ctx(
    ctx: &EvalCtx,
    elem: &Value,
    set: &Value,
    span: Option<Span>,
) -> EvalResult<bool> {
    match set.set_contains(elem) {
        Some(c) => Ok(c),
        None => set_contains_with_ctx(ctx, elem, set, span),
    }
}
