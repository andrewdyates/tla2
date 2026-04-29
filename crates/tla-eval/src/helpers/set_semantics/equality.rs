// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Set equality semantics (`values_equal`).
//!
//! Extracted from `helpers/set_semantics.rs` as part of #3463.

use crate::eval_membership::restore_setpred_ctx;
use crate::helpers::quantifiers::into_bind_local_bound_var;
use crate::value::Value;
use crate::{eval, EvalCtx, EvalError, EvalResult, StateEnvRef};
use tla_core::Span;

/// Compare two values for equality (extensional for sets).
/// `SetPred` values store lazy set comprehensions requiring eval context to enumerate.
/// Part of #2955: inline hot-path equality (CASE guard evaluation).
#[inline(always)]
pub fn values_equal(ctx: &EvalCtx, a: &Value, b: &Value, span: Option<Span>) -> EvalResult<bool> {
    use crate::value::SetPredValue;

    // Scalar fast path: SmallInt and Bool comparisons skip the is_set() check
    // entirely. These are the most frequent equality comparisons during BFS
    // (guard evaluation, state variable comparison, arithmetic results).
    match (a, b) {
        (Value::SmallInt(x), Value::SmallInt(y)) => return Ok(x == y),
        (Value::Bool(x), Value::Bool(y)) => return Ok(x == y),
        _ => {}
    }

    // Arc pointer equality: for UNCHANGED evaluation in BFS, when a variable
    // was not modified by an action, the primed and unprimed values share the
    // same Arc allocation. This O(1) check avoids deep comparison of
    // arbitrarily large functions, records, sequences, and sets — including
    // the expensive set extensional equality path below. Part of #3805.
    if a.ptr_eq(b) {
        return Ok(true);
    }

    // Non-sets: structural equality via Value::cmp (fast path).
    if !a.is_set() && !b.is_set() {
        return Ok(a == b);
    }
    // Set vs non-set: never equal.
    if a.is_set() != b.is_set() {
        return Ok(false);
    }

    // Fast path: pointer equality for explicit sets.
    if let (Value::Set(sa), Value::Set(sb)) = (a, b) {
        if sa.ptr_eq(sb) {
            return Ok(true);
        }
    }

    // Both are sets. First, handle definitional equalities that do not require enumeration.
    //
    // IMPORTANT: avoid `a == b` for sets. Explicit sets can contain set-like values, and
    // element equality must use `values_equal` so we correctly propagate TLC-style "attempted
    // enumeration" errors for element set comparisons.
    fn definitional_set_equal(
        ctx: &EvalCtx,
        a: &Value,
        b: &Value,
        span: Option<Span>,
    ) -> EvalResult<Option<bool>> {
        Ok(Some(match (a, b) {
            (Value::Interval(ia), Value::Interval(ib)) => ia == ib,
            (Value::StringSet, Value::StringSet) => true,
            (Value::AnySet, Value::AnySet) => true,
            // Infinite set markers (Nat/Int/Real) are compared by name.
            (Value::ModelValue(a), Value::ModelValue(b))
                if matches!(a.as_ref(), "Nat" | "Int" | "Real")
                    && matches!(b.as_ref(), "Nat" | "Int" | "Real") =>
            {
                a == b
            }
            (Value::Subset(sa), Value::Subset(sb)) => {
                values_equal(ctx, sa.base(), sb.base(), span)?
            }
            (Value::FuncSet(sa), Value::FuncSet(sb)) => {
                values_equal(ctx, sa.domain(), sb.domain(), span)?
                    && values_equal(ctx, sa.codomain(), sb.codomain(), span)?
            }
            (Value::RecordSet(sa), Value::RecordSet(sb)) => {
                if sa.fields_len() != sb.fields_len() {
                    false
                } else {
                    sa.fields_iter().zip(sb.fields_iter()).try_fold(
                        true,
                        |acc, ((ka, va), (kb, vb))| {
                            if !acc || ka != kb {
                                return Ok(false);
                            }
                            values_equal(ctx, va, vb, span)
                        },
                    )?
                }
            }
            (Value::TupleSet(sa), Value::TupleSet(sb)) => {
                if sa.components_len() != sb.components_len() {
                    false
                } else {
                    sa.components_iter().zip(sb.components_iter()).try_fold(
                        true,
                        |acc, (va, vb)| {
                            if !acc {
                                return Ok(false);
                            }
                            values_equal(ctx, va, vb, span)
                        },
                    )?
                }
            }
            (Value::KSubset(sa), Value::KSubset(sb)) => {
                sa.k() == sb.k() && values_equal(ctx, sa.base(), sb.base(), span)?
            }
            (Value::SeqSet(sa), Value::SeqSet(sb)) => {
                values_equal(ctx, sa.base(), sb.base(), span)?
            }
            (Value::SetPred(sa), Value::SetPred(sb)) => {
                if sa.id() == sb.id() {
                    true
                } else {
                    return Ok(None);
                }
            }
            // Same-shape lazy set ops are definitely equal if their operands are equal.
            // But unequal operands does NOT imply unequal sets (e.g., {1,2}∪{3} = {1}∪{2,3}).
            // Return None to fall through to element-by-element comparison.
            (Value::SetCup(sa), Value::SetCup(sb)) => {
                if values_equal(ctx, sa.set1(), sb.set1(), span)?
                    && values_equal(ctx, sa.set2(), sb.set2(), span)?
                {
                    true
                } else {
                    return Ok(None);
                }
            }
            (Value::SetCap(sa), Value::SetCap(sb)) => {
                if values_equal(ctx, sa.set1(), sb.set1(), span)?
                    && values_equal(ctx, sa.set2(), sb.set2(), span)?
                {
                    true
                } else {
                    return Ok(None);
                }
            }
            (Value::SetDiff(sa), Value::SetDiff(sb)) => {
                if values_equal(ctx, sa.set1(), sb.set1(), span)?
                    && values_equal(ctx, sa.set2(), sb.set2(), span)?
                {
                    true
                } else {
                    return Ok(None);
                }
            }
            (Value::BigUnion(sa), Value::BigUnion(sb)) => {
                if values_equal(ctx, sa.set(), sb.set(), span)? {
                    true
                } else {
                    return Ok(None);
                }
            }
            _ => return Ok(None),
        }))
    }

    if let Some(eq) = definitional_set_equal(ctx, a, b, span)? {
        return Ok(eq);
    }

    // Part of #3747: Stream source elements through predicate instead of
    // collecting the entire source set first (same fix as materialize_setpred_to_vec).
    fn materialize_setpred(
        ctx: &EvalCtx,
        spv: &SetPredValue,
        span: Option<Span>,
    ) -> EvalResult<Vec<Value>> {
        // Part of #2990: O(1) chain restore when available, O(n) fallback otherwise.
        let base_ctx = restore_setpred_ctx(ctx, spv)?;

        // Issue #418: Restore captured state (same fix as materialize_setpred_to_vec)
        let base_ctx = if spv.captured_state().is_some() || spv.captured_next_state().is_some() {
            let state_env = spv
                .captured_state()
                .map(StateEnvRef::from_slice)
                .or(base_ctx.state_env);
            let next_state_env = spv
                .captured_next_state()
                .map(StateEnvRef::from_slice)
                .or(base_ctx.next_state_env);
            // Part of #3416: establish cache boundary for direct eval() path
            base_ctx.with_state_envs_for_eval(state_env, next_state_env)
        } else {
            base_ctx
        };

        match spv.source() {
            Value::SetPred(inner_spv) => {
                let inner_elements = materialize_setpred(ctx, inner_spv, span)?;
                filter_pred_elements(&base_ctx, spv, inner_elements.into_iter(), span)
            }
            other => {
                let source_iter = other.iter_set().ok_or(EvalError::SetTooLarge { span })?;
                filter_pred_elements(&base_ctx, spv, source_iter, span)
            }
        }
    }

    fn filter_pred_elements(
        base_ctx: &EvalCtx,
        spv: &SetPredValue,
        source_iter: impl Iterator<Item = Value>,
        span: Option<Span>,
    ) -> EvalResult<Vec<Value>> {
        let mut result = Vec::new();
        for elem in source_iter {
            // Use into_bind_local_bound_var to respect BoundPattern::Tuple.
            let full_ctx = into_bind_local_bound_var(base_ctx.clone(), spv.bound(), &elem, span)?;
            match eval(&full_ctx, spv.pred()) {
                Ok(Value::Bool(true)) => {
                    result.push(elem);
                }
                Ok(Value::Bool(false)) => {}
                Ok(other) => {
                    // TLC: "Attempted to evaluate an expression of form
                    // {x \in S : P(x)} when P was <kind>."
                    return Err(EvalError::TypeError {
                        expected: "BOOLEAN",
                        got: other.type_name(),
                        span,
                    });
                }
                // TLC propagates eval errors (SetPredValue.member → Assert.fail).
                // Do NOT silently convert NotInDomain/IndexOutOfBounds to false.
                Err(e) => return Err(e),
            }
        }
        Ok(result)
    }

    fn collect_set_for_equal(
        ctx: &EvalCtx,
        v: &Value,
        span: Option<Span>,
    ) -> EvalResult<Vec<Value>> {
        match v {
            Value::SetPred(spv) => materialize_setpred(ctx, spv, span),
            // Composite set types may contain SetPred children that prevent
            // iter_set() from working. Decompose recursively to materialize them.
            Value::SetCup(cup) if v.iter_set().is_none() => {
                let mut s1 = collect_set_for_equal(ctx, cup.set1(), span)?;
                let s2 = collect_set_for_equal(ctx, cup.set2(), span)?;
                for elem in s2 {
                    if !s1.contains(&elem) {
                        s1.push(elem);
                    }
                }
                Ok(s1)
            }
            Value::SetCap(cap) if v.iter_set().is_none() => {
                let s1 = collect_set_for_equal(ctx, cap.set1(), span)?;
                let s2 = collect_set_for_equal(ctx, cap.set2(), span)?;
                Ok(s1.into_iter().filter(|e| s2.contains(e)).collect())
            }
            Value::SetDiff(diff) if v.iter_set().is_none() => {
                let s1 = collect_set_for_equal(ctx, diff.set1(), span)?;
                let s2 = collect_set_for_equal(ctx, diff.set2(), span)?;
                Ok(s1.into_iter().filter(|e| !s2.contains(e)).collect())
            }
            _ => v
                .iter_set()
                .map(std::iter::Iterator::collect)
                .ok_or(EvalError::SetTooLarge { span }),
        }
    }

    // Explicit-set fast path: avoid allocating/sorting the elements, but still use semantic
    // element equality (to propagate TLC parity errors).
    //
    // IMPORTANT: do not compare sets by zipping their iteration order. Explicit sets store
    // their elements in `Value::cmp` order, but set equality is unordered and must match
    // elements by semantic equality. Zipping can short-circuit to `false` without ever
    // evaluating required element set equalities (and thus can miss TLC-style enumeration
    // errors for set-of-sets comparisons).
    if let (Value::Set(sa), Value::Set(sb)) = (a, b) {
        if sa.len() != sb.len() {
            return Ok(false);
        }
        // Fast path: when both sets contain only non-set elements, `Value` structural
        // equality is sufficient and avoids O(n^2) matching.
        if sa.iter().all(|v| !v.is_set()) && sb.iter().all(|v| !v.is_set()) {
            return Ok(sa == sb);
        }

        // General case: unordered matching using semantic element equality.
        let mut remaining: Vec<Value> = sb.iter().cloned().collect();
        for av in sa.as_ref() {
            let mut matched = None;
            for (i, bv) in remaining.iter().enumerate() {
                if values_equal(ctx, av, bv, span)? {
                    matched = Some(i);
                    break;
                }
            }
            match matched {
                Some(i) => {
                    remaining.swap_remove(i);
                }
                None => return Ok(false),
            }
        }
        debug_assert!(remaining.is_empty());
        return Ok(true);
    }

    // Cardinality early-exit: if both sides have cheap O(1) cardinality
    // and they differ, the sets cannot be equal — skip full materialization.
    if let (Some(a_card), Some(b_card)) = (a.set_len(), b.set_len()) {
        if a_card != b_card {
            return Ok(false);
        }
    }

    let mut a_elements = collect_set_for_equal(ctx, a, span)?;
    let mut b_elements = collect_set_for_equal(ctx, b, span)?;
    if a_elements.len() != b_elements.len() {
        return Ok(false);
    }

    a_elements.sort();
    b_elements.sort();

    for (av, bv) in a_elements.iter().zip(b_elements.iter()) {
        if !values_equal(ctx, av, bv, span)? {
            return Ok(false);
        }
    }
    Ok(true)
}
