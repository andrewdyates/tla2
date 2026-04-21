// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Set iteration with EvalCtx-aware SetPred handling.
//!
//! Extracted from `helpers/set_semantics.rs` as part of #3463.

use crate::eval_membership::restore_setpred_ctx;
use crate::helpers::quantifiers::into_bind_local_bound_var;
use crate::value::{KSubsetValue, SetPredValue, SubsetValue, Value};
use crate::{eval, EvalCtx, EvalError, EvalResult, StateEnvRef};
use tla_core::ast::{BoundVar, Expr};
use tla_core::{Span, Spanned};

/// Materialize a SetPred value into a Vec for iteration.
///
/// This evaluates the predicate for each element of the source set *lazily* —
/// elements are streamed from the source iterator and filtered one-by-one so
/// that only elements satisfying the predicate are kept in memory.
///
/// Part of #3747: Previously, this function called `.iter_set()?.collect()` on
/// the source set, materializing the ENTIRE domain before filtering. For specs
/// like SpanTreeTest5Nodes with SetPred over large cross-products (e.g., 2^32
/// elements where only 1024 pass), this caused OOM. Now the source iterator is
/// consumed lazily — memory usage is O(|result|) instead of O(|source|).
///
/// Note: For membership testing, use `check_set_pred_membership` instead - it's O(1) + O(P)
/// vs O(|S|) for this function.
pub fn materialize_setpred_to_vec(ctx: &EvalCtx, spv: &SetPredValue) -> EvalResult<Vec<Value>> {
    // Part of #2990: O(1) chain restore when available, O(n) fallback otherwise.
    let base_ctx = restore_setpred_ctx(ctx, spv)?;

    // Issue #418: Restore captured state_env/next_state_env (TLC parity).
    // SetPredValue captures state at definition time; without restoring it here,
    // predicates referencing state variables evaluate against the wrong state.
    // check_set_pred_membership already does this — materialization must match.
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

    // Part of #3892: Fast path for {E \in SUBSET(S) : \A e \in E : Q(e)}.
    //
    // Mathematical identity: {E \in SUBSET(S) : \A e \in E : Q(e)} = SUBSET({s \in S : Q(s)})
    //
    // Proof: E \in SUBSET(S) with \A e \in E : Q(e) iff E \subseteq {s \in S : Q(s)}.
    //
    // This turns SUBSET(SUBSET Nodes) from 2^(2^n) enumeration to:
    //   enumerate S (2^n for SUBSET Nodes), filter by Q, take SUBSET of result.
    // For SpanTreeTest5Nodes: 2^32 -> 32 filter + 2^10 = 1024 elements.
    if let Value::Subset(sv) = spv.source() {
        if let Some((inner_bound, forall_body)) = try_extract_universal_element_filter(spv) {
            let base_set = sv.base();
            let base_iter = eval_iter_set(&base_ctx, base_set, None)?;

            let mut filtered = Vec::new();
            for elem in base_iter {
                let full_ctx = into_bind_local_bound_var(
                    base_ctx.clone(),
                    &inner_bound,
                    &elem,
                    Some(forall_body.span),
                )?;
                match eval(&full_ctx, &forall_body) {
                    Ok(Value::Bool(true)) => filtered.push(elem),
                    Ok(Value::Bool(false)) => {}
                    Ok(other) => {
                        return Err(EvalError::TypeError {
                            expected: "BOOLEAN",
                            got: other.type_name(),
                            span: Some(forall_body.span),
                        });
                    }
                    Err(e) => return Err(e),
                }
            }

            // Build SUBSET(filtered) and return all its elements.
            let filtered_set = Value::set(filtered);
            let subset_val = SubsetValue::new(filtered_set);
            let result: Vec<Value> = subset_val
                .iter()
                .ok_or_else(|| EvalError::Internal {
                    message: "Failed to iterate SUBSET of filtered set".into(),
                    span: None,
                })?
                .collect();
            return Ok(result);
        }
    }

    // Sorted partition optimization: detect {B \in [1..P -> min..max] : Sum(B,D)=N /\ sorted(B)}
    // and generate only the sorted integer partitions of N instead of iterating all max^P functions.
    // For CarTalkPuzzle M3 (N=121, P=5): 80,631 partitions vs 25.9B function elements.
    if let Value::FuncSet(_) = spv.source() {
        if let Some(params) = super::funcset_partition::try_detect_funcset_partition(spv) {
            let partition_values = super::funcset_partition::generate_partition_values(&params);
            return filter_elements_by_predicate(&base_ctx, spv, partition_values.into_iter());
        }
    }

    // K-subset optimization: detect {x \in SUBSET S : Cardinality(x) = k} in lazy
    // SetPred and use direct C(n,k) enumeration instead of 2^n powerset + filter.
    if let Value::Subset(sv) = spv.source() {
        if let Some(k) = try_extract_cardinality_eq_k_from_setpred(spv) {
            let ksubset = KSubsetValue::new(sv.base().clone(), k);
            return ksubset
                .iter()
                .map(|it| it.collect())
                .ok_or_else(|| EvalError::Internal {
                    message: "K-subset base set not enumerable".into(),
                    span: None,
                });
        }
    }

    // Part of #3747: Stream source elements through the predicate filter instead
    // of collecting the entire source set first. For nested SetPred sources, the
    // inner SetPred is itself streamed via recursion.
    match spv.source() {
        Value::SetPred(inner_spv) => {
            // Recursive case: inner SetPred is also streamed — the recursive call
            // returns only elements passing the inner predicate.
            let inner_elements = materialize_setpred_to_vec(ctx, inner_spv)?;
            filter_elements_by_predicate(&base_ctx, spv, inner_elements.into_iter())
        }
        other => {
            let source_iter = other.iter_set().ok_or_else(|| EvalError::Internal {
                message: "Cannot enumerate infinite SetPred source".into(),
                span: None,
            })?;
            filter_elements_by_predicate(&base_ctx, spv, source_iter)
        }
    }
}

/// Evaluate the predicate for each element from `source_iter` and collect only
/// those that satisfy it. Elements are consumed one at a time from the iterator,
/// so the full source set is never materialized in memory.
fn filter_elements_by_predicate(
    base_ctx: &EvalCtx,
    spv: &SetPredValue,
    source_iter: impl Iterator<Item = Value>,
) -> EvalResult<Vec<Value>> {
    let mut result = Vec::new();
    for elem in source_iter {
        if eval_setpred_predicate(base_ctx, spv, &elem)? {
            result.push(elem);
        }
    }
    Ok(result)
}

/// Evaluate a SetPred predicate for a single element.
///
/// Returns `Ok(true)` if the element passes the predicate, `Ok(false)` if not.
/// Propagates evaluation errors.
///
/// Part of #3978: Made pub(crate) for reuse in streaming SetPred iteration.
pub(crate) fn eval_setpred_predicate(
    base_ctx: &EvalCtx,
    spv: &SetPredValue,
    elem: &Value,
) -> EvalResult<bool> {
    // Use into_bind_local_bound_var to respect BoundPattern::Tuple destructuring.
    // Previously used bind_local with the synthetic name (e.g., "<<x, y>>") which
    // failed to destructure tuple patterns into individual variable bindings.
    let full_ctx =
        into_bind_local_bound_var(base_ctx.clone(), spv.bound(), elem, Some(spv.pred().span))?;
    // Evaluate predicate
    match eval(&full_ctx, spv.pred()) {
        Ok(Value::Bool(true)) => Ok(true),
        Ok(Value::Bool(false)) => Ok(false),
        Ok(other) => {
            // TLC: "Attempted to evaluate an expression of form
            // {x \in S : P(x)} when P was <kind>."
            Err(EvalError::TypeError {
                expected: "BOOLEAN",
                got: other.type_name(),
                span: Some(spv.pred().span),
            })
        }
        // TLC propagates eval errors (SetPredValue.member → Assert.fail).
        // Do NOT silently convert NotInDomain/IndexOutOfBounds to false.
        Err(e) => Err(e),
    }
}

fn map_set_iteration_error_span(err: EvalError, span: Option<Span>) -> EvalError {
    match (err, span) {
        (
            EvalError::TypeError {
                expected,
                got,
                span: None,
            },
            Some(span),
        ) => EvalError::TypeError {
            expected,
            got,
            span: Some(span),
        },
        (EvalError::SetTooLarge { span: None }, Some(span)) => {
            EvalError::SetTooLarge { span: Some(span) }
        }
        (
            EvalError::Internal {
                message,
                span: None,
            },
            Some(span),
        ) => EvalError::Internal {
            message,
            span: Some(span),
        },
        (other, _) => other,
    }
}

/// Iterate over a set value with EvalCtx-aware SetPred handling.
///
/// For `Value::SetPred`, this materializes elements by evaluating its predicate in
/// the captured environment and returns an owned iterator over those elements.
/// For all other set-like values, this returns the value's native iterator.
pub fn eval_iter_set<'a>(
    ctx: &EvalCtx,
    value: &'a Value,
    span: Option<Span>,
) -> EvalResult<Box<dyn Iterator<Item = Value> + 'a>> {
    match value {
        Value::SetPred(spv) => {
            let elems = materialize_setpred_to_vec(ctx, spv)
                .map_err(|err| map_set_iteration_error_span(err, span))?;
            Ok(Box::new(elems.into_iter()))
        }
        // Composite set types may contain SetPred children that prevent
        // iter_set() from working. Decompose and materialize recursively.
        Value::SetCup(cup) if value.iter_set().is_none() => {
            let s1: Vec<Value> = eval_iter_set(ctx, cup.set1(), span)?.collect();
            let s2: Vec<Value> = eval_iter_set(ctx, cup.set2(), span)?.collect();
            let mut combined = s1;
            for elem in s2 {
                if !combined.contains(&elem) {
                    combined.push(elem);
                }
            }
            Ok(Box::new(combined.into_iter()))
        }
        Value::SetCap(cap) if value.iter_set().is_none() => {
            let s1: Vec<Value> = eval_iter_set(ctx, cap.set1(), span)?.collect();
            let s2: Vec<Value> = eval_iter_set(ctx, cap.set2(), span)?.collect();
            let combined: Vec<Value> = s1.into_iter().filter(|e| s2.contains(e)).collect();
            Ok(Box::new(combined.into_iter()))
        }
        Value::SetDiff(diff) if value.iter_set().is_none() => {
            let s1: Vec<Value> = eval_iter_set(ctx, diff.set1(), span)?.collect();
            let s2: Vec<Value> = eval_iter_set(ctx, diff.set2(), span)?.collect();
            let combined: Vec<Value> = s1.into_iter().filter(|e| !s2.contains(e)).collect();
            Ok(Box::new(combined.into_iter()))
        }
        other => other
            .iter_set()
            .ok_or_else(|| EvalError::type_error("Set", other, span)),
    }
}

/// Iterate over a set using TLC's normalized element order.
///
/// This is used by bounded `CHOOSE` and all BFS enumeration paths to match TLC's
/// deterministic element ordering. SetPred and composite sets with SetPred children
/// are materialized first, then normalized.
///
/// Part of #2987: all enumeration callsites should use this instead of `eval_iter_set`
/// to ensure TLC ordering parity.
pub fn eval_iter_set_tlc_normalized<'a>(
    ctx: &EvalCtx,
    value: &'a Value,
    span: Option<Span>,
) -> EvalResult<Box<dyn Iterator<Item = Value> + 'a>> {
    match value {
        Value::SetPred(_) => {
            let materialized = Value::set(eval_iter_set(ctx, value, span)?.collect::<Vec<_>>());
            let normalized: Vec<Value> = materialized
                .iter_set_tlc_normalized()
                .map_err(|err| map_set_iteration_error_span(err, span))?
                .collect();
            Ok(Box::new(normalized.into_iter()))
        }
        // Part of #2987: composite sets with un-iterable children (e.g., SetPred)
        // can't use iter_set_tlc_normalized() directly. Materialize via eval_iter_set
        // (which handles recursive decomposition), then normalize.
        Value::SetCup(_) | Value::SetCap(_) | Value::SetDiff(_) if value.iter_set().is_none() => {
            let elems: Vec<Value> = eval_iter_set(ctx, value, span)?.collect();
            let materialized = Value::set(elems);
            let normalized: Vec<Value> = materialized
                .iter_set_tlc_normalized()
                .map_err(|err| map_set_iteration_error_span(err, span))?
                .collect();
            Ok(Box::new(normalized.into_iter()))
        }
        other => other
            .iter_set_tlc_normalized()
            .map_err(|err| map_set_iteration_error_span(err, span)),
    }
}

/// Stack-allocated variant of `eval_iter_set_tlc_normalized` for quantifier hot paths.
///
/// Part of #3364: For `Value::Set` with homogeneous safe types (the common case in
/// quantifier domain iteration), returns a `TlcSetIterInline::SliceCloned` that avoids
/// the heap allocation of `Box<dyn Iterator>`. All other cases fall back to boxed.
pub fn eval_iter_set_tlc_normalized_inline<'a>(
    ctx: &EvalCtx,
    value: &'a Value,
    span: Option<Span>,
) -> EvalResult<tla_value::TlcSetIterInline<'a>> {
    match value {
        // SetPred / composite: must materialize first — always boxed.
        Value::SetPred(_) => {
            let materialized = Value::set(eval_iter_set(ctx, value, span)?.collect::<Vec<_>>());
            let normalized: Vec<Value> = materialized
                .iter_set_tlc_normalized()
                .map_err(|err| map_set_iteration_error_span(err, span))?
                .collect();
            Ok(tla_value::TlcSetIterInline::Boxed(Box::new(
                normalized.into_iter(),
            )))
        }
        Value::SetCup(_) | Value::SetCap(_) | Value::SetDiff(_) if value.iter_set().is_none() => {
            let elems: Vec<Value> = eval_iter_set(ctx, value, span)?.collect();
            let materialized = Value::set(elems);
            let normalized: Vec<Value> = materialized
                .iter_set_tlc_normalized()
                .map_err(|err| map_set_iteration_error_span(err, span))?
                .collect();
            Ok(tla_value::TlcSetIterInline::Boxed(Box::new(
                normalized.into_iter(),
            )))
        }
        // Common path: delegate to Value's inline variant which avoids Box for safe sets.
        other => other
            .iter_set_tlc_normalized_inline()
            .map_err(|err| map_set_iteration_error_span(err, span)),
    }
}

/// Detect the pattern `{E \in SUBSET(S) : \A e \in E : Q(e)}` in a SetPred.
///
/// Returns `Some((inner_bound, forall_body))` if the SetPred's predicate is a
/// single-bound universal quantifier whose domain is the SetPred's own bound
/// variable. This enables the SUBSET filter optimization in #3892.
///
/// The inner_bound is the forall's bound variable (e.g., "e") and forall_body
/// is the quantifier body Q(e) that will be used to filter elements of S.
fn try_extract_universal_element_filter(spv: &SetPredValue) -> Option<(BoundVar, Spanned<Expr>)> {
    let pred = spv.pred();
    let outer_name = &spv.bound().name.node;

    match &pred.node {
        Expr::Forall(bounds, body) if bounds.len() == 1 => {
            let inner_bound = &bounds[0];
            // The forall's domain must be the SetPred's bound variable (E).
            if let Some(domain) = &inner_bound.domain {
                if let Expr::Ident(ref name, _) = domain.node {
                    if name == outer_name {
                        return Some((inner_bound.clone(), (**body).clone()));
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Detect `{x \in SUBSET S : Cardinality(x) = k}` in a lazy SetPredValue.
///
/// For the lazy materialization path, only matches when k is an integer literal
/// (covers the vast majority of real-world uses). The eager path in eval_set_filter
/// handles arbitrary k expressions via full evaluation.
///
/// Returns `Some(k)` if the pattern matches, `None` otherwise.
fn try_extract_cardinality_eq_k_from_setpred(spv: &SetPredValue) -> Option<usize> {
    let pred = spv.pred();
    let bound_name = &spv.bound().name.node;

    let (lhs, rhs) = match &pred.node {
        Expr::Eq(lhs, rhs) => (lhs.as_ref(), rhs.as_ref()),
        _ => return None,
    };

    // Try both orientations: Cardinality(x) = k  and  k = Cardinality(x)
    if let Some(k) = match_cardinality_eq_literal(bound_name, lhs, rhs) {
        return Some(k);
    }
    if let Some(k) = match_cardinality_eq_literal(bound_name, rhs, lhs) {
        return Some(k);
    }

    None
}

/// Check if `card_side` is `Cardinality(bound_name)` and `k_side` is an integer literal.
fn match_cardinality_eq_literal(
    bound_name: &str,
    card_side: &Spanned<Expr>,
    k_side: &Spanned<Expr>,
) -> Option<usize> {
    if let Expr::Apply(func, args) = &card_side.node {
        if args.len() != 1 {
            return None;
        }
        let is_cardinality = matches!(&func.node, Expr::Ident(name, _) if name == "Cardinality");
        if !is_cardinality {
            return None;
        }
        let is_bound_var = matches!(&args[0].node, Expr::Ident(name, _) if name == bound_name);
        if !is_bound_var {
            return None;
        }
        // k must be a literal integer
        if let Expr::Int(ref n) = k_side.node {
            use num_traits::ToPrimitive;
            return n.to_usize();
        }
    }
    None
}

/// Count elements in a SetPred by streaming through the source set and evaluating
/// the predicate, without materializing the full filtered set into a Vec.
///
/// Part of #3978: For `Cardinality({x \in S : P(x)})`, the old path materialized
/// all matching elements into a Vec<Value> then called `.count()`. This streaming
/// version avoids the Vec allocation entirely -- it counts matching elements as they
/// pass through the predicate filter, discarding each element immediately after.
///
/// Falls back to `None` when special optimizations (SUBSET filter, K-subset,
/// funcset partition) apply, since those produce element lists via different paths.
pub(crate) fn count_setpred_streaming(
    ctx: &EvalCtx,
    spv: &SetPredValue,
) -> EvalResult<Option<usize>> {
    // Check for special optimizations that require materialization:
    // These produce specialized element lists that can't be streamed.
    if let Value::Subset(_) = spv.source() {
        if try_extract_universal_element_filter(spv).is_some() {
            return Ok(None); // Fall back to materializing path
        }
        if try_extract_cardinality_eq_k_from_setpred(spv).is_some() {
            return Ok(None); // Fall back for K-subset
        }
    }
    if let Value::FuncSet(_) = spv.source() {
        if super::funcset_partition::try_detect_funcset_partition(spv).is_some() {
            return Ok(None); // Fall back for partition optimization
        }
    }

    // Restore the captured environment for predicate evaluation.
    let base_ctx = restore_setpred_ctx(ctx, spv)?;

    // Restore captured state/next_state if present (#418 TLC parity).
    let base_ctx = if spv.captured_state().is_some() || spv.captured_next_state().is_some() {
        let state_env = spv
            .captured_state()
            .map(StateEnvRef::from_slice)
            .or(base_ctx.state_env);
        let next_state_env = spv
            .captured_next_state()
            .map(StateEnvRef::from_slice)
            .or(base_ctx.next_state_env);
        base_ctx.with_state_envs_for_eval(state_env, next_state_env)
    } else {
        base_ctx
    };

    // Stream source elements through the predicate and count matches.
    let source_iter: Box<dyn Iterator<Item = Value>> = match spv.source() {
        Value::SetPred(inner_spv) => {
            // Recursive case: materialize inner SetPred (it needs context for predicate eval).
            let inner_elements = materialize_setpred_to_vec(ctx, inner_spv)?;
            Box::new(inner_elements.into_iter())
        }
        other => match other.iter_set() {
            Some(iter) => iter,
            None => return Ok(None), // Source not enumerable, fall back
        },
    };

    let mut count: usize = 0;
    for elem in source_iter {
        if eval_setpred_predicate(&base_ctx, spv, &elem)? {
            count += 1;
        }
    }

    Ok(Some(count))
}

/// Streaming iterator over SetPred elements that yields one element at a time.
///
/// Part of #3978: Instead of materializing all SetPred elements into a Vec before
/// iterating (via `materialize_setpred_to_vec`), this iterator evaluates the predicate
/// on each source element on-demand. This enables short-circuit exit in quantifiers:
/// `\E x \in {f \in [S->S] : P(f)} : Q(x)` can stop as soon as Q(x) is true for
/// some x, without evaluating P(f) for all remaining f.
///
/// Source elements are provided via an owned `Box<dyn Iterator>`. For most source
/// types (FuncSet, Interval, Subset, etc.), the source iterator generates elements
/// lazily, so elements not consumed due to short-circuit are never generated at all.
/// Predicate evaluation is deferred to `next()`.
///
/// For `\E x \in {f \in [S->S] : P(f)} : Q(x)`:
/// - Old path: enumerate all |T|^|S| functions, evaluate P on each, collect to Vec,
///   then iterate and evaluate Q on each matching element.
/// - New path: generate one function at a time from the odometer iterator, evaluate P,
///   if P passes evaluate Q, short-circuit on first match. Source elements not reached
///   are never generated.
///
/// **Note:** This iterator does NOT normalize element order. It yields elements in
/// source-set iteration order filtered by the predicate. This is correct for EXISTS
/// and FORALL (which are order-independent) but NOT for CHOOSE (which requires TLC
/// normalization for determinism). CHOOSE continues to use the materializing path.
pub(crate) struct SetPredStreamIter {
    ctx: EvalCtx,
    source_iter: Box<dyn Iterator<Item = Value>>,
    spv: Box<SetPredValue>,
}

impl Iterator for SetPredStreamIter {
    type Item = EvalResult<Value>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let elem = self.source_iter.next()?;
            match eval_setpred_predicate(&self.ctx, &self.spv, &elem) {
                Ok(true) => return Some(Ok(elem)),
                Ok(false) => continue,
                Err(e) => return Some(Err(e)),
            }
        }
    }
}

/// Create a streaming iterator over a SetPred value's elements.
///
/// Part of #3978: Returns `Some(SetPredStreamIter)` when the value is a SetPred
/// that can be streamed. Returns `None` for non-SetPred values or when the
/// source set cannot provide an iterator (e.g., infinite sets without iter_set).
///
/// The returned iterator handles:
/// - Captured environment restoration (O(1) chain restore or O(n) fallback)
/// - Captured state/next_state restoration (#418 TLC parity)
/// - Recursive SetPred sources (inner SetPred is materialized via recursion)
/// - All SetPred optimizations (SUBSET filter, K-subset, funcset partition) via
///   fallback to `materialize_setpred_to_vec` when those optimizations apply
///
/// Source elements are provided via an owned iterator (`iter_set_owned`). The
/// predicate is NOT evaluated during source iteration -- it is evaluated lazily
/// on each `next()` call. Combined with lazy source iterators (e.g., FuncSet's
/// odometer iterator), this means elements not reached due to short-circuit are
/// never generated or evaluated.
///
/// **When this returns None, the caller should fall back to the materializing path.**
pub(crate) fn try_stream_setpred(
    ctx: &EvalCtx,
    value: &Value,
    _span: Option<Span>,
) -> EvalResult<Option<SetPredStreamIter>> {
    let Value::SetPred(spv) = value else {
        return Ok(None);
    };

    // Check for special optimizations that require materialization:
    // - SUBSET filter optimization (#3892)
    // - Funcset partition optimization (CarTalkPuzzle)
    // - K-subset optimization
    // These produce specialized element lists that can't be streamed element-by-element
    // from the source iterator, so fall back to materialization.
    if let Value::Subset(_) = spv.source() {
        if try_extract_universal_element_filter(spv).is_some() {
            return Ok(None); // Fall back to materializing path for SUBSET optimization
        }
        if try_extract_cardinality_eq_k_from_setpred(spv).is_some() {
            return Ok(None); // Fall back for K-subset optimization
        }
    }
    if let Value::FuncSet(_) = spv.source() {
        if super::funcset_partition::try_detect_funcset_partition(spv).is_some() {
            return Ok(None); // Fall back for partition optimization
        }
    }

    // Restore the captured environment for predicate evaluation.
    let base_ctx = restore_setpred_ctx(ctx, spv)?;

    // Restore captured state/next_state if present (#418 TLC parity).
    let base_ctx = if spv.captured_state().is_some() || spv.captured_next_state().is_some() {
        let state_env = spv
            .captured_state()
            .map(StateEnvRef::from_slice)
            .or(base_ctx.state_env);
        let next_state_env = spv
            .captured_next_state()
            .map(StateEnvRef::from_slice)
            .or(base_ctx.next_state_env);
        base_ctx.with_state_envs_for_eval(state_env, next_state_env)
    } else {
        base_ctx
    };

    // Get an owned source iterator. For most source types (FuncSet, Interval,
    // Subset, etc.), this creates an iterator that generates elements on-demand.
    // The predicate is NOT evaluated during source iteration -- it is evaluated
    // lazily on each next() call, enabling short-circuit when the consumer
    // (EXISTS/FORALL) exits early.
    //
    // For nested SetPred sources, the inner SetPred is materialized recursively
    // (it needs its own EvalCtx for predicate evaluation).
    let source_iter: Box<dyn Iterator<Item = Value>> = match spv.source() {
        Value::SetPred(inner_spv) => {
            // Recursive case: materialize inner SetPred (it needs context for predicate eval).
            let elems = materialize_setpred_to_vec(ctx, inner_spv)?;
            Box::new(elems.into_iter())
        }
        other => match other.iter_set_owned() {
            Some(iter) => iter,
            None => return Ok(None), // Source not enumerable, fall back
        },
    };

    Ok(Some(SetPredStreamIter {
        ctx: base_ctx,
        source_iter,
        spv: spv.clone(),
    }))
}
