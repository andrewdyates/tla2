// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Set builder `{expr : x \in S}`, set filter `{x \in S : P}`, and
//! `count_set_filter_elements`. Split from `quantifiers.rs` as part of #3063.

use super::super::{eval, EvalCtx, EvalError, EvalResult};
use super::quantifiers::{enter_hoist_scope, push_bound_var_mut_preinterned, PreInternedBound};
use super::set_semantics::eval_iter_set;
use crate::value::{
    KSubsetValue, SetBuilder, SetPredCaptures, SetPredValue, SortedSet, SubsetValue, Value,
};
use std::sync::Arc;
use tla_core::ast::{BoundPattern, BoundVar, Expr};
use tla_core::{Span, Spanned};

/// Evaluate {expr : x \in S, y \in T, ...}
/// Clones ctx once at entry, uses O(1) mutable stack binding inside
pub(crate) fn eval_set_builder(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    bounds: &[BoundVar],
    span: Option<Span>,
) -> EvalResult<Value> {
    let mut result = Vec::new();
    let mut local_ctx = ctx.clone();
    eval_set_builder_rec(&mut local_ctx, expr, bounds, &mut result, span)?;
    Ok(Value::Set(Arc::new(SortedSet::from_iter(result))))
}

/// Uses O(1) mutable stack binding instead of O(n) context cloning per element
fn eval_set_builder_rec(
    ctx: &mut EvalCtx,
    expr: &Spanned<Expr>,
    bounds: &[BoundVar],
    result: &mut Vec<Value>,
    span: Option<Span>,
) -> EvalResult<()> {
    if bounds.is_empty() {
        result.push(eval(ctx, expr)?);
        return Ok(());
    }

    let first = &bounds[0];
    let domain = first.domain.as_ref().ok_or_else(|| EvalError::Internal {
        message: "Set builder requires bounded variables".into(),
        span,
    })?;

    let dv = eval(ctx, domain)?;
    let pre = PreInternedBound::from_bound(first);
    let mark = ctx.mark_stack();
    let is_simple = !matches!(&first.pattern, Some(BoundPattern::Tuple(_)));

    // Part of #3128: Hoist bound-variable-invariant subexpressions in set builders.
    let _hoist_guard = enter_hoist_scope(&expr.node, bounds);

    if is_simple {
        let mut first_iter = true;
        for elem in eval_iter_set(ctx, &dv, Some(domain.span))? {
            if first_iter {
                push_bound_var_mut_preinterned(ctx, first, &elem, span, Some(&pre))?;
                first_iter = false;
            } else {
                ctx.update_last_binding_value(elem.clone());
            }
            eval_set_builder_rec(ctx, expr, &bounds[1..], result, span)?;
        }
        ctx.pop_to_mark(&mark);
    } else {
        for elem in eval_iter_set(ctx, &dv, Some(domain.span))? {
            push_bound_var_mut_preinterned(ctx, first, &elem, span, Some(&pre))?;
            eval_set_builder_rec(ctx, expr, &bounds[1..], result, span)?;
            ctx.pop_to_mark(&mark);
        }
    }

    Ok(())
}

/// Evaluate {x \in S : P}
pub(crate) fn eval_set_filter(
    ctx: &EvalCtx,
    bound: &BoundVar,
    pred: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Value> {
    let domain = bound.domain.as_ref().ok_or_else(|| EvalError::Internal {
        message: "Set filter requires bounded variable".into(),
        span,
    })?;

    let dv = eval(ctx, domain)?;

    // K-subset optimization: detect {x \in SUBSET S : Cardinality(x) = k} and replace
    // the 2^n powerset+filter with direct C(n,k) k-subset generation.
    // This is critical for specs like SlushMedium that enumerate fixed-size subsets.
    if let Value::Subset(ref sv) = dv {
        if let Some(k) = try_extract_cardinality_eq_k(ctx, bound, pred)? {
            let base = sv.base().clone();
            return Ok(Value::KSubset(KSubsetValue::new(base, k)));
        }
    }

    // Nested powerset optimization (Part of #3826):
    // Detect {E \in SUBSET(X) : \A e \in E : P(e)} and rewrite to SUBSET({e \in X : P(e)}).
    //
    // This is critical for SpanTreeTest5Nodes where the Init constraint is:
    //   Edges \in {E \in SUBSET(SUBSET Nodes) : \A e \in E : Cardinality(e) = 2}
    //
    // Without this: SUBSET(SUBSET Nodes) with 5 nodes = 2^(2^5) = 2^32 ~ 4 billion elements,
    //   then filtered down to SUBSET(C(5,2) edges) = 2^10 = 1024 elements.
    // With this: we compute {e \in SUBSET Nodes : Cardinality(e) = 2} = 10 edges first,
    //   then SUBSET(10 edges) = 1024 elements -- directly.
    //
    // The rewrite is valid because \A e \in E : P(e) filters each element independently,
    // so {E \in SUBSET(X) : \A e \in E : P(e)} = SUBSET({e \in X : P(e)}).
    if let Value::Subset(ref sv) = dv {
        if let Some(filtered_base) =
            try_optimize_nested_powerset_filter(ctx, bound, pred, sv, span)?
        {
            return Ok(Value::Subset(SubsetValue::new(filtered_base)));
        }
    }

    // TLC Tool.java:2475 dispatches set filter based on `instanceof Reducible`.
    // Only SetEnumValue and IntervalValue implement Reducible — these get eager
    // enumeration with filtering. All other set types (BigUnion, FuncSet, RecordSet,
    // TupleSet, KSubset, SetCup, SetCap, SetDiff, Subset, SetPred) return a lazy
    // SetPredValue that defers enumeration until needed.
    let is_reducible = matches!(dv, Value::Set(_) | Value::Interval(_));
    if !is_reducible {
        if !dv.is_set() {
            return Err(EvalError::type_error("Set", &dv, Some(domain.span)));
        }
        let (captured_state, captured_next_state) = ctx.snapshot_state_envs();
        // Part of #2895 Step 4: BindingChain is the sole source of truth for all locals
        // (both AST and compiled paths). No fast_locals materialization needed.
        let (captured_chain, chain_depth) = (ctx.bindings.clone(), ctx.binding_depth);
        let captured_chain: Box<dyn tla_value::CapturedChain> = Box::new(captured_chain);
        let captures =
            SetPredCaptures::new(Arc::clone(&ctx.env), captured_state, captured_next_state)
                .with_captured_chain(captured_chain, chain_depth);
        let spv = SetPredValue::new_with_captures(dv, bound.clone(), pred.clone(), captures);
        return Ok(Value::SetPred(Box::new(spv)));
    }

    // Enumerable domain: evaluate eagerly
    let iter = dv
        .iter_set()
        .ok_or_else(|| EvalError::type_error("Set", &dv, Some(domain.span)))?;

    // Optimization: reuse a single EvalCtx with push/pop instead of cloning per element
    let mut local_ctx = ctx.clone();
    let pre = PreInternedBound::from_bound(bound);
    let mark = local_ctx.mark_stack();
    let mut result = SetBuilder::new();
    let is_simple = !matches!(&bound.pattern, Some(BoundPattern::Tuple(_)));

    // Part of #3128: Hoist bound-variable-invariant subexpressions in set filters.
    let _hoist_guard = enter_hoist_scope(&pred.node, std::slice::from_ref(bound));

    if is_simple {
        // Part of #3063 Phase E: push once, update in-place for subsequent iterations.
        let mut first_iter = true;
        for elem in iter {
            if first_iter {
                push_bound_var_mut_preinterned(&mut local_ctx, bound, &elem, span, Some(&pre))?;
                first_iter = false;
            } else {
                local_ctx.update_last_binding_value(elem.clone());
            }
            // TLC propagates eval errors (SetPredValue.member → Assert.fail).
            // Do NOT silently convert NotInDomain/IndexOutOfBounds to false.
            let pv = eval(&local_ctx, pred)?;
            let include = pv
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", &pv, Some(pred.span)))?;
            if include {
                result.insert(elem);
            }
        }
        local_ctx.pop_to_mark(&mark);
    } else {
        for elem in iter {
            push_bound_var_mut_preinterned(&mut local_ctx, bound, &elem, span, Some(&pre))?;
            let pv = eval(&local_ctx, pred)?;
            local_ctx.pop_to_mark(&mark);
            let include = pv
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", &pv, Some(pred.span)))?;
            if include {
                result.insert(elem);
            }
        }
    }

    Ok(result.build_value())
}

/// Count elements in a set filter without building the set.
/// Returns None if the domain is not enumerable.
pub(crate) fn count_set_filter_elements(
    ctx: &EvalCtx,
    domain_val: &Value,
    bound: &BoundVar,
    pred: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Option<usize>> {
    // #1814: SetPred domains (lazy set filters, e.g. {x \in SUBSET S : P(x)})
    // return None from iter_set() since they need eval context to enumerate.
    // Use eval_iter_set which materializes SetPred transparently.
    let iter: Box<dyn Iterator<Item = Value> + '_> = if let Value::SetPred(_) = domain_val {
        eval_iter_set(ctx, domain_val, span)?
    } else {
        match domain_val.iter_set() {
            Some(it) => it,
            None => return Ok(None), // Not enumerable (StringSet, AnySet, etc.)
        }
    };

    let mut count: usize = 0;
    let mut local_ctx = ctx.clone();
    let mark = local_ctx.mark_stack();
    let pre = PreInternedBound::from_bound(bound);
    let is_simple = !matches!(&bound.pattern, Some(BoundPattern::Tuple(_)));

    // Part of #3128: Hoist bound-variable-invariant subexpressions in set filter count.
    let _hoist_guard = enter_hoist_scope(&pred.node, std::slice::from_ref(bound));

    // Part of #3073: Push once, update in-place for subsequent iterations.
    // Also uses PreInternedBound to avoid repeated intern_string/intern_name.
    if is_simple {
        let mut first_iter = true;
        for elem in iter {
            if first_iter {
                push_bound_var_mut_preinterned(&mut local_ctx, bound, &elem, span, Some(&pre))?;
                first_iter = false;
            } else {
                local_ctx.update_last_binding_value(elem.clone());
            }
            let pv = eval(&local_ctx, pred)?;
            let include = pv
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", &pv, Some(pred.span)))?;
            if include {
                count += 1;
            }
        }
        local_ctx.pop_to_mark(&mark);
    } else {
        for elem in iter {
            push_bound_var_mut_preinterned(&mut local_ctx, bound, &elem, span, Some(&pre))?;
            let pv = eval(&local_ctx, pred)?;
            local_ctx.pop_to_mark(&mark);
            let include = pv
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", &pv, Some(pred.span)))?;
            if include {
                count += 1;
            }
        }
    }
    Ok(Some(count))
}

/// Detect the pattern `Cardinality(x) = k` (or `k = Cardinality(x)`) in a SetFilter
/// predicate where `x` is the bound variable.
///
/// Returns `Some(k)` if the pattern matches and `k` evaluates to a concrete
/// non-negative integer. Returns `None` if the pattern doesn't match. Returns
/// `Err` only if evaluating `k` raises an eval error.
///
/// This enables the k-subset optimization: `{x \in SUBSET S : Cardinality(x) = k}`
/// generates C(n,k) subsets directly instead of 2^n powerset + filter.
fn try_extract_cardinality_eq_k(
    ctx: &EvalCtx,
    bound: &BoundVar,
    pred: &Spanned<Expr>,
) -> EvalResult<Option<usize>> {
    let bound_name = &bound.name.node;

    // Match Eq(lhs, rhs) -- the predicate must be an equality test.
    let (lhs, rhs) = match &pred.node {
        Expr::Eq(lhs, rhs) => (lhs.as_ref(), rhs.as_ref()),
        _ => return Ok(None),
    };

    // Try both orientations: Cardinality(x) = k  and  k = Cardinality(x)
    if let Some(k) = try_match_cardinality_eq(ctx, bound_name, lhs, rhs)? {
        return Ok(Some(k));
    }
    if let Some(k) = try_match_cardinality_eq(ctx, bound_name, rhs, lhs)? {
        return Ok(Some(k));
    }

    Ok(None)
}

/// Check if `card_side` is `Cardinality(bound_name)` and `k_side` evaluates to
/// a concrete non-negative integer. Returns `Some(k)` on match.
fn try_match_cardinality_eq(
    ctx: &EvalCtx,
    bound_name: &str,
    card_side: &Spanned<Expr>,
    k_side: &Spanned<Expr>,
) -> EvalResult<Option<usize>> {
    // card_side must be Apply(Ident("Cardinality"), [Ident(bound_name)])
    if let Expr::Apply(func, args) = &card_side.node {
        if args.len() != 1 {
            return Ok(None);
        }
        // Function must be Cardinality
        let is_cardinality = matches!(&func.node, Expr::Ident(name, _) if name == "Cardinality");
        if !is_cardinality {
            return Ok(None);
        }
        // Argument must be the bound variable
        let is_bound_var = matches!(&args[0].node, Expr::Ident(name, _) if name == bound_name);
        if !is_bound_var {
            return Ok(None);
        }
        // k_side must evaluate to a concrete non-negative integer.
        // Only attempt evaluation if k_side does NOT reference the bound variable,
        // to avoid polluting the context or hitting undefined variable errors.
        if expr_references_name(&k_side.node, bound_name) {
            return Ok(None);
        }
        let k_val = eval(ctx, k_side)?;
        if let Some(n) = k_val.to_bigint() {
            use num_traits::ToPrimitive;
            if let Some(k) = n.to_usize() {
                return Ok(Some(k));
            }
            // Negative or too large -- fall through to normal path
        }
    }
    Ok(None)
}

/// Check if an expression references a given variable name.
/// Conservative: returns true if the name appears anywhere in the expression tree.
fn expr_references_name(expr: &Expr, name: &str) -> bool {
    match expr {
        Expr::Ident(n, _) | Expr::StateVar(n, _, _) => n == name,
        Expr::Int(_) | Expr::Bool(_) | Expr::String(_) | Expr::OpRef(_) => false,
        Expr::Apply(f, args) => {
            expr_references_name(&f.node, name)
                || args.iter().any(|a| expr_references_name(&a.node, name))
        }
        Expr::FuncApply(f, a) => {
            expr_references_name(&f.node, name) || expr_references_name(&a.node, name)
        }
        Expr::Eq(a, b)
        | Expr::Neq(a, b)
        | Expr::Lt(a, b)
        | Expr::Leq(a, b)
        | Expr::Gt(a, b)
        | Expr::Geq(a, b)
        | Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::Equiv(a, b)
        | Expr::Union(a, b)
        | Expr::Intersect(a, b)
        | Expr::SetMinus(a, b)
        | Expr::Subseteq(a, b)
        | Expr::In(a, b)
        | Expr::NotIn(a, b)
        | Expr::FuncSet(a, b) => {
            expr_references_name(&a.node, name) || expr_references_name(&b.node, name)
        }
        Expr::Not(a) | Expr::Powerset(a) | Expr::BigUnion(a) | Expr::Domain(a) => {
            expr_references_name(&a.node, name)
        }
        Expr::If(c, t, e) => {
            expr_references_name(&c.node, name)
                || expr_references_name(&t.node, name)
                || expr_references_name(&e.node, name)
        }
        // For complex expressions (Let, Lambda, quantifiers, etc.), conservatively
        // return true to avoid false negatives. The optimization just won't fire.
        _ => true,
    }
}

/// Detect the pattern `{E \in SUBSET(X) : \A e \in E : P(e)}` and rewrite to
/// `SUBSET({e \in X : P(e)})`.
///
/// This is valid because `\A e \in E : P(e)` keeps only those subsets of X where
/// every element satisfies P. This is exactly `SUBSET({e \in X : P(e)})`.
///
/// Returns `Some(filtered_base_value)` when the pattern matches, where the caller
/// wraps the result in `Value::Subset(SubsetValue::new(filtered_base))`.
///
/// Returns `None` when the pattern doesn't match (predicate is not a universal
/// quantification over elements of the bound variable, or references the bound
/// variable in a way that prevents the rewrite).
///
/// Part of #3826.
fn try_optimize_nested_powerset_filter(
    ctx: &EvalCtx,
    outer_bound: &BoundVar,
    pred: &Spanned<Expr>,
    subset_val: &SubsetValue,
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    let outer_name = &outer_bound.name.node;

    // The predicate must be Forall with exactly one bound variable whose domain
    // is the outer bound variable (i.e., \A e \in E : P(e)).
    let (forall_bounds, forall_body) = match &pred.node {
        Expr::Forall(bounds, body) => (bounds, body),
        _ => return Ok(None),
    };

    // Must have exactly one bound variable in the Forall.
    if forall_bounds.len() != 1 {
        return Ok(None);
    }

    let inner_bound = &forall_bounds[0];

    // The domain of the inner bound must be the outer bound variable.
    // i.e., \A e \in E where E is the SetFilter's bound variable.
    let inner_domain = match &inner_bound.domain {
        Some(d) => d,
        None => return Ok(None),
    };
    let domain_is_outer = matches!(&inner_domain.node, Expr::Ident(name, _) if name == outer_name);
    if !domain_is_outer {
        return Ok(None);
    }

    // The body of the Forall must NOT reference the outer variable (E), only the
    // inner variable (e). This ensures the predicate tests elements independently.
    if expr_references_name(&forall_body.node, outer_name) {
        return Ok(None);
    }

    // Pattern matched! Rewrite:
    // {E \in SUBSET(X) : \A e \in E : P(e)}  =>  SUBSET({e \in X : P(e)})
    //
    // 1. Get the base set X from the SubsetValue
    // 2. Evaluate {inner_bound_name \in X : forall_body} as a set filter
    // 3. Return the filtered base (caller wraps in SUBSET)

    let base = subset_val.base().clone();

    // Check if the base is enumerable. If not, we can't filter it.
    let iter = match base.iter_set() {
        Some(it) => it,
        None => return Ok(None),
    };

    // Evaluate the inner filter: {e \in X : P(e)}
    let inner_name = &inner_bound.name.node;
    let mut local_ctx = ctx.clone();
    let pre = PreInternedBound::from_bound(inner_bound);
    let mark = local_ctx.mark_stack();
    let mut result = SetBuilder::new();
    let is_simple = !matches!(&inner_bound.pattern, Some(BoundPattern::Tuple(_)));

    if is_simple {
        let mut first_iter = true;
        for elem in iter {
            if first_iter {
                push_bound_var_mut_preinterned(
                    &mut local_ctx,
                    inner_bound,
                    &elem,
                    span,
                    Some(&pre),
                )?;
                first_iter = false;
            } else {
                local_ctx.update_last_binding_value(elem.clone());
            }
            let pv = eval(&local_ctx, forall_body)?;
            let include = pv
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", &pv, Some(forall_body.span)))?;
            if include {
                result.insert(elem);
            }
        }
        local_ctx.pop_to_mark(&mark);
    } else {
        for elem in iter {
            push_bound_var_mut_preinterned(
                &mut local_ctx,
                inner_bound,
                &elem,
                span,
                Some(&pre),
            )?;
            let pv = eval(&local_ctx, forall_body)?;
            local_ctx.pop_to_mark(&mark);
            let include = pv
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", &pv, Some(forall_body.span)))?;
            if include {
                result.insert(elem);
            }
        }
    }

    let filtered = result.build_value();
    let _ = inner_name; // suppress unused warning

    Ok(Some(filtered))
}
