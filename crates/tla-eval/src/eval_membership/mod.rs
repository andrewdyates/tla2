// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Membership testing and lazy evaluation helpers for TLA+ set operations.
// Extracted from core.rs as part of #1219 decomposition.
//
// This module contains:
// - func_in_func_set: Check function membership in [S -> T]
// - is_lazy_membership_expr / needs_lazy_membership: Detect expressions needing lazy handling
// - eval_membership_lazy: Lazy membership for SUBSET, [S->T], Seq(S), RecordSet, Union, SetFilter
// - check_set_pred_membership: Check membership in SetPred values (in set_pred submodule)

mod set_pred;

pub use set_pred::{check_set_pred_membership, restore_setpred_ctx};

use super::{
    eval, eval_iter_set, push_bound_var_mut, EvalCtx, EvalError, EvalResult, Expr, FuncValue, Span,
    Spanned, Value,
};
use num_bigint::BigInt;
use num_traits::Zero;

pub(super) fn func_in_func_set(
    ctx: &EvalCtx,
    func: &FuncValue,
    domain_expr: &Spanned<Expr>,
    range_expr: &Spanned<Expr>,
) -> EvalResult<bool> {
    let dv = eval(ctx, domain_expr)?;

    // Handle both Set and Interval domains
    let domain = dv
        .to_sorted_set()
        .ok_or_else(|| EvalError::type_error("Set", &dv, Some(domain_expr.span)))?;

    if !func.domain_eq_sorted_set(&domain) {
        return Ok(false);
    }

    // Part of #3123: Always evaluate range to a Value. Lazy set types (SetCup,
    // RecordSet, Subset, FuncSet) are constructed symbolically in O(1) without
    // materializing elements, and their set_contains() methods support efficient
    // value-level membership testing. This evaluates the range expression ONCE
    // instead of re-traversing the AST per domain element via eval_membership_lazy,
    // matching TLC's approach where SetOfFcnsValue stores a pre-evaluated range
    // and calls range.member() per function value.
    let range_val = eval(ctx, range_expr)?;

    for d in &domain {
        let v = match func.mapping_get(d) {
            Some(v) => v,
            None => return Ok(false),
        };

        // Value::set_contains handles Set, Interval, ModelValue (Nat/Int/Real),
        // SetCup, RecordSet, Subset, FuncSet, etc. Returns None only when an
        // evaluation context is needed (SetPred inside compound sets).
        let in_range = match range_val.set_contains(v) {
            Some(c) => c,
            None => super::set_contains_with_ctx(ctx, v, &range_val, Some(range_expr.span))?,
        };

        if !in_range {
            return Ok(false);
        }
    }

    Ok(true)
}

/// Check if an expression requires lazy membership checking (FuncSet, Powerset, Seq, RecordSet, SetBuilder)
pub(super) fn is_lazy_membership_expr(expr: &Expr) -> bool {
    match expr {
        Expr::FuncSet(_, _) | Expr::Powerset(_) | Expr::RecordSet(_) | Expr::SetFilter(_, _) => {
            true
        }
        // SetBuilder: {expr : x \in S} -- check inverse membership lazily by finding
        // x \in S such that expr(x) = target, avoiding full materialization. Part of #3978.
        Expr::SetBuilder(_, _) => true,
        // Union: can check membership lazily as (x \in A) \/ (x \in B)
        Expr::Union(_, _) => true,
        Expr::Apply(op, args) => {
            // Check for Seq(S) pattern
            if let Expr::Ident(name, _) = &op.node {
                name == "Seq" && args.len() == 1
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Check if an expression (potentially through Ident resolution) requires lazy membership checking
pub(super) fn needs_lazy_membership(ctx: &EvalCtx, expr: &Spanned<Expr>) -> bool {
    if is_lazy_membership_expr(&expr.node) {
        return true;
    }
    // Also check if expr is an Ident that resolves to a lazy membership expression
    if let Expr::Ident(name, _) = &expr.node {
        let resolved_name = ctx.resolve_op_name(name);
        if let Some(def) = ctx.get_op(resolved_name) {
            if def.params.is_empty() && is_lazy_membership_expr(&def.body.node) {
                return true;
            }
        }
    }
    false
}

/// Check if a value is a member of a set expression, with lazy handling for SUBSET, [S -> T], Seq(S), and RecordSet
/// This avoids eager enumeration of large/infinite sets
///
/// Part of #3073: Takes `&Value` instead of `Value` to avoid cloning in the union
/// iteration hot path. For MultiPaxos TypeOK (`\A m \in msgs: m \in Messages`),
/// this eliminates ~5 record clones per message per state across 5 union branches.
pub(super) fn eval_membership_lazy(
    ctx: &EvalCtx,
    value: &Value,
    set_expr: &Spanned<Expr>,
) -> EvalResult<bool> {
    // Follow zero-arg operator aliases to their underlying lazy-membership expressions.
    // Keep this iterative so long chains of aliases cannot overflow the stack.
    let mut set_expr = set_expr;
    loop {
        let Expr::Ident(name, _) = &set_expr.node else {
            break;
        };
        let resolved_name = ctx.resolve_op_name(name);
        let Some(def) = ctx.get_op(resolved_name) else {
            break;
        };
        if !def.params.is_empty() {
            break;
        }
        if !is_lazy_membership_expr(&def.body.node) {
            break;
        }
        // Part of #3123: Before following through to the lazy body, try evaluating
        // the Ident normally. The zero-arg operator cache will return the cached
        // result if available (e.g., `Message` evaluated once then reused). If the
        // result is a concrete finite set (Set, Interval, SetCup, etc.), use
        // set_contains() directly instead of walking the AST tree for each
        // membership check. This avoids re-constructing SetMap elements on every
        // membership test in specs like MCLamportMutex where
        // `Message = {AckMessage, RelMessage} \union {ReqMessage(c) : c \in Clock}`
        // is checked ~19.5M times.
        //
        // Fix #3802: Skip eager eval for SetFilter bodies. SetFilter with
        // non-reducible domains (e.g., SUBSET SUBSET S) produces SetPred values
        // that the zero-arg cache materializes via materialize_setpred_to_vec,
        // causing exponential enumeration. Fall through to the lazy SetFilter
        // handler below which checks membership via source-set + predicate.
        if !matches!(def.body.node, Expr::SetFilter(_, _)) {
            if let Ok(set_val) = eval(ctx, set_expr) {
                match set_val.set_contains(value) {
                    Some(c) => return Ok(c),
                    None => {
                        // Indeterminate (e.g. SetPred inside compound set) --
                        // fall back to context-aware check.
                        return super::set_contains_with_ctx(
                            ctx,
                            value,
                            &set_val,
                            Some(set_expr.span),
                        );
                    }
                }
            }
        }
        set_expr = &def.body;
    }

    // Handle SUBSET lazily: v \in SUBSET S <==> v is a set AND v \subseteq S
    if let Expr::Powerset(inner) = &set_expr.node {
        // Use eval_iter_set for SetPred-aware iteration (Part of #1828/#1830).
        // Without this, SetPred values would return false for SUBSET membership
        // because Value::iter_set() returns None for SetPred.
        match eval_iter_set(ctx, value, None) {
            Ok(iter) => {
                for elem in iter {
                    if !eval_membership_lazy(ctx, &elem, inner)? {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
            Err(EvalError::TypeError {
                expected: "Set", ..
            }) => {
                // Value is not a set-like type — cannot be in SUBSET S
                return Ok(false);
            }
            Err(e) => {
                // Propagate real evaluation errors (e.g. SetPred predicate failures)
                return Err(e);
            }
        }
    }

    // Handle SetFilter lazily: v \in {x \in S : P(x)} <==> v \in S /\ P(v)
    if let Expr::SetFilter(bound, pred) = &set_expr.node {
        let domain_expr = bound.domain.as_ref().ok_or_else(|| EvalError::Internal {
            message: "SetFilter requires bounded variable".into(),
            span: Some(set_expr.span),
        })?;

        if !eval_membership_lazy(ctx, value, domain_expr)? {
            return Ok(false);
        }

        let mut local_ctx = ctx.clone();
        let mark = local_ctx.mark_stack();
        push_bound_var_mut(&mut local_ctx, bound, value, Some(set_expr.span))?;

        // TLC propagates eval errors here (SetPredValue.member → Assert.fail).
        // Do NOT silently convert NotInDomain/IndexOutOfBounds to false.
        let pv = eval(&local_ctx, pred)?;
        let include = pv
            .as_bool()
            .ok_or_else(|| EvalError::type_error("BOOLEAN", &pv, Some(pred.span)))?;

        local_ctx.pop_to_mark(&mark);
        return Ok(include);
    }

    // Handle SetBuilder lazily: v \in {expr(x) : x \in S} <==> \E x \in S : expr(x) = v
    // Part of #3978: Instead of materializing all mapped values, iterate domain elements
    // and short-circuit on the first match. This is O(|S|) in the worst case but
    // O(1) best case, vs always O(|S|) for eager materialization + linear scan.
    if let Expr::SetBuilder(body, bounds) = &set_expr.node {
        return check_set_builder_membership(ctx, value, body, bounds, Some(set_expr.span));
    }

    // Handle Union lazily: v \in (A \cup B) <==> (v \in A) \/ (v \in B)
    // This is critical for efficient type checking in specs like MultiPaxos where
    // Messages = PrepareMsgs \cup PrepareReplyMsgs \cup AcceptMsgs \cup ...
    // Without lazy union, we'd compute the full Cartesian product of all message types.
    if let Expr::Union(left, right) = &set_expr.node {
        // Part of #758: Union trees produced by stdlib expansions can be *very* deep.
        // Avoid recursion proportional to union depth by flattening via an explicit stack.
        let mut pending: Vec<&Spanned<Expr>> = Vec::new();
        pending.push(right);
        pending.push(left);

        while let Some(expr) = pending.pop() {
            // Resolve identifier aliases iteratively (same logic as above) so
            // `(A ∪ B)` can safely contain `Ident` chains as children.
            let mut expr = expr;
            loop {
                let Expr::Ident(name, _) = &expr.node else {
                    break;
                };
                let resolved_name = ctx.resolve_op_name(name);
                let Some(def) = ctx.get_op(resolved_name) else {
                    break;
                };
                if !def.params.is_empty() {
                    break;
                }
                if !is_lazy_membership_expr(&def.body.node) {
                    break;
                }
                // Part of #3123: Same eager-eval shortcut as outer loop.
                // For union branches that resolve to cached concrete sets,
                // use set_contains() directly.
                // Fix #3802: Skip eager eval for SetFilter bodies (see outer loop comment).
                if !matches!(def.body.node, Expr::SetFilter(_, _)) {
                    if let Ok(set_val) = eval(ctx, expr) {
                        match set_val.set_contains(value) {
                            Some(true) => return Ok(true),
                            Some(false) => break, // Not in this branch, try next
                            None => {
                                // Indeterminate -- fall back to context-aware check.
                                if super::set_contains_with_ctx(
                                    ctx,
                                    value,
                                    &set_val,
                                    Some(expr.span),
                                )? {
                                    return Ok(true);
                                }
                                break; // Not in this branch, try next
                            }
                        }
                    }
                }
                expr = &def.body;
            }

            match &expr.node {
                Expr::Union(l, r) => {
                    // Check left first (TLA+ semantics: short-circuit is OK).
                    pending.push(r);
                    pending.push(l);
                }
                _ => {
                    if eval_membership_lazy(ctx, value, expr)? {
                        return Ok(true);
                    }
                }
            }
        }

        return Ok(false);
    }

    // Handle [S -> T] lazily: v \in [S -> T] <==> v is a function with domain S and range in T
    if let Expr::FuncSet(domain_expr, range_expr) = &set_expr.node {
        // Performance optimization: evaluate the range expression ONCE and use
        // Value::set_contains() for each element, matching TLC's approach in
        // SetOfFcnsValue. This avoids re-traversing the AST per element via
        // eval_membership_lazy. Falls back to lazy evaluation when set_contains()
        // returns None (indeterminate, e.g. SetPred).
        match value {
            Value::Func(f) => return func_in_func_set(ctx, f, domain_expr, range_expr),
            // IntFunc is an array-backed function with integer interval domain
            Value::IntFunc(f) => {
                // Check domain: function set domain must equal min..max
                let domain_val = eval(ctx, domain_expr)?;
                let actual_domain = domain_val.to_sorted_set().ok_or_else(|| {
                    EvalError::type_error("Set", &domain_val, Some(domain_expr.span))
                })?;
                if !actual_domain.equals_integer_interval(
                    tla_value::IntIntervalFunc::min(f),
                    tla_value::IntIntervalFunc::max(f),
                ) {
                    return Ok(false);
                }
                // Evaluate range once, then check each value via set_contains
                let range_val = eval(ctx, range_expr)?;
                for val in f.values() {
                    let in_range = match range_val.set_contains(val) {
                        Some(c) => c,
                        None => super::set_contains_with_ctx(
                            ctx,
                            val,
                            &range_val,
                            Some(range_expr.span),
                        )?,
                    };
                    if !in_range {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
            // Tuples/Seqs are functions with domain 1..n
            Value::Tuple(elems) => {
                // Check domain: expected is 1..n
                let domain_val = eval(ctx, domain_expr)?;
                let actual_domain = domain_val.to_sorted_set().ok_or_else(|| {
                    EvalError::type_error("Set", &domain_val, Some(domain_expr.span))
                })?;
                if !actual_domain.equals_sequence_domain(elems.len()) {
                    return Ok(false);
                }
                // Evaluate range once, then check each element via set_contains
                let range_val = eval(ctx, range_expr)?;
                for elem in elems.iter() {
                    let in_range = match range_val.set_contains(elem) {
                        Some(c) => c,
                        None => super::set_contains_with_ctx(
                            ctx,
                            elem,
                            &range_val,
                            Some(range_expr.span),
                        )?,
                    };
                    if !in_range {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
            Value::Seq(seq) => {
                // Check domain: expected is 1..n
                let domain_val = eval(ctx, domain_expr)?;
                let actual_domain = domain_val.to_sorted_set().ok_or_else(|| {
                    EvalError::type_error("Set", &domain_val, Some(domain_expr.span))
                })?;
                if !actual_domain.equals_sequence_domain(seq.len()) {
                    return Ok(false);
                }
                // Evaluate range once, then check each element via set_contains
                let range_val = eval(ctx, range_expr)?;
                for elem in seq.iter() {
                    let in_range = match range_val.set_contains(elem) {
                        Some(c) => c,
                        None => super::set_contains_with_ctx(
                            ctx,
                            elem,
                            &range_val,
                            Some(range_expr.span),
                        )?,
                    };
                    if !in_range {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
            _ => return Ok(false),
        }
    }

    // Handle Seq(S) lazily: v \in Seq(S) <==> v is a sequence AND all elements are in S
    // Seq(S) is represented as Apply(Ident("Seq"), [S])
    if let Expr::Apply(op, args) = &set_expr.node {
        if let Expr::Ident(name, _) = &op.node {
            if name == "Seq" && args.len() == 1 {
                let elem_set_expr = &args[0];
                // Check if value is a sequence/tuple and all elements are in S
                if let Some(elems) = value.as_seq_or_tuple_elements() {
                    for elem in elems.iter() {
                        if !eval_membership_lazy(ctx, elem, elem_set_expr)? {
                            return Ok(false);
                        }
                    }
                    return Ok(true);
                }
                return match value {
                    // TLA+ treats functions 1..n -> T as sequences
                    Value::Func(f) => {
                        // Check if domain is 1..n for some n
                        if !f.domain_is_sequence() {
                            return Ok(false);
                        }
                        // Check all values are in S
                        for v in f.mapping_values() {
                            if !eval_membership_lazy(ctx, v, elem_set_expr)? {
                                return Ok(false);
                            }
                        }
                        Ok(true)
                    }
                    // IntFunc with domain 1..n is also a sequence
                    Value::IntFunc(f) => {
                        // Check if domain is 1..n for some n
                        if tla_value::IntIntervalFunc::min(f) != 1 {
                            return Ok(false);
                        }
                        // Check all values are in S
                        for v in f.values() {
                            if !eval_membership_lazy(ctx, v, elem_set_expr)? {
                                return Ok(false);
                            }
                        }
                        Ok(true)
                    }
                    _ => Ok(false),
                };
            }
        }
    }

    // Handle RecordSet lazily: v \in [f1: S1, f2: S2, ...] <==> v is a record with exactly those fields AND v.f1 \in S1 AND v.f2 \in S2 AND ...
    if let Expr::RecordSet(fields) = &set_expr.node {
        match value {
            Value::Record(rec) => {
                // Check that record has exactly the same fields
                if rec.len() != fields.len() {
                    return Ok(false);
                }
                // Check each field
                for (field_name, field_set_expr) in fields {
                    match rec.get(field_name.node.as_str()) {
                        Some(field_val) => {
                            if !eval_membership_lazy(ctx, field_val, field_set_expr)? {
                                return Ok(false);
                            }
                        }
                        None => return Ok(false), // Record doesn't have this field
                    }
                }
                return Ok(true);
            }
            _ => return Ok(false),
        }
    }

    // For other expressions, evaluate eagerly and check membership
    let set_val = eval(ctx, set_expr)?;

    // Handle ModelValue for infinite sets (Nat, Int, Real)
    if let Value::ModelValue(name) = &set_val {
        return match name.as_ref() {
            "Nat" => match value {
                Value::SmallInt(n) => Ok(*n >= 0),
                Value::Int(n) => Ok(**n >= BigInt::zero()),
                _ => Ok(false),
            },
            "Int" => Ok(matches!(value, Value::SmallInt(_) | Value::Int(_))),
            "Real" => Ok(matches!(value, Value::SmallInt(_) | Value::Int(_))), // Int ⊆ Real
            _ => Err(EvalError::type_error("Set", &set_val, Some(set_expr.span))),
        };
    }

    // Handle both Set and Interval using set_contains.
    // If set_contains returns None (e.g. SetPred inside SetCup/SetDiff/SetCap),
    // fall back to context-aware recursive decomposition.
    let contains = match set_val.set_contains(value) {
        Some(c) => c,
        None => super::set_contains_with_ctx(ctx, value, &set_val, Some(set_expr.span))?,
    };
    Ok(contains)
}

/// Check membership in a SetBuilder expression: v \in {expr : x \in S, y \in T, ...}
///
/// This is equivalent to `\E x \in S, y \in T, ... : expr(x, y, ...) = v`.
///
/// Part of #3979: Uses inverse membership checking for invertible patterns
/// (tuple construction, record construction, identity mapping) to avoid
/// iterating domain elements entirely. Falls back to iterate-and-short-circuit
/// for general expressions.
///
/// Inverse patterns (O(k) where k = number of bound variables):
/// - Tuple: `{<<x, y>> : x \in S, y \in T}` — decompose target tuple, check components
/// - Record: `{[a |-> x, b |-> y] : x \in S, y \in T}` — decompose target record, check fields
/// - Identity: `{x : x \in S}` — check `target \in S` directly
///
/// Fallback (O(|S1| * |S2| * ...) worst case, short-circuits on first match):
/// - General expressions: iterate domain elements, evaluate body, compare to target
fn check_set_builder_membership(
    ctx: &EvalCtx,
    target: &Value,
    body: &Spanned<Expr>,
    bounds: &[tla_core::ast::BoundVar],
    span: Option<Span>,
) -> EvalResult<bool> {
    // Try inverse membership checking for invertible patterns.
    // This avoids iterating the entire Cartesian product of domains.
    if let Some(result) = try_inverse_membership(ctx, target, body, bounds, span)? {
        return Ok(result);
    }

    // Fallback: iterate domain elements and short-circuit on first match.
    let mut local_ctx = ctx.clone();
    check_set_builder_membership_rec(&mut local_ctx, target, body, bounds, span)
}

/// Try inverse membership checking for known invertible SetBuilder patterns.
///
/// Returns `Some(bool)` if the pattern was recognized and checked, `None` if
/// the body expression is not invertible and the caller should fall back to
/// iterate-and-check.
///
/// Part of #3979.
fn try_inverse_membership(
    ctx: &EvalCtx,
    target: &Value,
    body: &Spanned<Expr>,
    bounds: &[tla_core::ast::BoundVar],
    span: Option<Span>,
) -> EvalResult<Option<bool>> {
    // Pattern 1: Identity mapping — {x : x \in S}
    // Single bound variable, body is just the bound variable.
    if bounds.len() == 1 {
        if let Expr::Ident(name, _) = &body.node {
            if name == &bounds[0].name.node {
                let domain = bounds[0].domain.as_ref().ok_or_else(|| EvalError::Internal {
                    message: "SetBuilder requires bounded variables".into(),
                    span,
                })?;
                return Ok(Some(eval_membership_lazy(ctx, target, domain)?));
            }
        }
    }

    // Pattern 2: Tuple construction with 1:1 variable-to-component mapping
    // {<<x, y, ...>> : x \in S, y \in T, ...}
    // Each tuple component is a single bound variable reference (distinct).
    if let Expr::Tuple(components) = &body.node {
        if let Some(result) = try_inverse_tuple_membership(ctx, target, components, bounds, span)? {
            return Ok(Some(result));
        }
    }

    // Pattern 3: Record construction with 1:1 variable-to-field mapping
    // {[f1 |-> x, f2 |-> y, ...] : x \in S, y \in T, ...}
    // Each field value is a single bound variable reference (distinct).
    if let Expr::Record(fields) = &body.node {
        if let Some(result) = try_inverse_record_membership(ctx, target, fields, bounds, span)? {
            return Ok(Some(result));
        }
    }

    Ok(None)
}

/// Inverse membership for tuple-valued SetBuilder:
/// `target \in {<<x, y, ...>> : x \in S, y \in T, ...}`
///
/// If the target is a tuple of the right length and each component in the body
/// is a distinct bound variable, decompose the target and check each component
/// against the corresponding domain. O(k) instead of O(|S|*|T|*...).
///
/// Returns `None` if the pattern doesn't match (components aren't simple variable refs,
/// or variables aren't 1:1 with bounds).
fn try_inverse_tuple_membership(
    ctx: &EvalCtx,
    target: &Value,
    components: &[Spanned<Expr>],
    bounds: &[tla_core::ast::BoundVar],
    span: Option<Span>,
) -> EvalResult<Option<bool>> {
    // Must have same number of components as bound variables
    if components.len() != bounds.len() {
        return Ok(None);
    }

    // Each component must be a simple Ident referencing a distinct bound variable
    let mut var_to_bound_idx: Vec<usize> = Vec::with_capacity(components.len());
    let mut used_bounds = vec![false; bounds.len()];

    for component in components.iter() {
        let Expr::Ident(name, _) = &component.node else {
            return Ok(None); // Component is not a simple variable ref
        };
        // Find which bound variable this references
        let Some(idx) = bounds.iter().position(|b| &b.name.node == name) else {
            return Ok(None); // References something that isn't a bound variable
        };
        if used_bounds[idx] {
            return Ok(None); // Same bound variable used twice (not 1:1)
        }
        used_bounds[idx] = true;
        var_to_bound_idx.push(idx);
    }

    // All bounds must be used
    if used_bounds.iter().any(|&u| !u) {
        return Ok(None);
    }

    // Pattern matched. Decompose target and check each component.
    let target_elems = match target.to_tuple_like_elements() {
        Some(elems) => elems,
        None => return Ok(Some(false)), // Target is not a tuple — can't be in the set
    };

    if target_elems.len() != components.len() {
        return Ok(Some(false)); // Wrong tuple length
    }

    // Check each target component against the corresponding bound variable's domain.
    for (comp_idx, &bound_idx) in var_to_bound_idx.iter().enumerate() {
        let domain = bounds[bound_idx].domain.as_ref().ok_or_else(|| EvalError::Internal {
            message: "SetBuilder requires bounded variables".into(),
            span,
        })?;
        if !eval_membership_lazy(ctx, &target_elems[comp_idx], domain)? {
            return Ok(Some(false));
        }
    }

    Ok(Some(true))
}

/// Inverse membership for record-valued SetBuilder:
/// `target \in {[f1 |-> x, f2 |-> y, ...] : x \in S, y \in T, ...}`
///
/// If the target is a record with the right fields and each field value in the body
/// is a distinct bound variable, decompose the target and check each field value
/// against the corresponding domain. O(k) instead of O(|S|*|T|*...).
///
/// Returns `None` if the pattern doesn't match.
fn try_inverse_record_membership(
    ctx: &EvalCtx,
    target: &Value,
    fields: &[(Spanned<String>, Spanned<Expr>)],
    bounds: &[tla_core::ast::BoundVar],
    span: Option<Span>,
) -> EvalResult<Option<bool>> {
    // Must have same number of fields as bound variables
    if fields.len() != bounds.len() {
        return Ok(None);
    }

    // Each field value must be a simple Ident referencing a distinct bound variable
    let mut field_to_bound_idx: Vec<usize> = Vec::with_capacity(fields.len());
    let mut used_bounds = vec![false; bounds.len()];

    for (_field_name, field_expr) in fields.iter() {
        let Expr::Ident(name, _) = &field_expr.node else {
            return Ok(None); // Field value is not a simple variable ref
        };
        let Some(idx) = bounds.iter().position(|b| &b.name.node == name) else {
            return Ok(None); // References something that isn't a bound variable
        };
        if used_bounds[idx] {
            return Ok(None); // Same bound variable used twice
        }
        used_bounds[idx] = true;
        field_to_bound_idx.push(idx);
    }

    // All bounds must be used
    if used_bounds.iter().any(|&u| !u) {
        return Ok(None);
    }

    // Pattern matched. Decompose target record and check each field.
    let Value::Record(rec) = target else {
        return Ok(Some(false)); // Target is not a record
    };

    if rec.len() != fields.len() {
        return Ok(Some(false)); // Wrong number of fields
    }

    // Check each field value against the corresponding bound variable's domain.
    for (field_idx, (field_name, _field_expr)) in fields.iter().enumerate() {
        let bound_idx = field_to_bound_idx[field_idx];
        let Some(field_val) = rec.get(field_name.node.as_str()) else {
            return Ok(Some(false)); // Record doesn't have this field
        };
        let domain = bounds[bound_idx].domain.as_ref().ok_or_else(|| EvalError::Internal {
            message: "SetBuilder requires bounded variables".into(),
            span,
        })?;
        if !eval_membership_lazy(ctx, field_val, domain)? {
            return Ok(Some(false));
        }
    }

    Ok(Some(true))
}

/// Recursive helper: iterate first bound variable's domain, bind each element,
/// and recurse on remaining bounds. When all bounds are bound, evaluate the
/// mapping expression and compare to target.
fn check_set_builder_membership_rec(
    ctx: &mut EvalCtx,
    target: &Value,
    body: &Spanned<Expr>,
    bounds: &[tla_core::ast::BoundVar],
    span: Option<Span>,
) -> EvalResult<bool> {
    if bounds.is_empty() {
        let mapped = eval(ctx, body)?;
        return Ok(mapped == *target);
    }

    let first = &bounds[0];
    let domain = first.domain.as_ref().ok_or_else(|| EvalError::Internal {
        message: "SetBuilder requires bounded variables".into(),
        span,
    })?;

    let dv = eval(ctx, domain)?;
    let mark = ctx.mark_stack();

    for elem in eval_iter_set(ctx, &dv, Some(domain.span))? {
        push_bound_var_mut(ctx, first, &elem, span)?;
        if check_set_builder_membership_rec(ctx, target, body, &bounds[1..], span)? {
            ctx.pop_to_mark(&mark);
            return Ok(true); // Short-circuit: found a match
        }
        ctx.pop_to_mark(&mark);
    }

    Ok(false)
}
