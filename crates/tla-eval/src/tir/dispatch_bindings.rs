// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TIR dispatch — Step 3: Quantifiers, comprehensions, and function defs.
//!
//! Binding-heavy dispatch functions that use the `EvalCtx` binding stack
//! for scoped variable bindings with TIR-native `push_binding_preinterned`.

use super::dispatch::eval_tir;
use crate::cache::{enter_tir_hoist_scope, enter_tir_hoist_scope_single};
use crate::core::EvalCtx;
use crate::helpers::{
    eval_choose_single, eval_quantifier_single, is_simple_tir_bound, push_tir_bound_var,
};
use num_traits::ToPrimitive;
use tla_core::Spanned;
use tla_tir::nodes::{TirBoundVar, TirCmpOp, TirExpr};
use tla_value::error::{EvalError, EvalResult};
use tla_value::{KSubsetValue, SetBuilder, Value};

/// Evaluate the domain expression of a TIR bound variable.
fn eval_tir_bound_domain(
    ctx: &EvalCtx,
    var: &TirBoundVar,
    kind: &str,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let domain = var.domain.as_ref().ok_or_else(|| EvalError::Internal {
        message: format!("{kind} requires bounded quantification"),
        span,
    })?;
    eval_tir(ctx, domain)
}

// === Quantifiers ===
/// Evaluate \A vars : body
pub(super) fn eval_tir_forall(
    ctx: &EvalCtx,
    vars: &[TirBoundVar],
    body: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    if vars.is_empty() {
        return eval_tir(ctx, body);
    }

    let mut local_ctx = ctx.clone();
    eval_tir_forall_inner(&mut local_ctx, vars, body, span)
}

fn eval_tir_forall_inner(
    ctx: &mut EvalCtx,
    vars: &[TirBoundVar],
    body: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    if vars.is_empty() {
        return eval_tir(ctx, body);
    }

    let dv = eval_tir_bound_domain(ctx, &vars[0], "Forall", span)?;
    let _hoist_guard = enter_tir_hoist_scope(body, vars);
    eval_quantifier_single(
        ctx,
        &vars[0],
        &dv,
        &mut |local_ctx| eval_tir_forall_inner(local_ctx, &vars[1..], body, span),
        Some(body.span),
        span,
        false,
    )
}

/// Evaluate \E vars : body
pub(super) fn eval_tir_exists(
    ctx: &EvalCtx,
    vars: &[TirBoundVar],
    body: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    if vars.is_empty() {
        return eval_tir(ctx, body);
    }

    let mut local_ctx = ctx.clone();
    eval_tir_exists_inner(&mut local_ctx, vars, body, span)
}

fn eval_tir_exists_inner(
    ctx: &mut EvalCtx,
    vars: &[TirBoundVar],
    body: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    if vars.is_empty() {
        return eval_tir(ctx, body);
    }

    let dv = eval_tir_bound_domain(ctx, &vars[0], "Exists", span)?;
    let _hoist_guard = enter_tir_hoist_scope(body, vars);
    eval_quantifier_single(
        ctx,
        &vars[0],
        &dv,
        &mut |local_ctx| eval_tir_exists_inner(local_ctx, &vars[1..], body, span),
        Some(body.span),
        span,
        true,
    )
}

/// Evaluate CHOOSE var \in S : body
///
/// Per-state CHOOSE memoization (two tiers):
/// - Tier 1 (shallow): `binding_depth == 0` — cache by (expr_ptr, instance_subs_id).
/// - Tier 2 (deep, Part of #3905): `binding_depth > 0` — cache by
///   (expr_ptr, instance_subs_id, domain_hash, bindings_hash).
///
/// Both tiers cleared at every state boundary by `clear_state_boundary_core_impl`.
pub(super) fn eval_tir_choose(
    ctx: &EvalCtx,
    var: &TirBoundVar,
    body: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let expr_ptr = body as *const Spanned<TirExpr> as usize;
    let instance_subs_id = crate::cache::scope_ids::resolve_instance_subs_id(
        ctx.scope_ids.instance_substitutions,
        &ctx.instance_substitutions,
    );
    let state_identity = ctx.state_env.map_or(0, |s| s.identity());

    // Tier 1 (shallow): binding_depth == 0 — check existing cache.
    let shallow_cacheable = ctx.binding_depth == 0;
    if shallow_cacheable {
        if let Some(cached) =
            crate::cache::choose_cache_lookup(expr_ptr, instance_subs_id, state_identity)
        {
            return Ok(cached);
        }
    }

    let dv = eval_tir_bound_domain(ctx, var, "Choose", span)?;

    // Fast path for CHOOSE x \in S : TRUE
    if let TirExpr::Const {
        value: Value::Bool(true),
        ..
    } = &body.node
    {
        // Part of #3905: For CHOOSE TRUE at any depth, check deep cache with bindings_hash=0.
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
            let result = dv
                .tlc_first_element()?
                .ok_or(EvalError::ChooseFailed { span })?;
            crate::cache::choose_deep_cache_store(deep_key, result.clone());
            return Ok(result);
        }
        let result = dv
            .tlc_first_element()?
            .ok_or(EvalError::ChooseFailed { span })?;
        crate::cache::choose_cache_store(expr_ptr, instance_subs_id, state_identity, result.clone());
        return Ok(result);
    }

    // Part of #3905: Tier 2 (deep) cache for general CHOOSE at binding_depth > 0.
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

    let mut local_ctx = ctx.clone();
    let _hoist_guard = enter_tir_hoist_scope_single(body, var);
    let result = eval_choose_single(
        &mut local_ctx,
        var,
        &dv,
        &mut |eval_ctx| eval_tir(eval_ctx, body),
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

// === Comprehensions ===
/// Evaluate {var \in S : body} (set filter).
pub(super) fn eval_tir_set_filter(
    ctx: &EvalCtx,
    var: &TirBoundVar,
    body: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let dv = eval_tir_bound_domain(ctx, var, "SetFilter", span)?;
    let domain_span = var.domain.as_ref().map(|d| d.span);

    if !dv.is_set() {
        return Err(EvalError::type_error("Set", &dv, domain_span));
    }

    // K-subset optimization: detect {x \in SUBSET S : Cardinality(x) = k} and replace
    // the 2^n powerset+filter with direct C(n,k) k-subset generation.
    if let Value::Subset(ref sv) = dv {
        if let Some(k) = try_extract_tir_cardinality_eq_k(ctx, var, body)? {
            let base = sv.base().clone();
            return Ok(Value::KSubset(KSubsetValue::new(base, k)));
        }
    }

    let iter = dv
        .iter_set()
        .ok_or_else(|| EvalError::type_error("Set", &dv, domain_span))?;

    let mut local_ctx = ctx.clone();
    let mark = local_ctx.mark_stack();
    let mut result = SetBuilder::new();
    let _hoist_guard = enter_tir_hoist_scope_single(body, var);

    if is_simple_tir_bound(var) {
        let mut first_iter = true;
        for elem in iter {
            if first_iter {
                push_tir_bound_var(&mut local_ctx, var, &elem, span)?;
                first_iter = false;
            } else {
                local_ctx.update_last_binding_value(elem.clone());
            }
            let pv = eval_tir(&local_ctx, body)?;
            let include = pv
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", &pv, Some(body.span)))?;
            if include {
                result.insert(elem);
            }
        }
        local_ctx.pop_to_mark(&mark);
    } else {
        for elem in iter {
            push_tir_bound_var(&mut local_ctx, var, &elem, span)?;
            let pv = eval_tir(&local_ctx, body)?;
            local_ctx.pop_to_mark(&mark);
            let include = pv
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", &pv, Some(body.span)))?;
            if include {
                result.insert(elem);
            }
        }
    }

    Ok(result.build_value())
}

/// Evaluate {body : vars} (set builder / set map).
pub(super) fn eval_tir_set_builder(
    ctx: &EvalCtx,
    body: &Spanned<TirExpr>,
    vars: &[TirBoundVar],
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let mut result = Vec::new();
    let mut local_ctx = ctx.clone();
    eval_tir_set_builder_rec(&mut local_ctx, body, vars, &mut result, span)?;
    Ok(Value::set(result))
}

fn eval_tir_set_builder_rec(
    ctx: &mut EvalCtx,
    body: &Spanned<TirExpr>,
    vars: &[TirBoundVar],
    result: &mut Vec<Value>,
    span: Option<tla_core::Span>,
) -> EvalResult<()> {
    if vars.is_empty() {
        result.push(eval_tir(ctx, body)?);
        return Ok(());
    }

    let first = &vars[0];
    let dv = eval_tir_bound_domain(ctx, first, "SetBuilder", span)?;
    let domain_span = first.domain.as_ref().map(|d| d.span);

    let mark = ctx.mark_stack();
    let iter = dv
        .iter_set()
        .ok_or_else(|| EvalError::type_error("Set", &dv, domain_span))?;
    let _hoist_guard = enter_tir_hoist_scope(body, vars);

    if is_simple_tir_bound(first) {
        let mut first_iter = true;
        for elem in iter {
            if first_iter {
                push_tir_bound_var(ctx, first, &elem, span)?;
                first_iter = false;
            } else {
                ctx.update_last_binding_value(elem.clone());
            }
            eval_tir_set_builder_rec(ctx, body, &vars[1..], result, span)?;
        }
        ctx.pop_to_mark(&mark);
    } else {
        for elem in iter {
            push_tir_bound_var(ctx, first, &elem, span)?;
            eval_tir_set_builder_rec(ctx, body, &vars[1..], result, span)?;
            ctx.pop_to_mark(&mark);
        }
    }

    Ok(())
}

/// Evaluate [vars |-> body] (function definition).
/// For finite, enumerable domains, eagerly evaluates the function.
pub(super) fn eval_tir_func_def(
    ctx: &EvalCtx,
    vars: &[TirBoundVar],
    body: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    if vars.len() == 1 {
        let var = &vars[0];
        let dv = eval_tir_bound_domain(ctx, var, "FuncDef", span)?;
        let domain_span = var.domain.as_ref().map(|d| d.span);
        let _hoist_guard = enter_tir_hoist_scope_single(body, var);

        // For intervals, use IntIntervalFunc/Seq for efficiency
        if let Value::Interval(intv) = &dv {
            if let (Some(min), Some(max)) = (intv.low().to_i64(), intv.high().to_i64()) {
                use crate::helpers::interval_len_for_bounds_check;
                let size = interval_len_for_bounds_check(min, max);
                if size <= 1_000_000 {
                    let mut local_ctx = ctx.clone();
                    let mark = local_ctx.mark_stack();
                    let mut values = Vec::with_capacity(size);
                    let mut first_iter = true;
                    for i in min..=max {
                        let elem = Value::SmallInt(i);
                        if first_iter {
                            push_tir_bound_var(&mut local_ctx, var, &elem, span)?;
                            first_iter = false;
                        } else {
                            local_ctx.update_last_binding_value(elem);
                        }
                        values.push(eval_tir(&local_ctx, body)?);
                    }
                    local_ctx.pop_to_mark(&mark);
                    // 1..n → Seq, otherwise IntIntervalFunc
                    if min == 1 {
                        return Ok(Value::Seq(tla_value::SeqValue::from_vec(values).into()));
                    }
                    return Ok(Value::IntFunc(
                        tla_value::IntIntervalFunc::new(min, max, values).into(),
                    ));
                }
            }
        }

        // For finite, enumerable sets, build FuncValue eagerly
        let iter = dv
            .iter_set()
            .ok_or_else(|| EvalError::type_error("Set", &dv, domain_span))?;

        let mut local_ctx = ctx.clone();
        let mark = local_ctx.mark_stack();
        let mut builder = tla_value::FuncBuilder::new();

        if is_simple_tir_bound(var) {
            let mut first_iter = true;
            for elem in iter {
                if first_iter {
                    push_tir_bound_var(&mut local_ctx, var, &elem, span)?;
                    first_iter = false;
                } else {
                    local_ctx.update_last_binding_value(elem.clone());
                }
                let val = eval_tir(&local_ctx, body)?;
                builder.insert(elem, val);
            }
            local_ctx.pop_to_mark(&mark);
        } else {
            for elem in iter {
                push_tir_bound_var(&mut local_ctx, var, &elem, span)?;
                let val = eval_tir(&local_ctx, body)?;
                local_ctx.pop_to_mark(&mark);
                builder.insert(elem, val);
            }
        }

        return Ok(Value::Func(builder.build().into()));
    }

    // Multi-variable function definition: [x \in S, y \in T |-> e]
    // Domain is S \X T, keys are tuples <<x, y>>.
    let mut domains = Vec::with_capacity(vars.len());
    for var in vars {
        let dv = eval_tir_bound_domain(ctx, var, "FuncDef", span)?;
        domains.push(dv);
    }

    // Eagerly evaluate via nested iteration, accumulating tuple key components
    let mut local_ctx = ctx.clone();
    let mut builder = tla_value::FuncBuilder::new();
    let mut key_components = Vec::with_capacity(vars.len());
    eval_tir_func_def_rec(
        &mut local_ctx,
        vars,
        &domains,
        body,
        &mut builder,
        &mut key_components,
        span,
    )?;
    Ok(Value::Func(builder.build().into()))
}

fn eval_tir_func_def_rec(
    ctx: &mut EvalCtx,
    vars: &[TirBoundVar],
    domains: &[Value],
    body: &Spanned<TirExpr>,
    builder: &mut tla_value::FuncBuilder,
    key_components: &mut Vec<Value>,
    span: Option<tla_core::Span>,
) -> EvalResult<()> {
    if vars.is_empty() {
        return Ok(());
    }

    let var = &vars[0];
    let dv = &domains[0];
    let domain_span = var.domain.as_ref().map(|d| d.span);
    let iter = dv
        .iter_set()
        .ok_or_else(|| EvalError::type_error("Set", dv, domain_span))?;
    let mark = ctx.mark_stack();
    let _hoist_guard = enter_tir_hoist_scope(body, vars);

    if vars.len() == 1 {
        // Base case: evaluate body and insert with tuple key
        for elem in iter {
            push_tir_bound_var(ctx, var, &elem, span)?;
            let val = eval_tir(ctx, body)?;
            ctx.pop_to_mark(&mark);
            key_components.push(elem);
            let key = Value::Tuple(key_components.as_slice().into());
            builder.insert(key, val);
            key_components.pop();
        }
    } else {
        // Recurse: bind this variable, recurse on remaining
        for elem in iter {
            key_components.push(elem.clone());
            push_tir_bound_var(ctx, var, &elem, span)?;
            eval_tir_func_def_rec(
                ctx,
                &vars[1..],
                &domains[1..],
                body,
                builder,
                key_components,
                span,
            )?;
            ctx.pop_to_mark(&mark);
            key_components.pop();
        }
    }
    Ok(())
}

/// Detect the pattern `Cardinality(x) = k` (or reversed) in a TIR SetFilter body,
/// where `x` is the bound variable. Returns `Some(k)` if matched.
///
/// Enables k-subset optimization: `{x \in SUBSET S : Cardinality(x) = k}` generates
/// C(n,k) subsets directly instead of 2^n powerset + filter.
fn try_extract_tir_cardinality_eq_k(
    ctx: &EvalCtx,
    var: &TirBoundVar,
    body: &Spanned<TirExpr>,
) -> EvalResult<Option<usize>> {
    let bound_name = &var.name;

    // Match Cmp { op: Eq, left, right }
    let (left, right) = match &body.node {
        TirExpr::Cmp {
            left,
            op: TirCmpOp::Eq,
            right,
        } => (left.as_ref(), right.as_ref()),
        _ => return Ok(None),
    };

    // Try both orientations
    if let Some(k) = try_match_tir_cardinality_eq(ctx, bound_name, left, right)? {
        return Ok(Some(k));
    }
    if let Some(k) = try_match_tir_cardinality_eq(ctx, bound_name, right, left)? {
        return Ok(Some(k));
    }

    Ok(None)
}

/// Check if `card_side` is `Apply(Name("Cardinality"), [Name(bound_name)])`
/// and `k_side` evaluates to a concrete non-negative integer.
fn try_match_tir_cardinality_eq(
    ctx: &EvalCtx,
    bound_name: &str,
    card_side: &Spanned<TirExpr>,
    k_side: &Spanned<TirExpr>,
) -> EvalResult<Option<usize>> {
    if let TirExpr::Apply { op, args } = &card_side.node {
        if args.len() != 1 {
            return Ok(None);
        }
        // The op must be Name("Cardinality")
        let is_cardinality = matches!(&op.node, TirExpr::Name(ref name_ref) if name_ref.name == "Cardinality");
        if !is_cardinality {
            return Ok(None);
        }
        // The argument must be the bound variable
        let is_bound_var = matches!(&args[0].node, TirExpr::Name(ref name_ref) if name_ref.name == bound_name);
        if !is_bound_var {
            return Ok(None);
        }
        // k_side must evaluate to a concrete non-negative integer.
        // Only attempt if k_side doesn't reference the bound variable.
        if tir_expr_references_name(&k_side.node, bound_name) {
            return Ok(None);
        }
        let k_val = eval_tir(ctx, k_side)?;
        if let Some(n) = k_val.to_bigint() {
            if let Some(k) = n.to_usize() {
                return Ok(Some(k));
            }
        }
    }
    Ok(None)
}

/// Check if a TIR expression references a given variable name.
fn tir_expr_references_name(expr: &TirExpr, name: &str) -> bool {
    match expr {
        TirExpr::Name(ref name_ref) => name_ref.name == name,
        TirExpr::Const { .. } | TirExpr::OpRef(_) => false,
        TirExpr::Apply { op, args } => {
            tir_expr_references_name(&op.node, name)
                || args.iter().any(|a| tir_expr_references_name(&a.node, name))
        }
        TirExpr::Cmp { left, right, .. } | TirExpr::ArithBinOp { left, right, .. } => {
            tir_expr_references_name(&left.node, name)
                || tir_expr_references_name(&right.node, name)
        }
        TirExpr::BoolBinOp { left, right, .. }
        | TirExpr::In { elem: left, set: right }
        | TirExpr::Subseteq { left, right }
        | TirExpr::SetBinOp { left, right, .. }
        | TirExpr::FuncSet {
            domain: left,
            range: right,
        }
        | TirExpr::FuncApply {
            func: left,
            arg: right,
        } => {
            tir_expr_references_name(&left.node, name)
                || tir_expr_references_name(&right.node, name)
        }
        TirExpr::BoolNot(inner)
        | TirExpr::ArithNeg(inner)
        | TirExpr::Powerset(inner)
        | TirExpr::BigUnion(inner)
        | TirExpr::Domain(inner)
        | TirExpr::Prime(inner) => tir_expr_references_name(&inner.node, name),
        TirExpr::KSubset { base, k } => {
            tir_expr_references_name(&base.node, name)
                || tir_expr_references_name(&k.node, name)
        }
        // Conservative: anything complex returns true
        _ => true,
    }
}
