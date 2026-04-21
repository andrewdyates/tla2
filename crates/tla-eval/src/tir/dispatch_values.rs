// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TIR dispatch — Step 3 value-level operations.
//!
//! Split from `dispatch_bindings.rs` to stay within the 500-line file size limit.
//! This module implements:
//! - Membership: `In`, `Subseteq`
//! - Set constructors: `Powerset`, `BigUnion`, `RecordSet`
//! - Control: `Case`, `Unchanged`

use super::dispatch::eval_tir;
use super::StoredTirBody;
use crate::core::EvalCtx;
use crate::eval_membership::check_set_pred_membership;
use crate::eval_sets::{set_contains_with_ctx, value_subseteq};
use crate::helpers::values_equal;
use num_bigint::BigInt;
use num_traits::Zero;
use std::sync::Arc;
use tla_core::{expr_mentions_name_v, Spanned};
use tla_tir::nodes::{TirCaseArm, TirExpr, TirLetDef, TirNameKind};
use tla_value::error::{EvalError, EvalResult};
use tla_value::{big_union, intern_string, SubsetValue, UnionValue, Value};

// === Membership ===

/// Evaluate set membership (`elem \in set`).
pub(super) fn eval_tir_in(
    ctx: &EvalCtx,
    elem: &Spanned<TirExpr>,
    set: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let av = eval_tir(ctx, elem)?;
    let bv = eval_tir(ctx, set)?;

    // Handle membership in infinite sets (Nat, Int, Real)
    // Use to_bigint() to avoid deref sensitivity to Box vs non-Box Int.
    if let Value::ModelValue(name) = &bv {
        return match name.as_ref() {
            "Nat" => Ok(Value::Bool(
                av.to_bigint().is_some_and(|n| n >= BigInt::zero()),
            )),
            "Int" => Ok(Value::Bool(av.to_bigint().is_some())),
            "Real" => Ok(Value::Bool(av.to_bigint().is_some())),
            _ => Err(EvalError::type_error("Set", &bv, span)),
        };
    }

    // Handle SetPred
    if let Value::SetPred(spv) = &bv {
        return Ok(Value::Bool(check_set_pred_membership(ctx, &av, spv, span)?));
    }

    // Handle concrete sets
    let contains = match bv.set_contains(&av) {
        Some(c) => c,
        None => set_contains_with_ctx(ctx, &av, &bv, span)?,
    };
    Ok(Value::Bool(contains))
}

/// Evaluate subset-or-equal (`left \subseteq right`).
pub(super) fn eval_tir_subseteq(
    ctx: &EvalCtx,
    left: &Spanned<TirExpr>,
    right: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let av = eval_tir(ctx, left)?;
    let bv = eval_tir(ctx, right)?;
    Ok(Value::Bool(value_subseteq(
        ctx,
        &av,
        &bv,
        span,
        Some(right.span),
    )?))
}

// === Set constructors ===

/// Evaluate SUBSET S (powerset).
pub(super) fn eval_tir_powerset(
    ctx: &EvalCtx,
    inner: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let av = eval_tir(ctx, inner)?;
    if !av.is_set() {
        return Err(EvalError::type_error("Set", &av, span));
    }
    Ok(Value::Subset(SubsetValue::new(av)))
}

/// Evaluate KSubset(S, k) — k-element subsets of S.
/// Constructs a lazy KSubsetValue representing C(n,k) subsets. Part of #3907.
pub(super) fn eval_tir_ksubset(
    ctx: &EvalCtx,
    base: &Spanned<TirExpr>,
    k: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let base_val = eval_tir(ctx, base)?;
    if !base_val.is_set() {
        return Err(EvalError::type_error("Set", &base_val, span));
    }
    let k_val = eval_tir(ctx, k)?;
    let k_int = k_val
        .to_bigint()
        .and_then(|n| {
            use num_traits::ToPrimitive;
            n.to_usize()
        })
        .ok_or_else(|| EvalError::type_error("non-negative integer", &k_val, span))?;
    Ok(Value::KSubset(tla_value::KSubsetValue::new(base_val, k_int)))
}

/// Evaluate UNION S (big union / generalized union).
pub(super) fn eval_tir_big_union(
    ctx: &EvalCtx,
    inner: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let av = eval_tir(ctx, inner)?;
    if !av.is_set() {
        return Err(EvalError::type_error("Set", &av, span));
    }
    // For small, fully enumerable sets, compute eagerly
    if let Some(sa) = av.to_sorted_set() {
        let mut can_eager = true;
        let mut total_size = 0usize;
        for elem in &sa {
            if let Some(len) = elem.set_len() {
                let len_usize: usize = len.try_into().unwrap_or(usize::MAX);
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
            return big_union(&sa).ok_or(EvalError::TypeError {
                expected: "Set of Sets",
                got: "Set containing non-Set",
                span,
            });
        }
    }
    Ok(Value::BigUnion(UnionValue::new(av)))
}

/// Evaluate a record set (`[a: S, b: T]`).
pub(super) fn eval_tir_record_set(
    ctx: &EvalCtx,
    fields: &[(tla_tir::nodes::TirFieldName, Spanned<TirExpr>)],
) -> EvalResult<Value> {
    let mut field_sets = Vec::with_capacity(fields.len());
    for (field, set_expr) in fields {
        let sv = eval_tir(ctx, set_expr)?;
        if !sv.is_set() {
            return Err(EvalError::type_error("Set", &sv, Some(set_expr.span)));
        }
        let interned: Arc<str> = intern_string(&field.name);
        field_sets.push((interned, sv));
    }
    Ok(Value::record_set(field_sets))
}

// === Control flow ===

/// Evaluate CASE arms.
pub(super) fn eval_tir_case(
    ctx: &EvalCtx,
    arms: &[TirCaseArm],
    other: Option<&Spanned<TirExpr>>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    for arm in arms {
        let guard = eval_tir(ctx, &arm.guard)?;
        let b = guard
            .as_bool()
            .ok_or_else(|| EvalError::type_error("BOOLEAN", &guard, Some(arm.guard.span)))?;
        if b {
            return eval_tir(ctx, &arm.body);
        }
    }
    if let Some(other) = other {
        return eval_tir(ctx, other);
    }
    Err(EvalError::CaseNoMatch { span })
}

/// Direct slot comparison for TIR UNCHANGED on a single state variable.
///
/// Part of #3073: TIR analog of `try_unchanged_statevar_fast` in eval_prime.rs.
/// When both state_env and next_state_env are array-backed and no overlays are
/// active, compare current/next slots directly without eval dispatch.
#[inline]
fn try_tir_unchanged_statevar_fast(
    ctx: &EvalCtx,
    inner: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> Option<EvalResult<Value>> {
    let state_env = ctx.state_env?;
    let next_state_env = ctx.next_state_env?;

    if !ctx.bindings.is_empty()
        || ctx.instance_substitutions().is_some()
        || ctx.eager_subst_bindings.is_some()
        || ctx.call_by_name_subs().is_some()
    {
        return None;
    }

    match &inner.node {
        TirExpr::Name(name_ref) => {
            let TirNameKind::StateVar { index } = &name_ref.kind else {
                return None;
            };
            let idx = *index as usize;
            if !crate::is_dep_tracking_active(ctx) {
                let eq = unsafe { state_env.values_equal(next_state_env, idx) };
                return Some(Ok(Value::Bool(eq)));
            }
            let cur = unsafe { state_env.get_value(idx) };
            let next = unsafe { next_state_env.get_value(idx) };
            Some(if !cur.is_set() && !next.is_set() {
                Ok(Value::Bool(cur == next))
            } else {
                values_equal(ctx, &cur, &next, span).map(Value::Bool)
            })
        }
        TirExpr::Tuple(elems) => {
            for elem in elems {
                let TirExpr::Name(name_ref) = &elem.node else {
                    return None;
                };
                let TirNameKind::StateVar { index } = &name_ref.kind else {
                    return None;
                };
                let idx = *index as usize;
                if !crate::is_dep_tracking_active(ctx) {
                    let eq = unsafe { state_env.values_equal(next_state_env, idx) };
                    if !eq {
                        return Some(Ok(Value::Bool(false)));
                    }
                    continue;
                }
                let cur = unsafe { state_env.get_value(idx) };
                let next = unsafe { next_state_env.get_value(idx) };
                let eq = if !cur.is_set() && !next.is_set() {
                    cur == next
                } else {
                    match values_equal(ctx, &cur, &next, span) {
                        Ok(eq) => eq,
                        Err(e) => return Some(Err(e)),
                    }
                };
                if !eq {
                    return Some(Ok(Value::Bool(false)));
                }
            }
            Some(Ok(Value::Bool(true)))
        }
        _ => None,
    }
}

/// Evaluate UNCHANGED expr: current-state value == next-state value.
pub(super) fn eval_tir_unchanged(
    ctx: &EvalCtx,
    inner: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    // Part of #3073: Direct slot comparison fast path for StateVar / Tuple-of-StateVar.
    if let Some(result) = try_tir_unchanged_statevar_fast(ctx, inner, span) {
        return result;
    }

    // Evaluate in current-state environment
    let cur_v = eval_tir(ctx, inner)?;

    // Build next-state context by swapping state_env with next_state_env
    if let Some(next_state_env) = ctx.next_state_env {
        let mut next_ctx = ctx.clone();
        let s = next_ctx.stable_mut();
        s.next_state = None;
        s.next_state_env = None;
        s.state_env = Some(next_state_env);
        let next_v = eval_tir(&next_ctx, inner)?;
        let eq = values_equal(ctx, &cur_v, &next_v, span)?;
        return Ok(Value::Bool(eq));
    }

    let Some(next_state) = &ctx.next_state else {
        return Err(EvalError::UnchangedNotEvaluable { span });
    };

    // Fallback: rebind next-state variables as unprimed
    let mut next_ctx = ctx.clone();
    // Part of #3964: Hoist Arc::make_mut outside loops via batch_insert_into_env.
    // Previously each iteration called Rc::make_mut + Arc::make_mut separately,
    // triggering N redundant refcount checks (N = state var count).
    if next_ctx.state_env.is_some() {
        let is_full = next_state.len() == ctx.var_registry().len();
        if is_full {
            next_ctx.stable_mut().state_env = None;
            next_ctx.batch_insert_into_env(next_state.iter());
        } else {
            for (name, value) in next_state.iter() {
                if !next_ctx.has_local_binding(name.as_ref()) {
                    let interned = intern_string(name.as_ref());
                    let name_id = tla_core::name_intern::intern_name(interned.as_ref());
                    next_ctx.push_binding_preinterned(interned, value.clone(), name_id);
                }
            }
        }
    } else {
        next_ctx.batch_insert_into_env(next_state.iter());
    }
    let next_v = eval_tir(&next_ctx, inner)?;
    let eq = values_equal(ctx, &cur_v, &next_v, span)?;
    Ok(Value::Bool(eq))
}

// === Let binding ===

/// Evaluate LET defs IN body.
///
/// Zero-arg defs are eagerly evaluated and bound. Parameterized defs are
/// normally lowered to LAMBDA + zero-param binding during TIR construction
/// (Part of #3262). The else-branch handles any un-lowered parameterized defs
/// by creating a closure with a TIR body at evaluation time.
pub(super) fn eval_tir_let(
    ctx: &EvalCtx,
    defs: &[TirLetDef],
    body: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let _ = span;
    let mut local_ctx = ctx.clone();
    let mark = local_ctx.mark_stack();

    for def in defs {
        if def.params.is_empty() {
            let interned: Arc<str> = intern_string(&def.name);
            let mut val = eval_tir(&local_ctx, &def.body)?;
            if let (Value::Closure(closure), true) =
                (&mut val, lambda_body_recurses_on_name(&def.body, &def.name))
            {
                *closure = Arc::new(
                    closure
                        .as_ref()
                        .clone()
                        .with_name_if_missing(Arc::clone(&interned)),
                );
            }
            local_ctx.push_binding_preinterned(interned, val, def.name_id);
        } else {
            // Parameterized LET defs are normally lowered to LAMBDA + zero-param
            // binding by the TIR lowerer. This branch handles the case robustly
            // by creating a closure with a TIR body at evaluation time.
            let dummy_ast_body = Spanned {
                node: tla_core::ast::Expr::Bool(true),
                span: def.body.span,
            };
            let closure = local_ctx
                .create_closure(
                    def.params.clone(),
                    dummy_ast_body,
                    local_ctx.local_ops().clone(),
                )
                .with_tir_body(Box::new(StoredTirBody::new(def.body.clone())));
            let interned: Arc<str> = intern_string(&def.name);
            local_ctx.push_binding_preinterned(
                interned,
                Value::Closure(Arc::new(closure)),
                def.name_id,
            );
        }
    }

    let result = eval_tir(&local_ctx, body)?;
    local_ctx.pop_to_mark(&mark);
    Ok(result)
}

fn lambda_body_recurses_on_name(expr: &Spanned<TirExpr>, name: &str) -> bool {
    match &expr.node {
        TirExpr::Lambda { ast_body, .. } => expr_mentions_name_v(&ast_body.0.node, name),
        _ => false,
    }
}
