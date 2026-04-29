// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TIR expression dispatch — `eval_tir()` entry point.
//!
//! Evaluates the current non-temporal `TirExpr` surface using the existing
//! `EvalCtx` runtime and value-layer helpers.
//!
//! Helper routines still reject a few semantic cases explicitly:
//! - module-qualified `OperatorRef` values if lowering failed to inline the
//!   module path first
//! - `ActionSubscript`, `Always`, `Eventually`, `LeadsTo`, `WeakFair`,
//!   `StrongFair`, `Enabled` — temporal operators consumed by the liveness
//!   checker, not the expression evaluator

mod name;
mod prime;
mod scalar;

use crate::cache::{
    is_dep_tracking_active, is_tir_hoist_cacheable, tir_hoist_lookup_ctx, tir_hoist_store_ctx,
};
use crate::core::EvalCtx;
use tla_core::Spanned;
use tla_tir::nodes::TirExpr;
use tla_value::error::{EvalError, EvalResult};
use tla_value::Value;

use super::{dispatch_bindings, dispatch_functions, dispatch_structured, dispatch_values};

use self::name::eval_tir_name;
use self::prime::eval_tir_prime;
use self::scalar::{eval_tir_arith, eval_tir_bool, eval_tir_cmp, eval_tir_neg};

/// Evaluate a TIR expression in the given context.
///
/// This is the TIR-side analog of `eval()` from `eval_dispatch.rs`. It is the
/// current entry point for expression evaluation over `TirExpr` nodes and
/// recursively evaluates sub-expressions without an AST fallback.
///
/// Unsupported TIR nodes return `EvalError::Internal`.
#[inline(always)]
pub fn eval_tir(ctx: &EvalCtx, expr: &Spanned<TirExpr>) -> EvalResult<Value> {
    // Part of #3962: Sync hoist_active, hoist_state_generation, and in_enabled_scope
    // shadows from TLS every 64 evals (piggyback on the stacker counter). Matches
    // the AST eval() sync pattern. Avoids per-eval TLS lookups in eval_tir_expr.
    if ctx.should_check_stack() {
        ctx.runtime_state
            .hoist_active
            .set(crate::cache::is_hoist_active());
        ctx.runtime_state
            .hoist_state_generation
            .set(crate::cache::quantifier_hoist::hoist_state_generation_tls());
        ctx.runtime_state
            .in_enabled_scope
            .set(crate::cache::lifecycle::in_enabled_scope());
    }
    eval_tir_expr(ctx, &expr.node, Some(expr.span))
}

#[inline(always)]
fn eval_tir_expr(ctx: &EvalCtx, expr: &TirExpr, span: Option<tla_core::Span>) -> EvalResult<Value> {
    // Part of #3392: TIR hoist cache — mirrors eval_expr hoist path.
    // Use runtime_state shadow (synced every 64 evals) instead of TLS lookup.
    let hoist_allowed = ctx.runtime_state.hoist_active.get()
        && is_tir_hoist_cacheable(expr)
        && !is_dep_tracking_active(ctx);
    if hoist_allowed {
        let key = expr as *const TirExpr as usize;
        if let Some(cached) = tir_hoist_lookup_ctx(ctx, key) {
            return Ok(cached);
        }
    }

    let result = match expr {
        // --- Step 1: Core arithmetic, boolean, comparison, control ---
        TirExpr::Const { value, .. } => Ok(value.clone()),
        TirExpr::Name(name_ref) => eval_tir_name(ctx, name_ref, span),
        TirExpr::ArithBinOp { left, op, right } => eval_tir_arith(ctx, left, *op, right, span),
        TirExpr::ArithNeg(inner) => eval_tir_neg(ctx, inner, span),
        TirExpr::BoolBinOp { left, op, right } => eval_tir_bool(ctx, left, *op, right, span),
        TirExpr::BoolNot(inner) => {
            let v = eval_tir(ctx, inner)?;
            match v {
                Value::Bool(b) => Ok(Value::Bool(!b)),
                _ => Err(EvalError::type_error("BOOLEAN", &v, span)),
            }
        }
        TirExpr::Cmp { left, op, right } => eval_tir_cmp(ctx, left, *op, right, span),
        TirExpr::If { cond, then_, else_ } => {
            let cv = eval_tir(ctx, cond)?;
            match cv {
                Value::Bool(true) => eval_tir(ctx, then_),
                Value::Bool(false) => eval_tir(ctx, else_),
                _ => Err(EvalError::type_error("BOOLEAN", &cv, span)),
            }
        }
        TirExpr::Prime(inner) => eval_tir_prime(ctx, inner, span),
        TirExpr::Label { body, .. } => eval_tir(ctx, body),

        // --- Step 2 subset: self-contained structured-value arms ---
        TirExpr::Record(fields) => dispatch_structured::eval_tir_record(ctx, fields),
        TirExpr::RecordAccess { record, field } => {
            dispatch_structured::eval_tir_record_access(ctx, record, field, span)
        }
        TirExpr::SetEnum(elems) => dispatch_structured::eval_tir_set_enum(ctx, elems),
        TirExpr::SetBinOp { left, op, right } => {
            dispatch_structured::eval_tir_set_bin(ctx, left, *op, right, span)
        }
        TirExpr::Range { lo, hi } => dispatch_structured::eval_tir_range(ctx, lo, hi),
        TirExpr::Tuple(elems) => dispatch_structured::eval_tir_tuple(ctx, elems),
        TirExpr::Times(factors) => dispatch_structured::eval_tir_times(ctx, factors),

        // --- Step 3: Value-level operations (dispatch_values.rs) ---
        TirExpr::In { elem, set } => dispatch_values::eval_tir_in(ctx, elem, set, span),
        TirExpr::Subseteq { left, right } => {
            dispatch_values::eval_tir_subseteq(ctx, left, right, span)
        }
        TirExpr::Powerset(inner) => dispatch_values::eval_tir_powerset(ctx, inner, span),
        TirExpr::BigUnion(inner) => dispatch_values::eval_tir_big_union(ctx, inner, span),
        TirExpr::KSubset { base, k } => dispatch_values::eval_tir_ksubset(ctx, base, k, span),
        TirExpr::RecordSet(fields) => dispatch_values::eval_tir_record_set(ctx, fields),
        TirExpr::Case { arms, other } => {
            dispatch_values::eval_tir_case(ctx, arms, other.as_deref(), span)
        }
        TirExpr::Unchanged(inner) => dispatch_values::eval_tir_unchanged(ctx, inner, span),
        TirExpr::Forall { vars, body } => dispatch_bindings::eval_tir_forall(ctx, vars, body, span),
        TirExpr::Exists { vars, body } => dispatch_bindings::eval_tir_exists(ctx, vars, body, span),
        TirExpr::Choose { var, body } => dispatch_bindings::eval_tir_choose(ctx, var, body, span),
        TirExpr::SetFilter { var, body } => {
            dispatch_bindings::eval_tir_set_filter(ctx, var, body, span)
        }
        TirExpr::SetBuilder { body, vars } => {
            dispatch_bindings::eval_tir_set_builder(ctx, body, vars, span)
        }
        TirExpr::FuncDef { vars, body } => {
            dispatch_bindings::eval_tir_func_def(ctx, vars, body, span)
        }
        TirExpr::Let { defs, body } => dispatch_values::eval_tir_let(ctx, defs, body, span),
        TirExpr::Except { base, specs } => {
            dispatch_functions::eval_tir_except(ctx, base, specs, span)
        }
        TirExpr::ExceptAt => dispatch_functions::eval_tir_except_at(ctx, span),
        TirExpr::FuncApply { func, arg } => {
            dispatch_functions::eval_tir_func_apply(ctx, func, arg, span)
        }
        TirExpr::FuncSet { domain, range } => {
            dispatch_functions::eval_tir_func_set(ctx, domain, range)
        }
        TirExpr::Domain(inner) => dispatch_functions::eval_tir_domain(ctx, inner, span),
        TirExpr::Apply { op, args } => dispatch_functions::eval_tir_apply(ctx, op, args, span),
        TirExpr::OpRef(name) => dispatch_functions::eval_tir_op_ref(ctx, name, span),

        // --- Step 5: Remaining non-temporal variants ---
        TirExpr::OperatorRef(op_ref) => {
            dispatch_functions::eval_tir_operator_ref(ctx, op_ref, span)
        }
        TirExpr::Lambda {
            params,
            body,
            ast_body,
        } => dispatch_functions::eval_tir_lambda(ctx, params, body, ast_body, span),

        // --- Temporal operators: consumed by liveness checker, not evaluable ---
        TirExpr::ActionSubscript { .. }
        | TirExpr::Always(_)
        | TirExpr::Eventually(_)
        | TirExpr::LeadsTo { .. }
        | TirExpr::WeakFair { .. }
        | TirExpr::StrongFair { .. }
        | TirExpr::Enabled(_) => Err(EvalError::Internal {
            message: format!(
                "TIR eval: temporal operator '{}' cannot be evaluated as an expression",
                dispatch_structured::tir_expr_kind(expr)
            ),
            span,
        }),
    };

    // Part of #3392: Store result in TIR hoist cache on success.
    // Part of #3962: Use ctx-aware variant to read hoist_state_generation
    // from EvalRuntimeState shadow instead of TLS.
    if hoist_allowed {
        if let Ok(ref value) = result {
            let key = expr as *const TirExpr as usize;
            tir_hoist_store_ctx(ctx, key, value);
        }
    }

    result
}
