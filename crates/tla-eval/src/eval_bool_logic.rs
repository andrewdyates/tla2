// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boolean logic operators: AND, OR, NOT, =>, <=>.
//!
//! Part of #3214: Split from eval_expr_helpers.rs.

use super::core::EvalCtx;
#[cfg(debug_assertions)]
use super::debug_or_eval;
use super::{eval, EvalError, EvalResult};
use crate::value::Value;
use tla_core::Spanned;

/// Evaluate conjunction with short-circuit semantics.
#[inline]
pub(super) fn eval_and(
    ctx: &EvalCtx,
    a: &Spanned<tla_core::ast::Expr>,
    b: &Spanned<tla_core::ast::Expr>,
) -> EvalResult<Value> {
    let av = eval(ctx, a)?;
    let ab = av
        .as_bool()
        .ok_or_else(|| EvalError::type_error("BOOLEAN", &av, Some(a.span)))?;
    if !ab {
        return Ok(Value::Bool(false));
    }
    let bv = eval(ctx, b)?;
    let bb = bv
        .as_bool()
        .ok_or_else(|| EvalError::type_error("BOOLEAN", &bv, Some(b.span)))?;
    Ok(Value::Bool(bb))
}

/// Evaluate disjunction with short-circuit semantics.
#[inline]
pub(super) fn eval_or(
    ctx: &EvalCtx,
    a: &Spanned<tla_core::ast::Expr>,
    b: &Spanned<tla_core::ast::Expr>,
) -> EvalResult<Value> {
    let av = eval(ctx, a)?;
    let ab = av
        .as_bool()
        .ok_or_else(|| EvalError::type_error("BOOLEAN", &av, Some(a.span)))?;
    debug_eprintln!(
        debug_or_eval(),
        "[OR DEBUG] LHS={}, will short-circuit={}",
        ab,
        ab
    );
    if ab {
        return Ok(Value::Bool(true));
    }
    let bv = eval(ctx, b)?;
    let bb = bv
        .as_bool()
        .ok_or_else(|| EvalError::type_error("BOOLEAN", &bv, Some(b.span)))?;
    debug_eprintln!(debug_or_eval(), "[OR DEBUG] RHS={}, result={}", bb, bb);
    Ok(Value::Bool(bb))
}

/// Evaluate logical negation.
#[inline]
pub(super) fn eval_not(ctx: &EvalCtx, a: &Spanned<tla_core::ast::Expr>) -> EvalResult<Value> {
    let av = eval(ctx, a)?;
    let ab = av
        .as_bool()
        .ok_or_else(|| EvalError::type_error("BOOLEAN", &av, Some(a.span)))?;
    Ok(Value::Bool(!ab))
}

/// Evaluate implication with short-circuit (FALSE => X is TRUE).
#[inline]
pub(super) fn eval_implies(
    ctx: &EvalCtx,
    a: &Spanned<tla_core::ast::Expr>,
    b: &Spanned<tla_core::ast::Expr>,
) -> EvalResult<Value> {
    let av = eval(ctx, a)?;
    let ab = av
        .as_bool()
        .ok_or_else(|| EvalError::type_error("BOOLEAN", &av, Some(a.span)))?;
    if !ab {
        return Ok(Value::Bool(true));
    }
    let bv = eval(ctx, b)?;
    let bb = bv
        .as_bool()
        .ok_or_else(|| EvalError::type_error("BOOLEAN", &bv, Some(b.span)))?;
    Ok(Value::Bool(bb))
}

/// Evaluate logical equivalence.
pub(super) fn eval_equiv(
    ctx: &EvalCtx,
    a: &Spanned<tla_core::ast::Expr>,
    b: &Spanned<tla_core::ast::Expr>,
) -> EvalResult<Value> {
    let av = eval(ctx, a)?;
    let ab = av
        .as_bool()
        .ok_or_else(|| EvalError::type_error("BOOLEAN", &av, Some(a.span)))?;
    let bv = eval(ctx, b)?;
    let bb = bv
        .as_bool()
        .ok_or_else(|| EvalError::type_error("BOOLEAN", &bv, Some(b.span)))?;
    Ok(Value::Bool(ab == bb))
}
