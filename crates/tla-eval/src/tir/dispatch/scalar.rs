// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TIR scalar evaluation — arithmetic, boolean, and comparison helpers.

use num_integer::Integer;
use tla_core::Spanned;
use tla_tir::nodes::{TirArithOp, TirBoolOp, TirCmpOp, TirExpr};
use tla_value::error::{EvalError, EvalResult};
use tla_value::Value;

use crate::core::EvalCtx;
use crate::eval_arith::{int_arith_op, int_cmp_op, int_div_op, int_mod_op, int_pow_op};
use crate::helpers::values_equal;

use super::eval_tir;

/// Evaluate a TIR arithmetic binary operation.
pub(super) fn eval_tir_arith(
    ctx: &EvalCtx,
    left: &Spanned<TirExpr>,
    op: TirArithOp,
    right: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let lv = eval_tir(ctx, left)?;
    let rv = eval_tir(ctx, right)?;
    match op {
        TirArithOp::Add => int_arith_op(lv, rv, i64::checked_add, |a, b| a + b, "+", span),
        TirArithOp::Sub => int_arith_op(lv, rv, i64::checked_sub, |a, b| a - b, "-", span),
        TirArithOp::Mul => int_arith_op(lv, rv, i64::checked_mul, |a, b| a * b, "*", span),
        TirArithOp::Div => int_div_op(lv, rv, i64::checked_div, |a, b| a / b, "/", span),
        TirArithOp::IntDiv => int_div_op(
            lv,
            rv,
            |a, b| {
                if a == i64::MIN && b == -1 {
                    return None;
                }
                let q = a / b;
                if (a ^ b) < 0 && a % b != 0 {
                    Some(q - 1)
                } else {
                    Some(q)
                }
            },
            |a, b| a.div_floor(&b),
            "\\div",
            span,
        ),
        TirArithOp::Mod => int_mod_op(lv, rv, span),
        TirArithOp::Pow => int_pow_op(lv, rv, span),
    }
}

/// Evaluate arithmetic negation.
pub(super) fn eval_tir_neg(
    ctx: &EvalCtx,
    inner: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let v = eval_tir(ctx, inner)?;
    match v {
        Value::SmallInt(n) => {
            if let Some(neg) = n.checked_neg() {
                Ok(Value::SmallInt(neg))
            } else {
                Ok(Value::big_int(-num_bigint::BigInt::from(n)))
            }
        }
        _ => {
            let n = v
                .to_bigint()
                .ok_or_else(|| EvalError::argument_error("first", "-.", "integer", &v, span))?;
            Ok(Value::big_int(-n))
        }
    }
}

/// Evaluate a TIR boolean binary operation with short-circuit semantics.
pub(super) fn eval_tir_bool(
    ctx: &EvalCtx,
    left: &Spanned<TirExpr>,
    op: TirBoolOp,
    right: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    match op {
        TirBoolOp::And => {
            let lv = eval_tir(ctx, left)?;
            match lv {
                Value::Bool(false) => Ok(Value::Bool(false)),
                Value::Bool(true) => eval_tir(ctx, right),
                _ => Err(EvalError::type_error("BOOLEAN", &lv, span)),
            }
        }
        TirBoolOp::Or => {
            let lv = eval_tir(ctx, left)?;
            match lv {
                Value::Bool(true) => Ok(Value::Bool(true)),
                Value::Bool(false) => eval_tir(ctx, right),
                _ => Err(EvalError::type_error("BOOLEAN", &lv, span)),
            }
        }
        TirBoolOp::Implies => {
            let lv = eval_tir(ctx, left)?;
            match lv {
                Value::Bool(false) => Ok(Value::Bool(true)),
                Value::Bool(true) => eval_tir(ctx, right),
                _ => Err(EvalError::type_error("BOOLEAN", &lv, span)),
            }
        }
        TirBoolOp::Equiv => {
            let lv = eval_tir(ctx, left)?;
            let rv = eval_tir(ctx, right)?;
            match (&lv, &rv) {
                (Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a == b)),
                _ => {
                    if !matches!(lv, Value::Bool(_)) {
                        Err(EvalError::type_error("BOOLEAN", &lv, span))
                    } else {
                        Err(EvalError::type_error("BOOLEAN", &rv, span))
                    }
                }
            }
        }
    }
}

/// Evaluate a TIR comparison operation.
pub(super) fn eval_tir_cmp(
    ctx: &EvalCtx,
    left: &Spanned<TirExpr>,
    op: TirCmpOp,
    right: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let lv = eval_tir(ctx, left)?;
    let rv = eval_tir(ctx, right)?;
    match op {
        TirCmpOp::Eq => {
            let eq = values_equal(ctx, &lv, &rv, span)?;
            Ok(Value::Bool(eq))
        }
        TirCmpOp::Neq => {
            let eq = values_equal(ctx, &lv, &rv, span)?;
            Ok(Value::Bool(!eq))
        }
        TirCmpOp::Lt => int_cmp_op(lv, rv, |a, b| a < b, |a, b| a < b, "<", span),
        TirCmpOp::Leq => int_cmp_op(lv, rv, |a, b| a <= b, |a, b| a <= b, "\\leq", span),
        TirCmpOp::Gt => int_cmp_op(lv, rv, |a, b| a > b, |a, b| a > b, ">", span),
        TirCmpOp::Geq => int_cmp_op(lv, rv, |a, b| a >= b, |a, b| a >= b, "\\geq", span),
    }
}
