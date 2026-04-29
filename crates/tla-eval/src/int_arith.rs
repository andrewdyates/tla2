// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{EvalError, EvalResult, Span, Value};
use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};

// Integer arithmetic helper functions extracted from eval_arith.rs as part of
// #3424.

/// Apply binary arithmetic operation with SmallInt fast path
///
/// Used for +, -, * which don't need division-by-zero checks.
/// `op_name` is the TLC operator name for TLC-compatible error messages.
/// Part of #2955: inline hot-path arithmetic inner helper.
#[inline(always)]
pub(super) fn int_arith_op(
    left: Value,
    right: Value,
    small_op: impl Fn(i64, i64) -> Option<i64>,
    big_op: impl Fn(BigInt, BigInt) -> BigInt,
    op_name: &str,
    span: Option<Span>,
) -> EvalResult<Value> {
    // SmallInt fast path
    if let (Value::SmallInt(a), Value::SmallInt(b)) = (&left, &right) {
        if let Some(result) = small_op(*a, *b) {
            return Ok(Value::SmallInt(result));
        }
        // Overflow: fall through to BigInt
    }
    // BigInt path (TLC: EC.TLC_MODULE_ARGUMENT_ERROR)
    let a = left
        .to_bigint()
        .ok_or_else(|| EvalError::argument_error("first", op_name, "integer", &left, span))?;
    let b = right
        .to_bigint()
        .ok_or_else(|| EvalError::argument_error("second", op_name, "integer", &right, span))?;
    Ok(Value::big_int(big_op(a, b)))
}

/// Apply integer comparison operation with SmallInt fast path
/// `op_name` is the TLC operator name for TLC-compatible error messages.
pub(super) fn int_cmp_op(
    left: Value,
    right: Value,
    small_cmp: impl Fn(i64, i64) -> bool,
    big_cmp: impl Fn(&BigInt, &BigInt) -> bool,
    op_name: &str,
    span: Option<Span>,
) -> EvalResult<Value> {
    if let (Value::SmallInt(a), Value::SmallInt(b)) = (&left, &right) {
        return Ok(Value::Bool(small_cmp(*a, *b)));
    }

    let a = left
        .to_bigint()
        .ok_or_else(|| EvalError::argument_error("first", op_name, "integer", &left, span))?;
    let b = right
        .to_bigint()
        .ok_or_else(|| EvalError::argument_error("second", op_name, "integer", &right, span))?;
    Ok(Value::Bool(big_cmp(&a, &b)))
}

/// Apply division operation with SmallInt fast path and zero check
///
/// Used for /, \div which need division-by-zero checks.
/// The `small_op` returns `Option<i64>` to handle potential overflow.
/// `op_name` is the TLC operator name for TLC-compatible error messages.
pub(super) fn int_div_op(
    left: Value,
    right: Value,
    small_op: impl Fn(i64, i64) -> Option<i64>,
    big_op: impl Fn(BigInt, BigInt) -> BigInt,
    op_name: &str,
    span: Option<Span>,
) -> EvalResult<Value> {
    // SmallInt fast path
    if let (Value::SmallInt(a), Value::SmallInt(b)) = (&left, &right) {
        if *b == 0 {
            return Err(EvalError::DivisionByZero { span });
        }
        if let Some(result) = small_op(*a, *b) {
            return Ok(Value::SmallInt(result));
        }
        // Overflow (e.g., MIN / -1): fall through to BigInt
    }
    // BigInt path (TLC: EC.TLC_MODULE_ARGUMENT_ERROR)
    let a = left
        .to_bigint()
        .ok_or_else(|| EvalError::argument_error("first", op_name, "integer", &left, span))?;
    let b = right
        .to_bigint()
        .ok_or_else(|| EvalError::argument_error("second", op_name, "integer", &right, span))?;
    if b.is_zero() {
        return Err(EvalError::DivisionByZero { span });
    }
    Ok(Value::big_int(big_op(a, b)))
}

/// Apply modulus operation with positive divisor check (TLC semantics)
///
/// TLC requires the divisor to be positive (> 0), not just non-zero.
/// Returns ModulusNotPositive error if divisor <= 0.
pub(super) fn int_mod_op(left: Value, right: Value, span: Option<Span>) -> EvalResult<Value> {
    // SmallInt fast path
    if let (Value::SmallInt(a), Value::SmallInt(b)) = (&left, &right) {
        if *b <= 0 {
            return Err(EvalError::ModulusNotPositive {
                value: b.to_string(),
                span,
            });
        }
        // Euclidean modulo (always non-negative for positive divisor)
        return Ok(Value::SmallInt(a.rem_euclid(*b)));
    }
    // BigInt path (TLC: EC.TLC_MODULE_ARGUMENT_ERROR)
    let a = left
        .to_bigint()
        .ok_or_else(|| EvalError::argument_error("first", "%", "integer", &left, span))?;
    let b = right
        .to_bigint()
        .ok_or_else(|| EvalError::argument_error("second", "%", "integer", &right, span))?;
    if b <= BigInt::from(0) {
        return Err(EvalError::ModulusNotPositive {
            value: b.to_string(),
            span,
        });
    }
    // Euclidean modulo (always non-negative for positive divisor)
    let r = &a % &b;
    let result = if r < BigInt::from(0) { r + &b } else { r };
    Ok(Value::big_int(result))
}

/// Apply power operation with SmallInt fast path
///
/// Special handling: exponent must be non-negative and fit in u32.
pub(super) fn int_pow_op(left: Value, right: Value, span: Option<Span>) -> EvalResult<Value> {
    // SmallInt fast path for small exponents
    if let (Value::SmallInt(base), Value::SmallInt(exp)) = (&left, &right) {
        if *exp >= 0 && *exp <= 62 {
            if let Some(result) = base.checked_pow(*exp as u32) {
                return Ok(Value::SmallInt(result));
            }
        }
        // Overflow or large exponent: fall through to BigInt
    }
    // BigInt path (TLC: EC.TLC_MODULE_ARGUMENT_ERROR)
    let base = left
        .to_bigint()
        .ok_or_else(|| EvalError::argument_error("first", "^", "integer", &left, span))?;
    let exp = right
        .to_bigint()
        .ok_or_else(|| EvalError::argument_error("second", "^", "integer", &right, span))?;
    let exp_u32 = exp.to_u32().ok_or_else(|| EvalError::Internal {
        message: "Exponent too large or negative".into(),
        span,
    })?;
    Ok(Value::big_int(base.pow(exp_u32)))
}
