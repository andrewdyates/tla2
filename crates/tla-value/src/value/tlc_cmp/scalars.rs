// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLC scalar comparison rules (bool, integer, string).

use super::super::{tlc_string_token, Value};
use crate::error::EvalResult;
use num_traits::ToPrimitive;
use std::cmp::Ordering;

/// Compare two boolean values per TLC rules.
pub(super) fn cmp_bool(a: &Value, b: &Value) -> EvalResult<Ordering> {
    match (a, b) {
        (Value::Bool(x), Value::Bool(y)) => Ok(x.cmp(y)),
        _ => Err(Value::tlc_cmp_err(format!(
            "Attempted to compare boolean {a:?} with non-boolean {b:?}"
        ))),
    }
}

/// Compare two integer values per TLC rules.
pub(super) fn cmp_int(a: &Value, b: &Value) -> EvalResult<Ordering> {
    match b {
        Value::SmallInt(_) | Value::Int(_) => {
            fn cmp_ints(a: &Value, b: &Value) -> Ordering {
                match (a, b) {
                    (Value::SmallInt(x), Value::SmallInt(y)) => x.cmp(y),
                    (Value::SmallInt(x), Value::Int(y)) => {
                        if let Some(y_i64) = y.to_i64() {
                            x.cmp(&y_i64)
                        } else if y.sign() == num_bigint::Sign::Minus {
                            Ordering::Greater
                        } else {
                            Ordering::Less
                        }
                    }
                    (Value::Int(x), Value::SmallInt(y)) => {
                        if let Some(x_i64) = x.to_i64() {
                            x_i64.cmp(y)
                        } else if x.sign() == num_bigint::Sign::Minus {
                            Ordering::Less
                        } else {
                            Ordering::Greater
                        }
                    }
                    (Value::Int(x), Value::Int(y)) => x.cmp(y),
                    _ => unreachable!("cmp_ints called on non-integer values"),
                }
            }
            Ok(cmp_ints(a, b))
        }
        _ => Err(Value::tlc_cmp_err(format!(
            "Attempted to compare integer {a:?} with non-integer {b:?}"
        ))),
    }
}

/// Compare two string values per TLC rules (token order, not lexical).
/// Part of #3193: TLC compares strings by intern-token order
/// (UniqueString.tok), not lexical order.
pub(super) fn cmp_string(a: &Value, b: &Value) -> EvalResult<Ordering> {
    match (a, b) {
        (Value::String(x), Value::String(y)) => {
            let tx = tlc_string_token(x);
            let ty = tlc_string_token(y);
            Ok(tx.cmp(&ty))
        }
        _ => Err(Value::tlc_cmp_err(format!(
            "Attempted to compare string {a:?} with non-string {b:?}"
        ))),
    }
}
