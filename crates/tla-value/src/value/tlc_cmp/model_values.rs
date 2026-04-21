// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Model-value and overridden-value TLC comparison rules.
//!
//! Handles `ModelValue` ordering (typed, untyped, special model sets) per TLC's
//! `ModelValue.compareTo`. Returns `Ok(Some(ordering))` when model-value rules
//! decide the result, `Ok(None)` when comparison should continue with ordinary
//! TLC rules.

use super::super::{get_or_assign_model_value_index, Value};
use crate::error::EvalResult;
use std::cmp::Ordering;

/// Attempt to resolve comparison using model-value rules.
///
/// Returns `Ok(Some(ord))` when model-value rules decide the result,
/// `Ok(None)` when neither operand is a model value and comparison should
/// continue with ordinary TLC rules.
pub(super) fn cmp_model_values(a: &Value, b: &Value) -> EvalResult<Option<Ordering>> {
    // `Value::ModelValue` is also used for the infinite sets Nat/Int/Real. In TLC those are
    // "overridden values" (UserValue) and are not comparable with arbitrary non-model values.
    if let Value::ModelValue(a_name) = a {
        if Value::tlc_is_special_model_set(a_name) {
            return match b {
                Value::ModelValue(b_name) if Value::tlc_is_special_model_set(b_name) => {
                    Ok(Some(a_name.cmp(b_name)))
                }
                Value::ModelValue(_) => Ok(Some(Ordering::Greater)), // UserValue.compareTo(ModelValue) == 1
                _ => Err(Value::tlc_cmp_err(format!(
                    "Attempted to compare overridden value {a:?} with non-model value {b:?}"
                ))),
            };
        }
    }
    if let Value::ModelValue(b_name) = b {
        if Value::tlc_is_special_model_set(b_name) {
            return match a {
                Value::ModelValue(a_name) => {
                    if Value::tlc_model_value_type(a_name).is_some() {
                        Err(Value::tlc_cmp_err(format!(
                            "Attempted to compare typed model value {a:?} with overridden value {b:?}"
                        )))
                    } else {
                        Ok(Some(Ordering::Less))
                    }
                }
                _ => Err(Value::tlc_cmp_err(format!(
                    "Attempted to compare non-model value {a:?} with overridden value {b:?}"
                ))),
            };
        }
    }

    // ModelValue.compareTo(...) rules (typed/untyped).
    if let Value::ModelValue(a_name) = a {
        let a_t = Value::tlc_model_value_type(a_name);
        return match b {
            Value::ModelValue(b_name) => {
                if Value::tlc_is_special_model_set(b_name) {
                    return Err(Value::tlc_cmp_err(format!(
                        "Attempted to compare typed model value {a:?} with overridden value {b:?}"
                    )));
                }
                let b_t = Value::tlc_model_value_type(b_name);
                // TLC compares (typed or untyped) model values by their UniqueString token
                // order, not lexicographic order. We approximate this with our global model
                // value registry order (first-seen assignment).
                let a_tok = get_or_assign_model_value_index(a_name)?;
                let b_tok = get_or_assign_model_value_index(b_name)?;
                match (a_t, b_t) {
                    (None, _) => Ok(Some(a_tok.cmp(&b_tok))),
                    (Some(_), None) => Ok(Some(a_tok.cmp(&b_tok))), // typed vs untyped allowed
                    (Some(at), Some(bt)) if at == bt => Ok(Some(a_tok.cmp(&b_tok))),
                    (Some(_), Some(_)) => Err(Value::tlc_cmp_err(format!(
                        "Attempted to compare the differently-typed model values {a:?} and {b:?}"
                    ))),
                }
            }
            _ => {
                if a_t.is_some() {
                    Err(Value::tlc_cmp_err(format!(
                        "Attempted to compare the typed model value {a:?} and non-model value {b:?}"
                    )))
                } else {
                    Ok(Some(Ordering::Less))
                }
            }
        };
    }

    // Non-model `compareTo(ModelValue)` delegates to `ModelValue.modelValueCompareTo`.
    if let Value::ModelValue(b_name) = b {
        if Value::tlc_model_value_type(b_name).is_some() {
            return Err(Value::tlc_cmp_err(format!(
                "Attempted to compare the typed model value {b:?} and non-model value {a:?}"
            )));
        }
        return Ok(Some(Ordering::Greater));
    }

    Ok(None)
}
