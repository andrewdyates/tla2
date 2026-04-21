// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TLC interval/set comparison rules.

use super::super::Value;
use crate::error::EvalResult;
use std::cmp::Ordering;

/// Compare interval values per TLC rules.
pub(super) fn cmp_interval(a: &Value, b: &Value) -> EvalResult<Ordering> {
    let Value::Interval(iv) = a else {
        unreachable!("cmp_interval called on non-interval");
    };
    match b {
        Value::Interval(jv) => {
            let cmp = iv.len().cmp(&jv.len());
            if cmp != Ordering::Equal {
                return Ok(cmp);
            }
            if iv.is_empty() {
                return Ok(Ordering::Equal);
            }
            Ok(iv.low.cmp(&jv.low))
        }
        _ => {
            // TLC: compare by converting to sets.
            cmp_set_elems(a, b)
        }
    }
}

/// Compare set-like values per TLC rules.
///
/// Part of #1434: Zero-allocation fast path for Set-Set comparison
/// when both sides are homogeneous-safe types (Bool/Int/String).
pub(super) fn cmp_sets(a: &Value, b: &Value) -> EvalResult<Ordering> {
    // SortedSet stores elements in Value::cmp order, which agrees with
    // tlc_cmp for these types, so we compare in-place without sorting.
    if let (Value::Set(sa), Value::Set(sb)) = (a, b) {
        let a_safe = match (sa.first(), sa.last()) {
            (Some(f), Some(l)) => {
                Value::tlc_cmp_agrees_with_ord(f)
                    && Value::tlc_cmp_type_class(f) == Value::tlc_cmp_type_class(l)
            }
            _ => true, // empty sets are trivially safe
        };
        let b_safe = match (sb.first(), sb.last()) {
            (Some(f), Some(l)) => {
                Value::tlc_cmp_agrees_with_ord(f)
                    && Value::tlc_cmp_type_class(f) == Value::tlc_cmp_type_class(l)
            }
            _ => true,
        };
        if a_safe && b_safe {
            let len_cmp = sa.len().cmp(&sb.len());
            if len_cmp != Ordering::Equal {
                return Ok(len_cmp);
            }
            for (x, y) in sa.iter().zip(sb.iter()) {
                let cmp = Value::tlc_cmp(x, y)?;
                if cmp != Ordering::Equal {
                    return Ok(cmp);
                }
            }
            return Ok(Ordering::Equal);
        }
    }

    // General path: materialize + sort both sides.
    cmp_set_elems(a, b)
}

/// Shared path: materialize elements from both sides and compare.
fn cmp_set_elems(a: &Value, b: &Value) -> EvalResult<Ordering> {
    let Some(ae) = Value::tlc_set_elems(a)? else {
        return Err(Value::tlc_cmp_err(format!(
            "Attempted to compare set {a:?} with non-set {b:?}"
        )));
    };
    let Some(be) = Value::tlc_set_elems(b)? else {
        return Err(Value::tlc_cmp_err(format!(
            "Attempted to compare set {a:?} with non-set {b:?}"
        )));
    };
    let len_cmp = ae.len().cmp(&be.len());
    if len_cmp != Ordering::Equal {
        return Ok(len_cmp);
    }
    for (x, y) in ae.iter().zip(be.iter()) {
        let cmp = Value::tlc_cmp(x, y)?;
        if cmp != Ordering::Equal {
            return Ok(cmp);
        }
    }
    Ok(Ordering::Equal)
}
