// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SmtValue comparison and array evaluation helpers.
//!
//! Contains `smt_values_equal` (cross-sort equality), `eval_array_select`,
//! `eval_array_store`, and `eval_int_cmp` used by the expression evaluator.

use rustc_hash::FxHashMap;

use super::super::ChcExpr;
use super::evaluate_expr;
use crate::smt::SmtValue;

fn array_lookup<'a>(
    default: &'a SmtValue,
    entries: &'a [(SmtValue, SmtValue)],
    idx: &SmtValue,
) -> Option<&'a SmtValue> {
    for (k, v) in entries.iter().rev() {
        match smt_values_equal(k, idx) {
            Some(true) => return Some(v),
            Some(false) => {}
            None => return None,
        }
    }
    Some(default)
}

/// Cross-sort equality for `SmtValue`.
///
/// Same-sort values use standard equality. For mixed Bool/Int (or Bool/Real),
/// coerces Bool to the arithmetic sort before comparing, matching the semantics
/// of `eliminate_mixed_sort_eq`: `true → 1`, `false → 0`.
///
/// This is needed because the model verifier evaluates the *original* CHC
/// expression (before preprocessing), which may contain mixed-sort equalities
/// like `(= D:Int (= E 0):Bool)`. The solver operates on the rewritten form
/// `(= D:Int (ite (= E 0) 1 0))` and produces Int values, but the verifier
/// must interpret the original cross-sort comparison correctly.
pub(super) fn smt_values_equal(a: &SmtValue, b: &SmtValue) -> Option<bool> {
    match (a, b) {
        // Same-sort cases: use standard equality
        (SmtValue::Bool(x), SmtValue::Bool(y)) => Some(x == y),
        (SmtValue::Int(x), SmtValue::Int(y)) => Some(x == y),
        (SmtValue::BitVec(v1, w1), SmtValue::BitVec(v2, w2)) => Some(v1 == v2 && w1 == w2),
        (SmtValue::Real(x), SmtValue::Real(y)) => Some(x == y),
        (SmtValue::Datatype(ctor1, fields1), SmtValue::Datatype(ctor2, fields2)) => {
            if ctor1 != ctor2 || fields1.len() != fields2.len() {
                return Some(false);
            }
            for (lhs, rhs) in fields1.iter().zip(fields2.iter()) {
                if !smt_values_equal(lhs, rhs)? {
                    return Some(false);
                }
            }
            Some(true)
        }
        (SmtValue::Opaque(x), SmtValue::Opaque(y)) => {
            if x == y {
                Some(true)
            } else {
                None
            }
        }
        (SmtValue::Opaque(_), _) | (_, SmtValue::Opaque(_)) => None,

        // Cross-sort Bool/Int: coerce Bool → Int (true=1, false=0)
        (SmtValue::Bool(b_val), SmtValue::Int(i_val))
        | (SmtValue::Int(i_val), SmtValue::Bool(b_val)) => {
            Some(*i_val == if *b_val { 1 } else { 0 })
        }

        // Cross-sort Bool/Real: coerce Bool → Real (true=1, false=0)
        (SmtValue::Bool(b_val), SmtValue::Real(r_val))
        | (SmtValue::Real(r_val), SmtValue::Bool(b_val)) => {
            use num_traits::{One, Zero};
            if *b_val {
                Some(r_val.is_one())
            } else {
                Some(r_val.is_zero())
            }
        }

        // Array equality: two arrays are equal iff they agree on all indices.
        // For finite representations we check structural equivalence (#6047).
        (SmtValue::ConstArray(d1), SmtValue::ConstArray(d2)) => smt_values_equal(d1, d2),
        (
            SmtValue::ArrayMap {
                default: d1,
                entries: e1,
            },
            SmtValue::ArrayMap {
                default: d2,
                entries: e2,
            },
        ) => {
            if !smt_values_equal(d1, d2)? {
                return Some(false);
            }
            // Compare the observable value at every explicit index from either
            // side, respecting last-store-wins semantics for duplicate writes.
            for (k, _) in e1.iter().chain(e2.iter()) {
                let lhs = array_lookup(d1.as_ref(), e1, k)?;
                let rhs = array_lookup(d2.as_ref(), e2, k)?;
                if !smt_values_equal(lhs, rhs)? {
                    return Some(false);
                }
            }
            Some(true)
        }
        (
            SmtValue::ConstArray(d),
            SmtValue::ArrayMap {
                default: d2,
                entries,
            },
        )
        | (
            SmtValue::ArrayMap {
                default: d2,
                entries,
            },
            SmtValue::ConstArray(d),
        ) => {
            if !smt_values_equal(d, d2)? {
                return Some(false);
            }
            // All observable explicit indices must agree with the const default.
            for (k, _) in entries {
                let observed = array_lookup(d2.as_ref(), entries, k)?;
                if !smt_values_equal(observed, d)? {
                    return Some(false);
                }
            }
            Some(true)
        }

        // All other cross-sort pairs are never equal
        _ => Some(false),
    }
}

/// Look up an index in an array value.
///
/// Walks the store chain (represented by `ArrayMap.entries`) to find the
/// matching index. Falls back to the default value for `ConstArray` or
/// `ArrayMap.default`.
pub(crate) fn eval_array_select(arr: &SmtValue, idx: &SmtValue) -> Option<SmtValue> {
    match arr {
        SmtValue::ConstArray(default) => Some(default.as_ref().clone()),
        SmtValue::ArrayMap { default, entries } => {
            // Search entries in reverse order (last store wins).
            for (k, v) in entries.iter().rev() {
                match smt_values_equal(k, idx) {
                    Some(true) => return Some(v.clone()),
                    Some(false) => {}
                    None => return None,
                }
            }
            Some(default.as_ref().clone())
        }
        _ => None,
    }
}

/// Insert/overwrite an entry in an array value, producing a new array.
pub(in crate::expr) fn eval_array_store(arr: SmtValue, idx: SmtValue, val: SmtValue) -> SmtValue {
    match arr {
        SmtValue::ConstArray(default) => SmtValue::ArrayMap {
            default,
            entries: vec![(idx, val)],
        },
        SmtValue::ArrayMap {
            default,
            mut entries,
        } => {
            // Remove any existing entry with the same index.
            entries.retain(|(k, _)| !matches!(smt_values_equal(k, &idx), Some(true)));
            entries.push((idx, val));
            SmtValue::ArrayMap { default, entries }
        }
        // If arr is not an array value, wrap as ArrayMap with arr as an opaque
        // default (lossy but sound for verification: select on unknown index
        // will return the opaque default → Indeterminate on type mismatch).
        _ => SmtValue::ArrayMap {
            default: Box::new(arr),
            entries: vec![(idx, val)],
        },
    }
}

/// Helper: evaluate an integer comparison.
pub(super) fn eval_int_cmp(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
    cmp: impl FnOnce(i64, i64) -> bool,
) -> Option<SmtValue> {
    match (evaluate_expr(lhs, model)?, evaluate_expr(rhs, model)?) {
        (SmtValue::Int(a), SmtValue::Int(b)) => Some(SmtValue::Bool(cmp(a, b))),
        _ => None,
    }
}
