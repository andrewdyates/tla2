// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::Value;
use num_traits::ToPrimitive;
use std::cmp::Ordering;
use std::sync::Arc;

// Primitive-to-Value comparison helpers (Part of #2825): avoid constructing
// Value enum (~96-136 bytes on stack) for what should be primitive comparisons.
// These produce identical orderings to Value::SmallInt(n).cmp(val) and
// Value::String(s).cmp(val) respectively.

/// Compare an i64 against a &Value, equivalent to Value::SmallInt(n).cmp(val).
#[inline]
pub(super) fn cmp_i64_with_value(n: i64, val: &Value) -> Ordering {
    match val {
        Value::SmallInt(k) => n.cmp(k),
        Value::Int(k) => {
            if let Some(k_i64) = k.to_i64() {
                n.cmp(&k_i64)
            } else if k.sign() == num_bigint::Sign::Minus {
                Ordering::Greater
            } else {
                Ordering::Less
            }
        }
        // type_order(SmallInt) = 1
        _ => 1u8.cmp(&type_order(val)),
    }
}

/// Compare an Arc<str> against a &Value, equivalent to Value::String(s.clone()).cmp(val).
#[inline]
pub(super) fn cmp_str_with_value(s: &Arc<str>, val: &Value) -> Ordering {
    match val {
        Value::String(other) => {
            if Arc::ptr_eq(s, other) {
                Ordering::Equal
            } else {
                (**s).cmp(&**other)
            }
        }
        // type_order(String) = 2
        _ => 2u8.cmp(&type_order(val)),
    }
}

/// Check if i64 == &Value, equivalent to Value::SmallInt(n) == *val.
#[inline]
pub(super) fn eq_i64_with_value(n: i64, val: &Value) -> bool {
    match val {
        Value::SmallInt(k) => n == *k,
        Value::Int(k) => k.to_i64().is_some_and(|k_i64| n == k_i64),
        _ => false,
    }
}

// We use a type-based ordering first, then value-based within types.
#[inline]
pub(in crate::value) fn type_order(v: &Value) -> u8 {
    match v {
        Value::Bool(_) => 0,
        Value::SmallInt(_) | Value::Int(_) => 1,
        Value::String(_) => 2,
        Value::ModelValue(_) => 3,
        Value::Tuple(_) => 4,
        Value::Seq(_) => 5,
        Value::Record(_) => 6,
        Value::Set(_)
        | Value::Interval(_)
        | Value::Subset(_)
        | Value::FuncSet(_)
        | Value::RecordSet(_)
        | Value::TupleSet(_)
        | Value::SetCup(_)
        | Value::SetCap(_)
        | Value::SetDiff(_)
        | Value::SetPred(_)
        | Value::KSubset(_)
        | Value::BigUnion(_)
        | Value::StringSet
        | Value::AnySet
        | Value::SeqSet(_) => 7,
        Value::Func(_) | Value::IntFunc(_) => 8,
        Value::LazyFunc(_) => 9,
        Value::Closure(_) => 10,
    }
}
