// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::Value;
use num_traits::ToPrimitive;
use std::cmp::Ordering;
use std::sync::Arc;

/// Same-type equality for values within the same type_order group.
/// Caller guarantees type_order(lhs) == type_order(rhs) and that cross-type
/// cases have already been handled.
#[inline]
pub(in crate::value) fn eq_same_type(lhs: &Value, rhs: &Value) -> bool {
    match (lhs, rhs) {
        (Value::Bool(a), Value::Bool(b)) => a == b,
        (Value::SmallInt(a), Value::SmallInt(b)) => a == b,
        (Value::SmallInt(a), Value::Int(b)) => b.to_i64().is_some_and(|b_i64| *a == b_i64),
        (Value::Int(a), Value::SmallInt(b)) => a.to_i64().is_some_and(|a_i64| a_i64 == *b),
        (Value::Int(a), Value::Int(b)) => a == b,
        (Value::String(a), Value::String(b)) => Arc::ptr_eq(a, b) || a == b,
        (Value::ModelValue(a), Value::ModelValue(b)) => Arc::ptr_eq(a, b) || a == b,
        (Value::Tuple(a), Value::Tuple(b)) => {
            Arc::ptr_eq(a, b)
                || (a.len() == b.len() && a.iter().zip(b.iter()).all(|(av, bv)| av == bv))
        }
        (Value::Seq(a), Value::Seq(b)) => {
            a.ptr_eq(b) || (a.len() == b.len() && a.iter().zip(b.iter()).all(|(av, bv)| av == bv))
        }
        (Value::Record(a), Value::Record(b)) => {
            a.ptr_eq(b)
                || (a.len() == b.len()
                    && a.iter()
                        .zip(b.iter())
                        .all(|((ak, av), (bk, bv))| ak == bk && av == bv))
        }
        (Value::Func(a), Value::Func(b)) => {
            a.ptr_eq(b)
                || (a.domain_len() == b.domain_len()
                    && a.mapping_iter()
                        .zip(b.mapping_iter())
                        .all(|((ak, av), (bk, bv))| ak == bk && av == bv))
        }
        (Value::IntFunc(a), Value::IntFunc(b)) => {
            (Arc::ptr_eq(&a.values, &b.values) && a.min == b.min && a.max == b.max)
                || (a.min == b.min
                    && a.max == b.max
                    && a.values.len() == b.values.len()
                    && a.values
                        .iter()
                        .zip(b.values.iter())
                        .all(|(av, bv)| av == bv))
        }
        (Value::LazyFunc(a), Value::LazyFunc(b)) => a.id() == b.id(),
        (Value::Closure(a), Value::Closure(b)) => a.id() == b.id(),
        // Set types: Arc pointer equality fast path before full extensional
        // comparison. For UNCHANGED evaluation, sets that weren't modified share
        // the same Arc allocation. Part of #3805.
        (Value::Set(a), Value::Set(b)) => {
            a.ptr_eq(b) || *a == *b
        }
        // Other set types: delegate to cmp()-based comparison since set equality
        // requires extensional/structural comparison that cmp() already handles.
        _ => lhs.cmp(rhs) == Ordering::Equal,
    }
}
