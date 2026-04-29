// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{IntervalValue, SortedSet, Value};
use crate::error::{EvalError, EvalResult};
use num_bigint::BigInt;
use std::sync::Arc;

// === Utility functions ===

/// Create a range set {a..b} (inclusive) as a lazy interval
pub fn range_set(a: &BigInt, b: &BigInt) -> Value {
    if a > b {
        return Value::empty_set();
    }
    Value::Interval(Arc::new(IntervalValue::new(a.clone(), b.clone())))
}

/// Create the BOOLEAN set {TRUE, FALSE}.
///
/// Returns a cached singleton to avoid constructing the 2-element set on each
/// call. Part of #3980.
#[inline]
pub fn boolean_set() -> Value {
    super::value_pool::cached_boolean_set()
}

/// Compute SUBSET S (powerset)
///
/// Returns `EvalError::SetTooLarge` if the set has more than 20 elements,
/// since 2^20 = 1M subsets would be too large to enumerate.
pub fn powerset(set: &SortedSet) -> EvalResult<Value> {
    let elements: Vec<_> = set.iter().cloned().collect();
    let n = elements.len();

    if n > 20 {
        // Safety limit - 2^20 = 1M elements
        return Err(EvalError::SetTooLarge { span: None });
    }

    let mut result: Vec<Value> = Vec::with_capacity(1 << n);
    for mask in 0..(1u64 << n) {
        let mut subset: Vec<Value> = Vec::new();
        for (i, elem) in elements.iter().enumerate() {
            if mask & (1 << i) != 0 {
                subset.push(elem.clone());
            }
        }
        result.push(Value::set(subset));
    }
    Ok(Value::set(result))
}

/// Compute UNION S (big union - union of all sets in S)
pub fn big_union(set: &SortedSet) -> Option<Value> {
    let mut result: Vec<Value> = Vec::new();
    for elem in set.raw_iter() {
        let inner = elem.to_sorted_set()?;
        result.extend(inner.raw_iter().cloned());
    }
    Some(Value::set(result))
}

/// Compute Cartesian product S1 \X S2 \X ...
pub fn cartesian_product(sets: &[&SortedSet]) -> Value {
    if sets.is_empty() {
        return Value::set([Value::Tuple(Vec::new().into())]);
    }

    // Build up tuples incrementally
    let mut result: Vec<Vec<Value>> = vec![vec![]];

    for set in sets {
        let mut new_result = Vec::new();
        for tuple in &result {
            for elem in set.raw_iter() {
                let mut new_tuple = tuple.clone();
                new_tuple.push(elem.clone());
                new_result.push(new_tuple);
            }
        }
        result = new_result;
    }

    Value::set(result.into_iter().map(|v| Value::Tuple(v.into())))
}
