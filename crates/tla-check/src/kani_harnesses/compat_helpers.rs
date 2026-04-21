// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Test/harness helpers for constructing Value types without OrdSet/OrdMap.
//! Part of #3073 Step 3: migrate test code off deprecated tree-materialization APIs.

use crate::value::{FuncValue, SortedSet, Value};
use std::collections::BTreeSet;
use std::sync::Arc;

/// Create a Value::Set from unsorted elements.
pub(super) fn make_set(elems: Vec<Value>) -> Value {
    Value::Set(Arc::new(SortedSet::from_iter(elems)))
}

/// Create a FuncValue from unsorted (key, value) entries directly.
pub(super) fn make_func(mut entries: Vec<(Value, Value)>) -> FuncValue {
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    entries.dedup_by(|a, b| a.0 == b.0);
    FuncValue::from_sorted_entries(entries)
}

/// Simulate CHOOSE semantics on a BTreeSet: returns first element satisfying predicate.
#[allow(clippy::mutable_key_type)] // Value's OnceLock cache does not affect Ord/Eq
pub(super) fn choose<P>(set: &BTreeSet<Value>, predicate: P) -> Option<Value>
where
    P: Fn(&Value) -> bool,
{
    for elem in set.iter() {
        if predicate(elem) {
            return Some(elem.clone());
        }
    }
    None
}
