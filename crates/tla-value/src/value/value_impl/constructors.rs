// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `impl Value` constructors and model-value entry points.

use super::super::*;

impl Value {
    /// Create a boolean value
    pub fn bool(b: bool) -> Self {
        Value::Bool(b)
    }

    /// Create an integer value from i64 (uses SmallInt fast path)
    pub fn int(n: i64) -> Self {
        Value::SmallInt(n)
    }

    /// Create an integer value from BigInt
    /// Normalizes to SmallInt if the value fits in i64
    pub fn big_int(n: BigInt) -> Self {
        if let Some(small) = n.to_i64() {
            Value::SmallInt(small)
        } else {
            Value::Int(Arc::new(n))
        }
    }

    /// Create a string value, interning through the global string table.
    ///
    /// Part of #3287: Routes through `intern_string()` so that all production
    /// Value::String values get eager TLC token assignment at construction time.
    pub fn string(s: impl AsRef<str>) -> Self {
        Value::String(intern_string(s.as_ref()))
    }

    /// Create an empty set.
    ///
    /// Returns a cached singleton to avoid repeated `Arc::new(SortedSet::new())`
    /// allocation. Part of #3980.
    #[inline]
    pub fn empty_set() -> Self {
        super::super::value_pool::cached_empty_set()
    }

    /// Create a set from an iterator
    pub fn set(values: impl IntoIterator<Item = Value>) -> Self {
        Self::from_sorted_set(SortedSet::from_iter(values))
    }

    /// Create a concrete set from an already canonical `SortedSet`.
    ///
    /// Returns the cached empty set singleton when `set` is empty. Part of #3980.
    #[inline]
    pub fn from_sorted_set(set: SortedSet) -> Self {
        if set.is_empty() {
            return super::super::value_pool::cached_empty_set();
        }
        Value::Set(Arc::new(set))
    }

    /// Create a sequence from values (0-indexed internally, 1-indexed in TLA+).
    ///
    /// Returns a cached singleton for empty sequences. Part of #3980.
    pub fn seq(values: impl IntoIterator<Item = Value>) -> Self {
        let sv: SeqValue = values.into_iter().collect();
        if sv.is_empty() {
            return super::super::value_pool::cached_empty_seq();
        }
        Value::Seq(Arc::new(sv))
    }

    /// Create a tuple from values.
    ///
    /// Returns a cached singleton for empty tuples. Part of #3980.
    pub fn tuple(values: impl IntoIterator<Item = Value>) -> Self {
        let elems: Vec<Value> = values.into_iter().collect();
        if elems.is_empty() {
            return super::super::value_pool::cached_empty_tuple();
        }
        Value::Tuple(elems.into())
    }

    /// Create a record from field-value pairs
    pub fn record(fields: impl IntoIterator<Item = (impl Into<Arc<str>>, Value)>) -> Self {
        Value::Record(fields.into_iter().map(|(k, v)| (k.into(), v)).collect())
    }

    /// Create a lazy record set from field-name/set pairs.
    pub fn record_set(fields: impl IntoIterator<Item = (impl Into<Arc<str>>, Value)>) -> Self {
        Value::RecordSet(Arc::new(RecordSetValue::new(
            fields.into_iter().map(|(k, v)| (k.into(), v)),
        )))
    }

    /// Create a lazy tuple set from component sets.
    pub fn tuple_set(components: impl IntoIterator<Item = Value>) -> Self {
        Value::TupleSet(Arc::new(TupleSetValue::new(components)))
    }

    /// Create an interned model value.
    ///
    /// Uses the string intern table to ensure pointer equality for repeated model values.
    /// This enables O(1) comparisons via Arc pointer equality.
    ///
    /// Also registers the model value in the global model-value registry. This is used for:
    /// - O(1) permutation lookup during symmetry reduction.
    /// - TLC-normalized `compareTo` ordering (UniqueString token / first-seen order) for
    ///   parity-critical iteration (e.g. bounded `CHOOSE`).
    pub fn try_model_value(name: &str) -> crate::error::EvalResult<Self> {
        interned_model_value(name)
    }
}
