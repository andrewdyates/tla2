// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::{SortedSet, Value};
use super::FuncValue;
use num_bigint::BigInt;
use std::sync::Arc;

impl FuncValue {
    /// Get the cached TLC-normalized domain index order if already computed.
    #[inline]
    pub(crate) fn tlc_normalized_order(&self) -> Option<&[usize]> {
        self.tlc_normalized.get().map(std::convert::AsRef::as_ref)
    }

    /// Cache TLC-normalized domain index order and return a reference to it.
    /// If another thread already set it (race), returns the winner's value.
    pub(crate) fn cache_tlc_normalized_order(&self, order: Arc<[usize]>) -> &[usize] {
        let _ = self.tlc_normalized.set(order);
        // Safe: either our set succeeded or another thread's did — either way it's populated.
        self.tlc_normalized
            .get()
            .expect("invariant: OnceLock populated by set() or concurrent init")
            .as_ref()
    }

    /// Get the number of elements in the domain.
    #[inline]
    pub fn domain_len(&self) -> usize {
        self.domain.len()
    }

    /// Borrow the domain keys as a slice.
    #[doc(hidden)]
    #[deprecated(
        note = "compatibility-only storage view; prefer domain_iter() or domain_eq_sorted_set()"
    )]
    #[inline]
    pub fn domain_slice(&self) -> &[Value] {
        self.domain.as_ref()
    }

    /// Check if the domain is empty.
    #[inline]
    pub fn domain_is_empty(&self) -> bool {
        self.domain.is_empty()
    }

    /// Check if a value is in the domain.
    #[inline]
    pub fn domain_contains(&self, key: &Value) -> bool {
        self.domain
            .binary_search_by(|domain_key| domain_key.cmp(key))
            .is_ok()
    }

    /// Iterator over domain elements (keys).
    pub fn domain_iter(&self) -> impl Iterator<Item = &Value> + '_ {
        self.domain.iter()
    }

    /// Compare this function's domain with a sorted set without allocating adapters.
    #[inline]
    pub fn domain_eq_sorted_set(&self, other: &SortedSet) -> bool {
        self.domain_len() == other.len()
            && self.domain_iter().zip(other.iter()).all(|(a, b)| a == b)
    }

    /// Check whether the domain is exactly `{1, 2, ..., n}`.
    pub fn domain_is_sequence(&self) -> bool {
        let mut expected: i64 = 1;
        for key in self.domain_iter() {
            match key {
                Value::SmallInt(n) if *n == expected => {}
                Value::Int(n) if **n == BigInt::from(expected) => {}
                _ => return false,
            }
            expected = match expected.checked_add(1) {
                Some(next) => next,
                None => return false,
            };
        }
        true
    }

    /// Convert domain to SortedSet.
    #[doc(hidden)]
    #[deprecated(
        note = "compatibility-only materialization helper; prefer domain_eq_sorted_set() or domain_iter()"
    )]
    pub fn domain_as_sorted_set(&self) -> SortedSet {
        let keys: Vec<Value> = self.domain.iter().cloned().collect();
        SortedSet::from_sorted_vec(keys)
    }

    /// Get a value by key (same as apply).
    #[inline]
    pub fn mapping_get(&self, key: &Value) -> Option<&Value> {
        self.apply(key)
    }

    /// Borrow the mapped values as a raw slice.
    /// Part of #3371: Panics if overlay is active. Callers that need raw
    /// slice access must call `materialize()` first or switch to `get_value_at()`.
    #[doc(hidden)]
    #[deprecated(note = "compatibility-only storage view; prefer mapping_values() or iter()")]
    #[inline]
    pub fn values_slice(&self) -> &[Value] {
        debug_assert!(
            self.overrides.is_none(),
            "values_slice called on overlaid FuncValue — call materialize() first"
        );
        self.values.as_slice()
    }

    /// Iterator over values (overlay-aware).
    /// Part of #3371.
    pub fn mapping_values(&self) -> impl Iterator<Item = &Value> + '_ {
        (0..self.domain.len()).map(move |i| self.get_value_at(i))
    }

    /// Iterator over (key, value) pairs (overlay-aware).
    /// Part of #3371.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = (&Value, &Value)> + '_ {
        self.domain
            .iter()
            .enumerate()
            .map(move |(i, k)| (k, self.get_value_at(i)))
    }

    /// Iterator over (key, value) pairs.
    #[inline]
    pub fn mapping_iter(&self) -> impl ExactSizeIterator<Item = (&Value, &Value)> + '_ {
        self.iter()
    }

    /// Clone the interleaved `(key, value)` view.
    #[doc(hidden)]
    #[deprecated(
        note = "compatibility-only allocating helper; prefer iter() and clone locally only where needed"
    )]
    #[inline]
    pub fn entries_cloned(&self) -> Vec<(Value, Value)> {
        self.iter()
            .map(|(key, value)| (key.clone(), value.clone()))
            .collect()
    }

    /// Borrow the key at a given domain index.
    #[inline]
    pub(crate) fn key_at(&self, idx: usize) -> &Value {
        &self.domain[idx]
    }

    /// Borrow the value at a given domain index (overlay-aware).
    /// Part of #3371.
    #[inline]
    pub(crate) fn value_at(&self, idx: usize) -> &Value {
        self.get_value_at(idx)
    }

    /// Pointer to the current domain buffer, used by split-array tests.
    #[cfg(test)]
    #[inline]
    pub(crate) fn domain_ptr(&self) -> *const Value {
        self.domain.as_ptr()
    }

    /// Pointer to the current values buffer, used by COW tests.
    #[cfg(test)]
    #[inline]
    pub(crate) fn values_ptr(&self) -> *const Value {
        self.values.as_ptr()
    }
}
