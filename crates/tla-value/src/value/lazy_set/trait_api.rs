// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared `LazySet` trait contract and default materialization helpers.

use crate::value::sorted_set::SortedSet;
use crate::value::Value;
use num_bigint::BigInt;

/// Trait for lazy/unenumerated set types that support common set operations.
///
/// Not all set types can implement all operations (e.g., SetPredValue needs
/// an eval context for membership, SeqSetValue is infinite). Types that cannot
/// support an operation return None.
///
/// Phase 1A (#3073): `to_sorted_set()` is the primary materialization method.
/// All defaults route through `to_sorted_set()`.
#[allow(dead_code)] // set_is_empty/is_enumerable called on concrete types, not via dyn dispatch
pub(crate) trait LazySet {
    /// Check if a value is a member of this set.
    /// Returns None if membership cannot be determined without additional context.
    fn set_contains(&self, value: &Value) -> Option<bool>;

    /// Materialize to a SortedSet (primary materialization path).
    /// Returns None if the set cannot be enumerated.
    fn to_sorted_set(&self) -> Option<SortedSet>;

    /// Compute the cardinality of this set.
    /// Default uses `to_sorted_set()` — O(n) Vec length vs O(n log n) OrdSet build.
    /// Types with optimized cardinality (IntervalValue, SubsetValue, etc.) override this.
    fn set_len(&self) -> Option<BigInt> {
        let set = self.to_sorted_set()?;
        Some(BigInt::from(set.len()))
    }

    /// Check if the set is empty.
    fn set_is_empty(&self) -> bool;

    /// Return an iterator over all elements.
    /// Default materializes via `to_sorted_set()` and collects to an owned Vec.
    /// Types with native iterators (IntervalValue, SubsetValue, etc.) override this.
    fn set_iter(&self) -> Option<Box<dyn Iterator<Item = Value> + '_>> {
        let set = self.to_sorted_set()?;
        // SortedSet is Arc-backed; collect to Vec for an owned iterator.
        // This is O(n) clone vs the old O(n log n) OrdSet build + O(n) consume.
        let elements: Vec<Value> = set.as_slice().to_vec();
        Some(Box::new(elements.into_iter()))
    }

    /// Return a fully owned (`'static`) iterator over all elements.
    ///
    /// Part of #3978: Unlike `set_iter()` which returns an iterator borrowing `self`,
    /// this returns an iterator that owns its data. This enables streaming iteration
    /// in `SetPredStreamIter` where the source iterator must outlive the source value
    /// reference.
    ///
    /// Types with native owned iterators (FuncSet's odometer, Interval, Subset, KSubset)
    /// override this to avoid the collect+re-iterate overhead. The default falls back
    /// to `set_iter()` -> collect -> `Vec::into_iter()`.
    fn set_iter_owned(&self) -> Option<Box<dyn Iterator<Item = Value>>> {
        let iter = self.set_iter()?;
        let elements: Vec<Value> = iter.collect();
        Some(Box::new(elements.into_iter()))
    }

    /// Whether this set can be enumerated (finite and materializable).
    fn is_enumerable(&self) -> bool {
        true
    }
}
