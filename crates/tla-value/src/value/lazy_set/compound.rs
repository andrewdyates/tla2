// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `LazySet` implementations for compound special cases with non-default
//! iteration semantics: `UnionValue` and `SeqSetValue`.

use super::trait_api::LazySet;
use crate::value::sorted_set::SortedSet;
use crate::value::{SeqSetValue, UnionValue, Value};
use num_bigint::BigInt;

// ==========================================================================
// Tier 3: UnionValue — set_contains returns Option<bool>
// to_ord_set, set_len, set_iter: use trait defaults (route through to_sorted_set).
// TLC's UnionValue.Enumerator does NOT dedup during streaming iteration.
// Dedup happens lazily through normalize() only when the set needs comparison or
// fingerprinting. For set filter usage ({x \in UNION S : P(x)}), TLC returns a
// lazy SetPredValue because UnionValue does NOT implement Reducible.
// ==========================================================================

impl LazySet for UnionValue {
    fn set_contains(&self, value: &Value) -> Option<bool> {
        self.contains(value)
    }

    fn to_sorted_set(&self) -> Option<SortedSet> {
        UnionValue::to_sorted_set(self)
    }

    fn set_is_empty(&self) -> bool {
        self.is_empty()
    }

    /// Streaming iteration without sort — matches TLC's UnionValue.Enumerator.
    ///
    /// The default `set_iter()` routes through `to_sorted_set()` → `as_slice()`,
    /// which forces O(n log n) sort+dedup on all inner elements. For specs like
    /// MCBinarySearch with ~488K elements across 8 FuncSets, this sort dominates
    /// startup time.
    ///
    /// This override iterates each inner set's elements directly via `iter_set()`
    /// (which uses streaming iterators like FuncSetIterator) and collects without
    /// sorting. Duplicates across inner sets are harmless: predicate filtering
    /// evaluates the same element twice (correct), and final set construction
    /// deduplicates via SortedSet normalization.
    fn set_iter(&self) -> Option<Box<dyn Iterator<Item = Value> + '_>> {
        let outer_iter = self.set.iter_set()?;
        let mut all_elements = Vec::new();
        for inner_set in outer_iter {
            match inner_set.iter_set() {
                Some(inner_iter) => all_elements.extend(inner_iter),
                None => return None,
            }
        }
        Some(Box::new(all_elements.into_iter()))
    }

    fn is_enumerable(&self) -> bool {
        UnionValue::is_enumerable(self)
    }
}

// ==========================================================================
// Tier 4: SeqSetValue — membership-only, infinite set
// ==========================================================================

impl LazySet for SeqSetValue {
    fn set_contains(&self, value: &Value) -> Option<bool> {
        self.contains(value)
    }

    fn to_sorted_set(&self) -> Option<SortedSet> {
        None // Infinite set, cannot enumerate
    }

    fn set_len(&self) -> Option<BigInt> {
        None // Infinite
    }

    fn set_is_empty(&self) -> bool {
        false // Seq(S) always contains <<>> (the empty sequence)
    }

    fn set_iter(&self) -> Option<Box<dyn Iterator<Item = Value> + '_>> {
        // Seq(S) is infinite in general, but Seq({}) = {<<>>} is enumerable.
        let mut base_iter = self.base.iter_set()?;
        if base_iter.next().is_none() {
            Some(Box::new(std::iter::once(Value::seq(std::iter::empty()))))
        } else {
            None
        }
    }

    fn is_enumerable(&self) -> bool {
        false
    }
}
