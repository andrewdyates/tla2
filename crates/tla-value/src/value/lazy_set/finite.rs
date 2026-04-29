// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `LazySet` implementations for finite, mostly delegating set families.

use super::trait_api::LazySet;
use crate::value::sorted_set::SortedSet;
use crate::value::{
    FuncSetIterator, FuncSetValue, IntervalValue, KSubsetIterator, KSubsetValue,
    RecordSetOwnedIterator, RecordSetValue, SubsetIterator, SubsetValue, TupleSetOwnedIterator,
    TupleSetValue, Value,
};
use num_bigint::BigInt;

// ==========================================================================
// Tier 2: IntervalValue — always succeeds (non-optional returns wrapped in Some)
// ==========================================================================

impl LazySet for IntervalValue {
    fn set_contains(&self, value: &Value) -> Option<bool> {
        Some(self.contains(value))
    }

    fn to_sorted_set(&self) -> Option<SortedSet> {
        Some(IntervalValue::to_sorted_set(self))
    }

    fn set_len(&self) -> Option<BigInt> {
        Some(self.len())
    }

    fn set_is_empty(&self) -> bool {
        self.is_empty()
    }

    fn set_iter(&self) -> Option<Box<dyn Iterator<Item = Value> + '_>> {
        Some(Box::new(self.iter_values()))
    }

    /// Part of #3978: IntervalValue's iter_values() produces an owned iterator
    /// (i64 range or BigInt counter) — no collection needed.
    fn set_iter_owned(&self) -> Option<Box<dyn Iterator<Item = Value>>> {
        Some(Box::new(self.iter_values()))
    }
}

// ==========================================================================
// Tier 1: SubsetValue — own optimized methods
// ==========================================================================

impl LazySet for SubsetValue {
    fn set_contains(&self, value: &Value) -> Option<bool> {
        self.contains(value)
    }

    fn to_sorted_set(&self) -> Option<SortedSet> {
        SubsetValue::to_sorted_set(self)
    }

    fn set_len(&self) -> Option<BigInt> {
        self.len()
    }

    fn set_is_empty(&self) -> bool {
        self.is_empty()
    }

    fn set_iter(&self) -> Option<Box<dyn Iterator<Item = Value> + '_>> {
        let iter = self.iter()?;
        Some(Box::new(iter))
    }

    /// Part of #3978: SubsetIterator owns its element Vec — construct directly
    /// to avoid the borrowing `self.iter()` method signature.
    fn set_iter_owned(&self) -> Option<Box<dyn Iterator<Item = Value>>> {
        let base_set = self.base().to_sorted_set()?;
        Some(Box::new(SubsetIterator::new(base_set)))
    }
}

// ==========================================================================
// Tier 1: FuncSetValue — own optimized methods
// ==========================================================================

impl LazySet for FuncSetValue {
    fn set_contains(&self, value: &Value) -> Option<bool> {
        self.contains(value)
    }

    fn to_sorted_set(&self) -> Option<SortedSet> {
        FuncSetValue::to_sorted_set(self)
    }

    fn set_len(&self) -> Option<BigInt> {
        self.len()
    }

    fn set_is_empty(&self) -> bool {
        self.is_empty()
    }

    fn set_iter(&self) -> Option<Box<dyn Iterator<Item = Value> + '_>> {
        let iter = self.iter()?;
        Some(Box::new(iter))
    }

    /// Part of #3978: FuncSetIterator (odometer) owns domain/codomain Vecs —
    /// no collection needed. Construct directly to avoid the borrowing `self.iter()`
    /// lifetime. This is the key win: [S -> T] with |T|^|S| elements generates
    /// them one-at-a-time via the odometer without pre-materializing.
    fn set_iter_owned(&self) -> Option<Box<dyn Iterator<Item = Value>>> {
        let domain_sorted = self.domain().to_sorted_set()?;
        let codomain_sorted = self.codomain().to_sorted_set()?;
        Some(Box::new(FuncSetIterator::from_elems(
            domain_sorted.iter().cloned().collect(),
            codomain_sorted.iter().cloned().collect(),
        )))
    }
}

// ==========================================================================
// Tier 1: RecordSetValue — own optimized methods
// to_sorted_set delegates to own optimized method
// ==========================================================================

impl LazySet for RecordSetValue {
    fn set_contains(&self, value: &Value) -> Option<bool> {
        self.contains(value)
    }

    fn to_sorted_set(&self) -> Option<SortedSet> {
        RecordSetValue::to_sorted_set(self)
    }

    fn set_len(&self) -> Option<BigInt> {
        self.len()
    }

    fn set_is_empty(&self) -> bool {
        self.is_empty()
    }

    fn set_iter(&self) -> Option<Box<dyn Iterator<Item = Value> + '_>> {
        let iter = self.iter()?;
        Some(Box::new(iter))
    }

    /// Part of #3978: RecordSetOwnedIterator owns clones of field set values,
    /// enabling streaming SetPred iteration without borrowing the source
    /// RecordSetValue. Clone cost is O(fields) not O(product).
    fn set_iter_owned(&self) -> Option<Box<dyn Iterator<Item = Value>>> {
        let iter = RecordSetOwnedIterator::new(self)?;
        Some(Box::new(iter))
    }
}

// ==========================================================================
// Tier 1: TupleSetValue — own optimized methods
// to_sorted_set delegates to own optimized method
// ==========================================================================

impl LazySet for TupleSetValue {
    fn set_contains(&self, value: &Value) -> Option<bool> {
        self.contains(value)
    }

    fn to_sorted_set(&self) -> Option<SortedSet> {
        TupleSetValue::to_sorted_set(self)
    }

    fn set_len(&self) -> Option<BigInt> {
        self.len()
    }

    fn set_is_empty(&self) -> bool {
        self.is_empty()
    }

    fn set_iter(&self) -> Option<Box<dyn Iterator<Item = Value> + '_>> {
        let iter = self.iter()?;
        Some(Box::new(iter))
    }

    /// Part of #3978: TupleSetOwnedIterator owns clones of component values,
    /// enabling streaming SetPred iteration without borrowing the source
    /// TupleSetValue. Clone cost is O(components) not O(product).
    fn set_iter_owned(&self) -> Option<Box<dyn Iterator<Item = Value>>> {
        let iter = TupleSetOwnedIterator::new(self)?;
        Some(Box::new(iter))
    }
}

// ==========================================================================
// Tier 1: KSubsetValue — own optimized methods
// to_sorted_set delegates to own optimized method
// ==========================================================================

impl LazySet for KSubsetValue {
    fn set_contains(&self, value: &Value) -> Option<bool> {
        self.contains(value)
    }

    fn to_sorted_set(&self) -> Option<SortedSet> {
        KSubsetValue::to_sorted_set(self)
    }

    fn set_len(&self) -> Option<BigInt> {
        self.len()
    }

    fn set_is_empty(&self) -> bool {
        self.is_empty()
    }

    fn set_iter(&self) -> Option<Box<dyn Iterator<Item = Value> + '_>> {
        let iter = self.iter()?;
        Some(Box::new(iter))
    }

    /// Part of #3978: KSubsetIterator owns its element Vec — construct directly
    /// to avoid the borrowing `self.iter()` method signature.
    fn set_iter_owned(&self) -> Option<Box<dyn Iterator<Item = Value>>> {
        let base_set = self.base().to_sorted_set()?;
        Some(Box::new(KSubsetIterator::new(base_set, self.k())))
    }

    fn is_enumerable(&self) -> bool {
        KSubsetValue::is_enumerable(self)
    }
}
