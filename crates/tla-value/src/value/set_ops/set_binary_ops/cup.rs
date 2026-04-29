// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lazy set union (`SetCupValue`).

use super::super::super::*;

/// Lazy set union (S1 \cup S2)
///
/// Membership is computed lazily: v \in S1 \cup S2 iff v \in S1 OR v \in S2
/// Enumeration only happens when both operands are enumerable.
#[derive(Clone)]
pub struct SetCupValue {
    pub(crate) set1: Box<Value>,
    pub(crate) set2: Box<Value>,
}

impl SetCupValue {
    /// Create a new lazy set union
    pub fn new(set1: Value, set2: Value) -> Self {
        SetCupValue {
            set1: Box::new(set1),
            set2: Box::new(set2),
        }
    }

    pub fn set1(&self) -> &Value {
        &self.set1
    }

    pub fn set2(&self) -> &Value {
        &self.set2
    }

    /// Check if a value is in this union set
    /// v \in S1 \cup S2 iff v \in S1 OR v \in S2
    /// Returns None if membership cannot be determined (e.g. SetPred operand).
    pub(crate) fn contains(&self, v: &Value) -> Option<bool> {
        let in1 = self.set1.set_contains(v)?;
        if in1 {
            return Some(true);
        }
        self.set2.set_contains(v)
    }

    /// Check if the union is enumerable (both operands must be enumerable)
    #[allow(dead_code)] // called via Value enum dispatch
    pub(crate) fn is_enumerable(&self) -> bool {
        self.set1.iter_set().is_some() && self.set2.iter_set().is_some()
    }

    /// Check if the set is empty
    #[allow(dead_code)] // called via Value enum dispatch
    pub(crate) fn is_empty(&self) -> bool {
        // Empty iff both operands are empty
        let e1 = self.set1.set_len().is_some_and(|n| n.is_zero());
        let e2 = self.set2.set_len().is_some_and(|n| n.is_zero());
        e1 && e2
    }

    /// Materialize to a SortedSet with deferred normalization.
    ///
    /// #3073: Collects both operands' iterators into a Vec and defers sort+dedup
    /// to the first observation that requires canonical order (fingerprinting,
    /// comparison, iteration). This matches TLC's `SetEnumValue(vals, false)`.
    pub fn to_sorted_set(&self) -> Option<SortedSet> {
        let iter1 = self.set1.iter_set()?;
        let iter2 = self.set2.iter_set()?;
        Some(SortedSet::from_iter(iter1.chain(iter2)))
    }
}

impl fmt::Debug for SetCupValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SetCup({:?}, {:?})", self.set1, self.set2)
    }
}

impl Ord for SetCupValue {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.set1.cmp(&other.set1) {
            Ordering::Equal => self.set2.cmp(&other.set2),
            ord => ord,
        }
    }
}

impl PartialOrd for SetCupValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for SetCupValue {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for SetCupValue {}

impl Hash for SetCupValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        "SetCup".hash(state);
        self.set1.hash(state);
        self.set2.hash(state);
    }
}
