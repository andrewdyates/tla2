// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lazy set intersection (`SetCapValue`).

use super::super::super::*;
use super::helpers::filter_to_vec;

/// Lazy set intersection (S1 \cap S2)
///
/// Membership is computed lazily: v \in S1 \cap S2 iff v \in S1 AND v \in S2
/// Enumeration happens by iterating the smaller enumerable set (if any) and filtering.
#[derive(Clone)]
pub struct SetCapValue {
    pub(crate) set1: Box<Value>,
    pub(crate) set2: Box<Value>,
}

impl SetCapValue {
    /// Create a new lazy set intersection
    pub fn new(set1: Value, set2: Value) -> Self {
        SetCapValue {
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

    /// Check if a value is in this intersection
    /// v \in S1 \cap S2 iff v \in S1 AND v \in S2
    /// Returns None if membership cannot be determined (e.g. SetPred operand).
    pub(crate) fn contains(&self, v: &Value) -> Option<bool> {
        let in1 = self.set1.set_contains(v)?;
        if !in1 {
            return Some(false);
        }
        self.set2.set_contains(v)
    }

    /// Check if the intersection is enumerable (at least one operand must be enumerable)
    #[allow(dead_code)] // called via Value enum dispatch
    pub(crate) fn is_enumerable(&self) -> bool {
        self.set1.iter_set().is_some() || self.set2.iter_set().is_some()
    }

    /// Check if the set is empty
    #[allow(dead_code)] // called via Value enum dispatch
    pub(crate) fn is_empty(&self) -> bool {
        // Check if either operand is empty (which makes intersection empty)
        let e1 = self.set1.set_len().is_some_and(|n| n.is_zero());
        let e2 = self.set2.set_len().is_some_and(|n| n.is_zero());
        if e1 || e2 {
            return true;
        }
        // Otherwise, we can only know by enumerating
        self.to_sorted_set().is_some_and(|s| s.is_empty())
    }

    /// Materialize to a SortedSet via filtered Vec (avoids im::OrdSet overhead).
    ///
    /// Phase 1A (#3073): Filters elements into a Vec, then defers normalization
    /// to `SortedSet::from_iter()` when the source iterator is not already ordered.
    pub fn to_sorted_set(&self) -> Option<SortedSet> {
        // Prefer to iterate the smaller set if both are enumerable
        let iter1 = self.set1.iter_set();
        let iter2 = self.set2.iter_set();

        let filtered = match (iter1, iter2) {
            (Some(it1), Some(it2)) => {
                // Both enumerable - choose smaller one to iterate
                let len1 = self.set1.set_len();
                let len2 = self.set2.set_len();
                match (len1, len2) {
                    (Some(l1), Some(l2)) if l1 <= l2 => {
                        filter_to_vec(it1, |v| self.set2.set_contains(v))
                    }
                    (Some(_), Some(_)) => filter_to_vec(it2, |v| self.set1.set_contains(v)),
                    // Unknown lengths - just use set1
                    _ => filter_to_vec(it1, |v| self.set2.set_contains(v)),
                }
            }
            (Some(it), None) => {
                // Only set1 enumerable - iterate it, filter by set2 membership
                filter_to_vec(it, |v| self.set2.set_contains(v))
            }
            (None, Some(it)) => {
                // Only set2 enumerable - iterate it, filter by set1 membership
                filter_to_vec(it, |v| self.set1.set_contains(v))
            }
            (None, None) => {
                // Neither enumerable - cannot compute
                None
            }
        };
        filtered.map(SortedSet::from_iter)
    }
}

impl fmt::Debug for SetCapValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SetCap({:?}, {:?})", self.set1, self.set2)
    }
}

impl Ord for SetCapValue {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.set1.cmp(&other.set1) {
            Ordering::Equal => self.set2.cmp(&other.set2),
            ord => ord,
        }
    }
}

impl PartialOrd for SetCapValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for SetCapValue {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for SetCapValue {}

impl Hash for SetCapValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        "SetCap".hash(state);
        self.set1.hash(state);
        self.set2.hash(state);
    }
}
