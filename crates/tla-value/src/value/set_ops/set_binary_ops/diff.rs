// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lazy set difference (`SetDiffValue`).

use super::super::super::*;
use super::helpers::filter_to_vec;

/// Lazy set difference (S1 \ S2)
///
/// Membership is computed lazily: v \in S1 \ S2 iff v \in S1 AND v \notin S2
/// Enumeration happens by iterating S1 (if enumerable) and filtering out S2 members.
#[derive(Clone)]
pub struct SetDiffValue {
    pub(crate) set1: Box<Value>,
    pub(crate) set2: Box<Value>,
}

impl SetDiffValue {
    /// Create a new lazy set difference
    pub fn new(set1: Value, set2: Value) -> Self {
        SetDiffValue {
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

    /// Check if a value is in this set difference
    /// v \in S1 \ S2 iff v \in S1 AND v \notin S2
    /// Returns None if membership cannot be determined (e.g. SetPred operand).
    pub(crate) fn contains(&self, v: &Value) -> Option<bool> {
        let in1 = self.set1.set_contains(v)?;
        if !in1 {
            return Some(false);
        }
        Some(!self.set2.set_contains(v)?)
    }

    /// Check if the difference is enumerable (LHS must be enumerable)
    #[allow(dead_code)] // called via Value enum dispatch
    pub(crate) fn is_enumerable(&self) -> bool {
        self.set1.iter_set().is_some()
    }

    /// Check if the set is empty
    #[allow(dead_code)] // called via Value enum dispatch
    pub(crate) fn is_empty(&self) -> bool {
        // Empty if LHS is empty
        let e1 = self.set1.set_len().is_some_and(|n| n.is_zero());
        if e1 {
            return true;
        }
        // Otherwise, check by enumeration if possible
        self.to_sorted_set().is_some_and(|s| s.is_empty())
    }

    /// Materialize to a SortedSet via filtered Vec (avoids im::OrdSet overhead).
    ///
    /// Phase 1A (#3073): Filters LHS elements into a Vec, then defers normalization
    /// to `SortedSet::from_iter()` when the source iterator is not already ordered.
    pub fn to_sorted_set(&self) -> Option<SortedSet> {
        let iter = self.set1.iter_set()?;
        filter_to_vec(iter, |v| self.set2.set_contains(v).map(|b| !b)).map(SortedSet::from_iter)
    }
}

impl fmt::Debug for SetDiffValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SetDiff({:?}, {:?})", self.set1, self.set2)
    }
}

impl Ord for SetDiffValue {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.set1.cmp(&other.set1) {
            Ordering::Equal => self.set2.cmp(&other.set2),
            ord => ord,
        }
    }
}

impl PartialOrd for SetDiffValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for SetDiffValue {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for SetDiffValue {}

impl Hash for SetDiffValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        "SetDiff".hash(state);
        self.set1.hash(state);
        self.set2.hash(state);
    }
}
