// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lazy compound set operations: sequence sets (`SeqSetValue`) and big union (`UnionValue`).
//!
//! Extracted from `set_ops.rs` as part of #2747 decomposition.

use super::super::*;
use super::set_binary_ops::all_in_set;

/// Lazy sequence set value representing Seq(S) - the set of all finite sequences over S
///
/// This is infinite in general, but supports membership checking:
/// v \in Seq(S) iff v is a sequence AND all elements of v are in S
#[derive(Clone)]
pub struct SeqSetValue {
    /// The base set S
    pub(crate) base: Box<Value>,
}

impl SeqSetValue {
    /// Create a new sequence set
    pub fn new(base: Value) -> Self {
        SeqSetValue {
            base: Box::new(base),
        }
    }

    pub fn base(&self) -> &Value {
        &self.base
    }

    /// Check if a value is in this sequence set
    /// v \in Seq(S) iff v is a sequence AND all elements are in S
    ///
    /// In TLA+, a sequence is a function from 1..n to some set.
    /// This means:
    /// - Value::Seq and Value::Tuple are explicit sequences
    /// - Value::IntFunc with domain 1..n is also a valid sequence
    /// - Value::Func with domain {1, 2, ..., n} is also a valid sequence
    ///
    /// # Returns
    ///
    /// `None` if base set membership is indeterminate (e.g. `SetPred` base).
    pub(crate) fn contains(&self, v: &Value) -> Option<bool> {
        match v {
            Value::Seq(seq) => {
                // All elements must be in the base set
                all_in_set(seq.iter(), &self.base)
            }
            Value::Tuple(elems) => {
                // All elements must be in the base set
                all_in_set(elems.iter(), &self.base)
            }
            // IntFunc with domain 1..n is a valid sequence
            Value::IntFunc(f) => {
                // Domain must start at 1 (sequence indexing in TLA+)
                if f.min != 1 {
                    return Some(false);
                }
                // All values must be in the base set
                all_in_set(f.values.iter(), &self.base)
            }
            // Func with domain {1, 2, ..., n} is a valid sequence
            Value::Func(f) => {
                if !f.domain_is_sequence() {
                    return Some(false);
                }
                all_in_set(f.mapping_values(), &self.base)
            }
            _ => Some(false),
        }
    }
}

impl fmt::Debug for SeqSetValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SeqSet({:?})", self.base)
    }
}

impl Ord for SeqSetValue {
    fn cmp(&self, other: &Self) -> Ordering {
        if std::ptr::eq(self.base.as_ref(), other.base.as_ref()) {
            return Ordering::Equal;
        }
        self.base.cmp(&other.base)
    }
}

impl PartialOrd for SeqSetValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for SeqSetValue {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.base.as_ref(), other.base.as_ref()) || self.cmp(other) == Ordering::Equal
    }
}

impl Eq for SeqSetValue {}

impl Hash for SeqSetValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        "SeqSet".hash(state);
        self.base.hash(state);
    }
}

/// Lazy big union value representing UNION S without allocating all elements
///
/// This is a performance optimization for membership checking.
/// Membership check: x \in UNION S iff exists s \in S : x \in s
#[derive(Clone)]
pub struct UnionValue {
    /// The set of sets S
    pub(crate) set: Box<Value>,
}

impl UnionValue {
    /// Create a new lazy big union
    pub fn new(set: Value) -> Self {
        UnionValue { set: Box::new(set) }
    }

    pub fn set(&self) -> &Value {
        &self.set
    }

    /// Check if a value is in this union
    /// v \in UNION S iff exists s \in S : v \in s
    pub(crate) fn contains(&self, v: &Value) -> Option<bool> {
        // Need to enumerate the outer set
        let iter = self.set.iter_set()?;
        let mut any_indeterminate = false;
        for inner_set in iter {
            match inner_set.set_contains(v) {
                Some(true) => return Some(true),
                Some(false) => {}
                None => any_indeterminate = true,
            }
        }
        if any_indeterminate {
            None
        } else {
            Some(false)
        }
    }

    /// Check if enumerable (outer set and all inner sets must be enumerable)
    #[allow(dead_code)] // called via Value enum dispatch
    pub(crate) fn is_enumerable(&self) -> bool {
        if let Some(iter) = self.set.iter_set() {
            for inner_set in iter {
                if inner_set.iter_set().is_none() {
                    return false;
                }
            }
            true
        } else {
            false
        }
    }

    /// Check if empty
    #[allow(dead_code)] // called via Value enum dispatch
    pub(crate) fn is_empty(&self) -> bool {
        // Empty if outer is empty, or all inner sets are empty
        if let Some(iter) = self.set.iter_set() {
            for inner_set in iter {
                if !inner_set.set_len().map_or(true, |n| n.is_zero()) {
                    return false;
                }
            }
            true
        } else {
            // Non-enumerable outer set - assume not empty
            false
        }
    }

    /// Materialize to a SortedSet with deferred normalization.
    ///
    /// #3073: Collects all inner set elements into a Vec and defers sort+dedup
    /// to the first observation that requires canonical order. For specs like
    /// MCBinarySearch (~488K elements), avoiding eager sort at materialization
    /// time saves O(n log n) when the result is used for membership testing
    /// (which uses linear scan on Unnormalized) before any ordered observation.
    pub fn to_sorted_set(&self) -> Option<SortedSet> {
        let iter = self.set.iter_set()?;
        let mut elements = Vec::new();
        for inner_set in iter {
            let inner_sorted = inner_set.to_sorted_set()?;
            // Use raw_iter to avoid forcing normalization of inner sets
            // when they are already Unnormalized
            elements.extend(inner_sorted.raw_iter().cloned());
        }
        Some(SortedSet::from_iter(elements))
    }
}

impl fmt::Debug for UnionValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Union({:?})", self.set)
    }
}

impl Ord for UnionValue {
    fn cmp(&self, other: &Self) -> Ordering {
        self.set.cmp(&other.set)
    }
}

impl PartialOrd for UnionValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for UnionValue {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for UnionValue {}

impl Hash for UnionValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        "Union".hash(state);
        self.set.hash(state);
    }
}
