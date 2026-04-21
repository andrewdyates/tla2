// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SubsetValue (powerset) and SubsetIterator.

use super::super::*;

/// A lazy powerset value representing SUBSET S without allocating all 2^|S| elements
///
/// This is a performance optimization for large powersets.
/// Membership check: x \in SUBSET S <==> x \subseteq S
#[derive(Clone, Debug)]
pub struct SubsetValue {
    /// The base set S (can be Set, Interval, or Subset)
    pub(crate) base: Box<Value>,
}

impl SubsetValue {
    /// Create a new powerset of the given set
    pub fn new(base: Value) -> Self {
        SubsetValue {
            base: Box::new(base),
        }
    }

    pub fn base(&self) -> &Value {
        &self.base
    }

    /// Check if a value is contained in this powerset (i.e., is a subset of base)
    /// Returns None if membership in the base set is indeterminate (e.g. SetPred base).
    pub(crate) fn contains(&self, v: &Value) -> Option<bool> {
        // v \in SUBSET S <==> v is a set AND v \subseteq S
        if let Some(iter) = v.iter_set() {
            for elem in iter {
                if !self.base.set_contains(&elem)? {
                    return Some(false);
                }
            }
            Some(true)
        } else {
            Some(false)
        }
    }

    /// Get the cardinality of the powerset: 2^|base|
    pub(crate) fn len(&self) -> Option<BigInt> {
        let base_len = self.base.set_len()?;
        // 2^base_len - be careful about very large sets
        base_len.to_u32().map(|n| BigInt::from(1u64) << n)
    }

    /// Check if the powerset is empty (only if base is invalid)
    #[allow(dead_code)] // called via Value enum dispatch
    pub(crate) fn is_empty(&self) -> bool {
        // SUBSET S always contains {} (the empty set)
        false
    }

    /// Convert to an eager SortedSet (use sparingly for large powersets)
    pub(crate) fn to_sorted_set(&self) -> Option<SortedSet> {
        let base_set = self.base.to_sorted_set()?;
        Some(powerset_eager(&base_set))
    }

    /// Iterate over all elements of the powerset
    pub fn iter(&self) -> Option<impl Iterator<Item = Value> + '_> {
        let base_set = self.base.to_sorted_set()?;
        Some(SubsetIterator::new(base_set))
    }
}

/// Iterator over powerset elements
pub(crate) struct SubsetIterator {
    elements: Vec<Value>,
    n: usize,
    k: usize,
    indices: Vec<usize>,
    returned_empty: bool,
    done: bool,
    /// Part of #3364: When true, elements are in Value::cmp order (from
    /// SortedSet::iter()) so subsets drawn with ascending indices are already
    /// sorted — use from_sorted_vec to skip the double allocation.
    /// When false (from_elements with TLC-normalized order), subsets must be
    /// sorted before from_sorted_vec or use the original from_iter path.
    elements_cmp_sorted: bool,
}

impl SubsetIterator {
    /// Create a new SubsetIterator over all subsets of the given base set.
    pub fn new(base: SortedSet) -> Self {
        let elements: Vec<Value> = base.iter().cloned().collect();
        let n = elements.len();
        SubsetIterator {
            elements,
            n,
            k: 0,
            indices: Vec::new(),
            returned_empty: false,
            done: false,
            elements_cmp_sorted: true,
        }
    }

    pub(in crate::value) fn from_elements(elements: Vec<Value>) -> Self {
        let n = elements.len();
        SubsetIterator {
            elements,
            n,
            k: 0,
            indices: Vec::new(),
            returned_empty: false,
            done: false,
            elements_cmp_sorted: false,
        }
    }
}

impl Iterator for SubsetIterator {
    type Item = Value;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        // TLC's normalized powerset enumeration is cardinality-first:
        //   {} ; all 1-subsets ; all 2-subsets ; ... ; all n-subsets.
        if !self.returned_empty {
            self.returned_empty = true;
            if self.n == 0 {
                self.done = true;
            } else {
                self.k = 1;
                self.indices = vec![0];
            }
            return Some(Value::empty_set());
        }

        debug_assert!(self.k > 0);

        // Part of #3364: Use from_sorted_vec when elements are in Value::cmp
        // order to avoid the double allocation in the from_unnormalized_vec →
        // normalized_elements_from_raw lazy path (was 28.8% of total dhat
        // blocks on bosco 20k sample).  When elements are TLC-normalized
        // (from_elements path), sort the small subset first — the sort cost
        // on 2–8 elements is negligible vs the saved Arc allocation.
        let mut subset: Vec<Value> = self
            .indices
            .iter()
            .map(|&i| self.elements[i].clone())
            .collect();
        if !self.elements_cmp_sorted {
            subset.sort();
        }
        let result = Value::from_sorted_set(SortedSet::from_sorted_vec(subset));

        let mut i = self.k;
        while i > 0 {
            i -= 1;
            if self.indices[i] < self.n - self.k + i {
                break;
            }
        }

        if i == 0 && self.indices[0] >= self.n - self.k {
            self.k += 1;
            if self.k > self.n {
                self.done = true;
                self.indices.clear();
            } else {
                self.indices = (0..self.k).collect();
            }
            return Some(result);
        }

        self.indices[i] += 1;
        for j in (i + 1)..self.k {
            self.indices[j] = self.indices[j - 1] + 1;
        }

        Some(result)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl PartialEq for SubsetValue {
    fn eq(&self, other: &Self) -> bool {
        self.base == other.base
    }
}

impl Eq for SubsetValue {}

impl Hash for SubsetValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.base.hash(state);
    }
}

impl Ord for SubsetValue {
    fn cmp(&self, other: &Self) -> Ordering {
        self.base.cmp(&other.base)
    }
}

impl PartialOrd for SubsetValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Helper function to compute powerset eagerly (for SubsetValue::to_ord_set)
fn powerset_eager(set: &SortedSet) -> SortedSet {
    let mut result = SetBuilder::new();
    let elements: Vec<_> = set.iter().cloned().collect();
    let n = elements.len();
    let count = if n >= 64 { u64::MAX } else { 1u64 << n };

    for i in 0..count {
        // Elements are selected from a sorted source in ascending index order,
        // so the subset vec is already sorted and duplicate-free.
        let subset: Vec<Value> = elements
            .iter()
            .enumerate()
            .filter(|&(j, _)| i & (1u64 << j) != 0)
            .map(|(_, elem)| elem.clone())
            .collect();
        result.insert(Value::from_sorted_set(SortedSet::from_sorted_vec(subset)));
    }
    result.build()
}
