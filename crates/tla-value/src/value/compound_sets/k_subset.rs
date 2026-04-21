// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! KSubsetValue (k-element subsets of S) and KSubsetIterator.

use super::super::*;

/// Lazy k-subset value representing Ksubsets(S, k) without allocating all C(n,k) subsets
///
/// This is a performance optimization that allows membership checking without enumeration.
/// Membership check: x \in Ksubsets(S, k) iff x is a set with |x| = k and x \subseteq S
#[derive(Clone)]
pub struct KSubsetValue {
    /// The base set S
    pub(crate) base: Box<Value>,
    /// The subset size k
    pub(crate) k: usize,
}

impl KSubsetValue {
    /// Create a new k-subset set
    pub fn new(base: Value, k: usize) -> Self {
        KSubsetValue {
            base: Box::new(base),
            k,
        }
    }

    pub fn base(&self) -> &Value {
        &self.base
    }

    pub fn k(&self) -> usize {
        self.k
    }

    /// Check if a value is in this k-subset set
    /// v \in Ksubsets(S, k) iff v is a set with |v| = k and v \subseteq S
    /// Returns None if base set membership is indeterminate (e.g. SetPred base).
    pub(crate) fn contains(&self, v: &Value) -> Option<bool> {
        // Must be a set with exactly k elements
        if let Some(set) = v.to_sorted_set() {
            if set.len() != self.k {
                return Some(false);
            }
            // All elements must be in base
            for elem in &set {
                if !self.base.set_contains(elem)? {
                    return Some(false);
                }
            }
            Some(true)
        } else {
            Some(false)
        }
    }

    /// Check if enumerable (base must be enumerable)
    #[allow(dead_code)] // called via Value enum dispatch
    pub(crate) fn is_enumerable(&self) -> bool {
        self.base.iter_set().is_some()
    }

    /// Get the cardinality: C(n, k) = n! / (k! * (n-k)!)
    pub(crate) fn len(&self) -> Option<BigInt> {
        let n = self.base.set_len()?.to_usize()?;
        if self.k > n {
            return Some(BigInt::zero());
        }
        Some(binomial(n, self.k))
    }

    /// Check if empty
    #[allow(dead_code)] // called via Value enum dispatch
    pub(crate) fn is_empty(&self) -> bool {
        self.len().is_some_and(|n| n.is_zero())
    }

    /// Materialize to a SortedSet via direct iteration.
    ///
    /// This avoids building an intermediate `OrdSet` while generating all
    /// subsets. The final `SortedSet` normalizes only once when needed.
    pub fn to_sorted_set(&self) -> Option<SortedSet> {
        let iter = self.iter()?;
        Some(SortedSet::from_iter(iter))
    }

    /// Iterate over all k-subsets
    pub fn iter(&self) -> Option<impl Iterator<Item = Value> + '_> {
        let base_set = self.base.to_sorted_set()?;
        Some(KSubsetIterator::new(base_set, self.k))
    }
}

/// Iterator over k-element subsets
pub(crate) struct KSubsetIterator {
    elements: Vec<Value>,
    indices: Vec<usize>,
    k: usize,
    n: usize,
    done: bool,
    /// Part of #3364: See SubsetIterator::elements_cmp_sorted for rationale.
    elements_cmp_sorted: bool,
}

impl KSubsetIterator {
    /// Create a new KSubsetIterator over all k-element subsets of the given set.
    pub fn new(base: SortedSet, k: usize) -> Self {
        let elements: Vec<Value> = base.iter().cloned().collect();
        let n = elements.len();
        let done = k > n;
        KSubsetIterator {
            elements,
            indices: if k <= n { (0..k).collect() } else { vec![] },
            k,
            n,
            done,
            elements_cmp_sorted: true,
        }
    }

    pub(in crate::value) fn from_elements(elements: Vec<Value>, k: usize) -> Self {
        let n = elements.len();
        let done = k > n;
        KSubsetIterator {
            elements,
            indices: if k <= n { (0..k).collect() } else { vec![] },
            k,
            n,
            done,
            elements_cmp_sorted: false,
        }
    }
}

impl Iterator for KSubsetIterator {
    type Item = Value;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        // Special case k=0: return empty set once
        if self.k == 0 {
            self.done = true;
            return Some(Value::empty_set());
        }

        // Part of #3364: Use from_sorted_vec to avoid double allocation.
        // See SubsetIterator::next() for full rationale.
        let mut subset: Vec<Value> = self
            .indices
            .iter()
            .map(|&i| self.elements[i].clone())
            .collect();
        if !self.elements_cmp_sorted {
            subset.sort();
        }
        let result = Value::from_sorted_set(SortedSet::from_sorted_vec(subset));

        // Find rightmost index that can be incremented
        let mut i = self.k;
        while i > 0 {
            i -= 1;
            if self.indices[i] < self.n - self.k + i {
                break;
            }
        }
        if i == 0 && self.indices[0] >= self.n - self.k {
            self.done = true;
            return Some(result);
        }

        // Increment and reset subsequent indices
        self.indices[i] += 1;
        for j in (i + 1)..self.k {
            self.indices[j] = self.indices[j - 1] + 1;
        }

        Some(result)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.done {
            return (0, Some(0));
        }
        // Approximate: we can compute exact but it's complex
        (0, None)
    }
}

impl fmt::Debug for KSubsetValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "KSubset({:?}, {})", self.base, self.k)
    }
}

impl Ord for KSubsetValue {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.k.cmp(&other.k) {
            Ordering::Equal => self.base.cmp(&other.base),
            ord => ord,
        }
    }
}

impl PartialOrd for KSubsetValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for KSubsetValue {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for KSubsetValue {}

impl Hash for KSubsetValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        "KSubset".hash(state);
        self.k.hash(state);
        self.base.hash(state);
    }
}

/// Compute binomial coefficient C(n, k) = n! / (k! * (n-k)!)
pub(in crate::value) fn binomial(n: usize, k: usize) -> BigInt {
    if k > n {
        return BigInt::zero();
    }
    if k == 0 || k == n {
        return BigInt::one();
    }
    // Use smaller k for efficiency: C(n, k) = C(n, n-k)
    let k = k.min(n - k);
    let mut result = BigInt::one();
    for i in 0..k {
        result = result * BigInt::from(n - i) / BigInt::from(i + 1);
    }
    result
}
