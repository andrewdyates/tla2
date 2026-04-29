// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TupleSetValue (S1 \X S2 \X ...) and TupleSetIterator.

use super::super::*;

/// A lazy tuple set value representing S1 \X S2 \X ... without allocating all tuples.
///
/// This is a performance optimization for large cartesian products.
/// Membership check: t \in S1 \X S2 \X ... <==> t is a tuple of the right length and
/// for each index i, `t[i] \in components[i]`.
#[derive(Clone, Debug)]
pub struct TupleSetValue {
    /// Component sets in order
    #[allow(clippy::vec_box)]
    // Box<Value> is intentional: uniform with other compound set types
    pub(crate) components: Vec<Box<Value>>,
}

impl TupleSetValue {
    /// Create a new tuple set (cartesian product) from component sets.
    pub fn new(components: impl IntoIterator<Item = Value>) -> Self {
        TupleSetValue {
            components: components.into_iter().map(Box::new).collect(),
        }
    }

    pub fn components_len(&self) -> usize {
        self.components.len()
    }

    pub fn components_iter(&self) -> impl Iterator<Item = &Value> + '_ {
        self.components.iter().map(Box::as_ref)
    }

    /// Check if a value is contained in this tuple set.
    /// `t \in S1 \X S2 \X ...` iff t is a tuple of the right length and `t[i] \in components[i]`.
    /// Returns None if component set membership is indeterminate (e.g. SetPred component).
    pub(crate) fn contains(&self, v: &Value) -> Option<bool> {
        let Value::Tuple(elems) = v else {
            return Some(false);
        };

        if elems.len() != self.components.len() {
            return Some(false);
        }

        for (elem, set) in elems.iter().zip(self.components.iter()) {
            if !set.set_contains(elem)? {
                return Some(false);
            }
        }

        Some(true)
    }

    /// Get the cardinality of the tuple set: Π |Si| for each component i.
    pub(crate) fn len(&self) -> Option<BigInt> {
        let mut total = BigInt::one();
        for set in &self.components {
            let n = set.set_len()?;
            total *= n;
        }
        Some(total)
    }

    /// Check if the tuple set is empty.
    pub(crate) fn is_empty(&self) -> bool {
        // Empty if any component is empty
        self.components
            .iter()
            .any(|c| c.set_len().map_or(true, |n| n.is_zero()))
    }

    /// Materialize to a SortedSet via direct iteration.
    ///
    /// This keeps tuple-set enumeration on the contiguous `SortedSet` path
    /// instead of inserting each tuple into an `OrdSet` B-tree first.
    pub fn to_sorted_set(&self) -> Option<SortedSet> {
        let iter = self.iter()?;
        Some(SortedSet::from_iter(iter))
    }

    /// Iterate over all tuples in the tuple set.
    pub(crate) fn iter(&self) -> Option<TupleSetIterator<'_>> {
        TupleSetIterator::new(self)
    }
}

impl Ord for TupleSetValue {
    fn cmp(&self, other: &Self) -> Ordering {
        // Two empty tuple sets are equal regardless of their component structure
        // e.g., {} \X {1,2} == {1,2} \X {} == {}
        let self_empty = self.is_empty();
        let other_empty = other.is_empty();
        match (self_empty, other_empty) {
            (true, true) => return Ordering::Equal,
            (true, false) => return Ordering::Less,
            (false, true) => return Ordering::Greater,
            (false, false) => {}
        }

        // Compare by length first, then element-wise
        match self.components.len().cmp(&other.components.len()) {
            Ordering::Equal => {
                for (a, b) in self.components.iter().zip(other.components.iter()) {
                    match a.cmp(b) {
                        Ordering::Equal => {}
                        ord => return ord,
                    }
                }
                Ordering::Equal
            }
            ord => ord,
        }
    }
}

impl PartialOrd for TupleSetValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for TupleSetValue {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for TupleSetValue {}

impl Hash for TupleSetValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.components.len().hash(state);
        for c in &self.components {
            c.hash(state);
        }
    }
}

/// Iterator over tuple set elements, generated in lexicographic order.
pub(crate) struct TupleSetIterator<'a> {
    components: &'a [Box<Value>],
    iters: Vec<Box<dyn Iterator<Item = Value> + 'a>>,
    current: Vec<Value>,
    done: bool,
}

impl<'a> TupleSetIterator<'a> {
    fn new(tuple_set: &'a TupleSetValue) -> Option<Self> {
        if tuple_set.components.is_empty() {
            // Empty product: single empty tuple
            return Some(TupleSetIterator {
                components: &tuple_set.components,
                iters: Vec::new(),
                current: Vec::new(),
                done: false,
            });
        }

        let mut iters = Vec::with_capacity(tuple_set.components.len());
        let mut current = Vec::with_capacity(tuple_set.components.len());

        for set in &tuple_set.components {
            let mut iter = set.iter_set()?;
            match iter.next() {
                Some(first) => {
                    current.push(first);
                    iters.push(iter);
                }
                None => {
                    // Empty component set => empty tuple set.
                    return Some(TupleSetIterator {
                        components: &tuple_set.components,
                        iters: Vec::new(),
                        current: Vec::new(),
                        done: true,
                    });
                }
            }
        }

        Some(TupleSetIterator {
            components: &tuple_set.components,
            iters,
            current,
            done: false,
        })
    }
}

/// Owned iterator over tuple set elements for streaming SetPred iteration.
///
/// Part of #3978: Unlike `TupleSetIterator<'a>` which borrows component sets,
/// this iterator owns clones of the component values. This enables
/// `set_iter_owned()` to return an iterator that outlives the source value
/// reference, which is required by `SetPredStreamIter` for streaming evaluation.
///
/// The owned components are only the component sets (e.g., {1,2} and {"a","b"}),
/// not the full cartesian product, so the clone cost is O(components) not O(product).
pub(crate) struct TupleSetOwnedIterator {
    components: Vec<Value>,
    iters: Vec<Box<dyn Iterator<Item = Value>>>,
    current: Vec<Value>,
    done: bool,
}

impl TupleSetOwnedIterator {
    pub(crate) fn new(tuple_set: &TupleSetValue) -> Option<Self> {
        let components: Vec<Value> = tuple_set.components.iter().map(|b| (**b).clone()).collect();

        if components.is_empty() {
            return Some(TupleSetOwnedIterator {
                components,
                iters: Vec::new(),
                current: Vec::new(),
                done: false,
            });
        }

        let mut iters: Vec<Box<dyn Iterator<Item = Value>>> = Vec::with_capacity(components.len());
        let mut current = Vec::with_capacity(components.len());

        for set in &components {
            let mut iter = set.iter_set_owned()?;
            match iter.next() {
                Some(first) => {
                    current.push(first);
                    iters.push(iter);
                }
                None => {
                    return Some(TupleSetOwnedIterator {
                        components,
                        iters: Vec::new(),
                        current: Vec::new(),
                        done: true,
                    });
                }
            }
        }

        Some(TupleSetOwnedIterator {
            components,
            iters,
            current,
            done: false,
        })
    }
}

impl Iterator for TupleSetIterator<'_> {
    type Item = Value;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        // Special case: empty component list produces one empty tuple.
        if self.components.is_empty() {
            self.done = true;
            return Some(Value::Tuple(Vec::new().into()));
        }

        // Build the current tuple.
        let out = Value::Tuple(self.current.clone().into());

        // Advance the mixed-radix counter (last component changes fastest).
        for idx in (0..self.components.len()).rev() {
            if let Some(next_val) = self.iters.get_mut(idx).and_then(std::iter::Iterator::next) {
                self.current[idx] = next_val;

                // Reset all less-significant components to their first element.
                for j in (idx + 1)..self.components.len() {
                    let Some(mut iter) = self.components[j].iter_set() else {
                        self.done = true;
                        return Some(out);
                    };
                    let Some(first) = iter.next() else {
                        self.done = true;
                        return Some(out);
                    };
                    self.current[j] = first;
                    self.iters[j] = iter;
                }

                return Some(out);
            }

            // Carry: reset this component to its first element and continue.
            let Some(mut iter) = self.components[idx].iter_set() else {
                self.done = true;
                return Some(out);
            };
            let Some(first) = iter.next() else {
                self.done = true;
                return Some(out);
            };
            self.current[idx] = first;
            self.iters[idx] = iter;
        }

        // Exhausted all components: this was the last element.
        self.done = true;
        Some(out)
    }
}

impl Iterator for TupleSetOwnedIterator {
    type Item = Value;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        if self.components.is_empty() {
            self.done = true;
            return Some(Value::Tuple(Vec::new().into()));
        }

        let out = Value::Tuple(self.current.clone().into());

        for idx in (0..self.components.len()).rev() {
            if let Some(next_val) = self.iters.get_mut(idx).and_then(std::iter::Iterator::next) {
                self.current[idx] = next_val;

                for j in (idx + 1)..self.components.len() {
                    let Some(mut iter) = self.components[j].iter_set_owned() else {
                        self.done = true;
                        return Some(out);
                    };
                    let Some(first) = iter.next() else {
                        self.done = true;
                        return Some(out);
                    };
                    self.current[j] = first;
                    self.iters[j] = iter;
                }

                return Some(out);
            }

            let Some(mut iter) = self.components[idx].iter_set_owned() else {
                self.done = true;
                return Some(out);
            };
            let Some(first) = iter.next() else {
                self.done = true;
                return Some(out);
            };
            self.current[idx] = first;
            self.iters[idx] = iter;
        }

        self.done = true;
        Some(out)
    }
}
