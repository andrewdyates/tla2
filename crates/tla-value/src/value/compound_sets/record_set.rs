// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RecordSetValue ([a: S, b: T, ...]) and RecordSetIterator.

use super::super::*;
use std::collections::BTreeMap;
use tla_core::{intern_name, NameId};

/// A lazy record set value representing [a: S, b: T, ...] without allocating all records.
///
/// This is a performance optimization for large record sets.
/// Membership check: r \in [a: S, b: T] <==> r is a record with exactly those fields and
/// for each field name k, `r[k] \in fields[k]`.
///
/// Part of #3792: `check_order` stores field names sorted by ascending domain cardinality
/// so that `contains()` checks the most discriminating fields first. For message-type
/// unions like MultiPaxos `Messages`, the singleton "type" field (cardinality 1) is checked
/// before multi-valued fields like "bal" or "src", enabling early rejection in 4/5 branches.
#[derive(Clone, Debug)]
pub struct RecordSetValue {
    /// Field name -> allowed values set (BTreeMap for canonical Ord/Hash/Eq).
    pub(crate) fields: BTreeMap<Arc<str>, Box<Value>>,
    /// Field names sorted by ascending domain cardinality for membership checks.
    /// Singleton fields (cardinality 1) are checked first for maximal rejection power.
    /// Falls back to alphabetical order when cardinalities are equal or unknown.
    check_order: Box<[Arc<str>]>,
}

impl RecordSetValue {
    /// Create a new record set from (field_name, field_set) pairs.
    pub fn new(fields: impl IntoIterator<Item = (Arc<str>, Value)>) -> Self {
        let mut map = BTreeMap::new();
        for (name, set) in fields {
            map.insert(name, Box::new(set));
        }
        let check_order = Self::compute_check_order(&map);
        RecordSetValue {
            fields: map,
            check_order,
        }
    }

    /// Compute the field check order: ascending by domain cardinality, then alphabetical.
    /// Fields with unknown cardinality are placed last (treated as u64::MAX).
    fn compute_check_order(fields: &BTreeMap<Arc<str>, Box<Value>>) -> Box<[Arc<str>]> {
        use num_traits::ToPrimitive;
        let mut ordered: Vec<(Arc<str>, u64)> = fields
            .iter()
            .map(|(name, set)| {
                let card = set.set_len().and_then(|n| n.to_u64()).unwrap_or(u64::MAX);
                (name.clone(), card)
            })
            .collect();
        // Stable sort: equal cardinalities preserve BTreeMap (alphabetical) order.
        ordered.sort_by_key(|&(_, card)| card);
        ordered.into_iter().map(|(name, _)| name).collect()
    }

    pub fn fields_len(&self) -> usize {
        self.fields.len()
    }

    pub fn fields_iter(&self) -> impl Iterator<Item = (&Arc<str>, &Value)> + '_ {
        self.fields.iter().map(|(name, set)| (name, set.as_ref()))
    }

    /// Iterate fields in check order (ascending cardinality) for membership checks.
    /// Part of #3792: Matches the ordering used by `contains()`.
    pub fn fields_check_order_iter(&self) -> impl Iterator<Item = (&Arc<str>, &Value)> + '_ {
        self.check_order
            .iter()
            .map(|name| (name, self.fields[name.as_ref()].as_ref()))
    }

    /// Check if the record set is definitely empty.
    ///
    /// `[ ]` is **not** empty: it contains the empty record.
    /// Otherwise, the record set is empty if any field domain is known to be empty.
    pub(crate) fn is_empty(&self) -> bool {
        if self.fields.is_empty() {
            return false;
        }

        self.fields
            .iter()
            .any(|(_field, set)| set.set_len().is_some_and(|n| n.is_zero()))
    }

    /// Check if a value is contained in this record set.
    /// Returns None if field set membership is indeterminate (e.g. SetPred field set).
    ///
    /// Part of #3792: Iterates fields in `check_order` (ascending cardinality) rather than
    /// BTreeMap alphabetical order. For message-union specs like MultiPaxos, this checks
    /// the singleton "type" field first, enabling early rejection without testing
    /// multi-valued fields like "bal" or "src".
    pub(crate) fn contains(&self, v: &Value) -> Option<bool> {
        let Value::Record(rec) = v else {
            return Some(false);
        };

        if rec.len() != self.fields.len() {
            return Some(false);
        }

        for field in self.check_order.iter() {
            let set = &self.fields[field.as_ref()];
            let Some(field_val) = rec.get(field.as_ref()) else {
                return Some(false);
            };
            if !set.set_contains(field_val)? {
                return Some(false);
            }
        }

        Some(true)
    }

    /// Get the cardinality of the record set: Π |Si| for each field i.
    ///
    /// If any field set cardinality is unknown, returns None.
    pub(crate) fn len(&self) -> Option<BigInt> {
        let mut total = BigInt::one();
        for set in self.fields.values() {
            let n = set.set_len()?;
            total *= n;
        }
        Some(total)
    }

    /// Materialize to a SortedSet via direct iteration.
    ///
    /// This keeps record-set enumeration on the contiguous `SortedSet` path
    /// instead of inserting each record into an `OrdSet` B-tree first.
    pub fn to_sorted_set(&self) -> Option<SortedSet> {
        let iter = self.iter()?;
        Some(SortedSet::from_iter(iter))
    }

    /// Iterate over all records in the record set.
    pub(crate) fn iter(&self) -> Option<RecordSetIterator<'_>> {
        RecordSetIterator::new(self)
    }
}

impl Ord for RecordSetValue {
    fn cmp(&self, other: &Self) -> Ordering {
        // Two empty record sets are equal regardless of their field structure.
        // e.g., [a: {1}, b: {}] == [c: {2}, d: {}] == {}
        let self_empty = self.is_empty();
        let other_empty = other.is_empty();
        match (self_empty, other_empty) {
            (true, true) => return Ordering::Equal,
            (true, false) => return Ordering::Less,
            (false, true) => return Ordering::Greater,
            (false, false) => {}
        }

        self.fields.iter().cmp(other.fields.iter())
    }
}

impl PartialOrd for RecordSetValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for RecordSetValue {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for RecordSetValue {}

impl Hash for RecordSetValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash/Eq consistency: empty record sets compare equal regardless of field structure.
        // Hash the empty record set as an empty set (Value::Set({})) which contributes no
        // additional structure beyond the set-like discriminant already hashed by Value::hash.
        if self.is_empty() {
            return;
        }

        for (k, v) in &self.fields {
            k.hash(state);
            v.hash(state);
        }
    }
}

/// Iterator over record set elements, generated in lexicographic order by field name then value.
pub(crate) struct RecordSetIterator<'a> {
    field_sets: Vec<&'a Value>,
    record_fields: Vec<(NameId, usize)>,
    iters: Vec<Box<dyn Iterator<Item = Value> + 'a>>,
    current: Vec<Value>,
    done: bool,
}

impl<'a> RecordSetIterator<'a> {
    fn new(record_set: &'a RecordSetValue) -> Option<Self> {
        let mut field_sets = Vec::with_capacity(record_set.fields.len());
        let mut record_fields = Vec::with_capacity(record_set.fields.len());
        for (name, set) in &record_set.fields {
            let idx = field_sets.len();
            field_sets.push(set.as_ref());
            record_fields.push((intern_name(name), idx));
        }
        record_fields.sort_by_key(|(field_id, _)| *field_id);

        if field_sets.is_empty() {
            return Some(RecordSetIterator {
                field_sets,
                record_fields,
                iters: Vec::new(),
                current: Vec::new(),
                done: false,
            });
        }

        let mut iters = Vec::with_capacity(field_sets.len());
        let mut current = Vec::with_capacity(field_sets.len());

        for set in &field_sets {
            let mut iter = set.iter_set()?;
            match iter.next() {
                Some(first) => {
                    current.push(first);
                    iters.push(iter);
                }
                None => {
                    // Empty field set => empty record set.
                    return Some(RecordSetIterator {
                        field_sets,
                        record_fields,
                        iters: Vec::new(),
                        current: Vec::new(),
                        done: true,
                    });
                }
            }
        }

        Some(RecordSetIterator {
            field_sets,
            record_fields,
            iters,
            current,
            done: false,
        })
    }
}

/// Owned iterator over record set elements for streaming SetPred iteration.
///
/// Part of #3978: Unlike `RecordSetIterator<'a>` which borrows field sets from
/// the `RecordSetValue`, this iterator owns clones of the field set values. This
/// enables `set_iter_owned()` to return an iterator that outlives the source value
/// reference, which is required by `SetPredStreamIter` for streaming evaluation.
///
/// The owned field sets are only the component sets (e.g., {1,2} and {"a","b"}),
/// not the full cartesian product, so the clone cost is O(fields) not O(product).
pub(crate) struct RecordSetOwnedIterator {
    field_sets: Vec<Value>,
    record_fields: Vec<(NameId, usize)>,
    iters: Vec<Box<dyn Iterator<Item = Value>>>,
    current: Vec<Value>,
    done: bool,
}

impl RecordSetOwnedIterator {
    pub(crate) fn new(record_set: &RecordSetValue) -> Option<Self> {
        let mut field_sets = Vec::with_capacity(record_set.fields.len());
        let mut record_fields = Vec::with_capacity(record_set.fields.len());
        for (name, set) in &record_set.fields {
            let idx = field_sets.len();
            field_sets.push(set.as_ref().clone());
            record_fields.push((intern_name(name), idx));
        }
        record_fields.sort_by_key(|(field_id, _)| *field_id);

        if field_sets.is_empty() {
            return Some(RecordSetOwnedIterator {
                field_sets,
                record_fields,
                iters: Vec::new(),
                current: Vec::new(),
                done: false,
            });
        }

        let mut iters: Vec<Box<dyn Iterator<Item = Value>>> =
            Vec::with_capacity(field_sets.len());
        let mut current = Vec::with_capacity(field_sets.len());

        for set in &field_sets {
            let mut iter = set.iter_set_owned()?;
            match iter.next() {
                Some(first) => {
                    current.push(first);
                    iters.push(iter);
                }
                None => {
                    return Some(RecordSetOwnedIterator {
                        field_sets,
                        record_fields,
                        iters: Vec::new(),
                        current: Vec::new(),
                        done: true,
                    });
                }
            }
        }

        Some(RecordSetOwnedIterator {
            field_sets,
            record_fields,
            iters,
            current,
            done: false,
        })
    }
}

impl Iterator for RecordSetIterator<'_> {
    type Item = Value;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        // Special case: [ ] record set has one element: the empty record.
        if self.field_sets.is_empty() {
            self.done = true;
            return Some(Value::Record(RecordValue::new()));
        }

        // Build the current record in RecordValue's NameId-sorted layout.
        let mut entries = Vec::with_capacity(self.record_fields.len());
        for &(field_id, idx) in &self.record_fields {
            entries.push((field_id, self.current[idx].clone()));
        }
        let out = Value::Record(RecordValue::from_sorted_entries(entries));

        // Advance the mixed-radix counter (last field changes fastest).
        for idx in (0..self.field_sets.len()).rev() {
            if let Some(next_val) = self.iters.get_mut(idx).and_then(std::iter::Iterator::next) {
                self.current[idx] = next_val;

                // Reset all less-significant fields to their first element.
                for j in (idx + 1)..self.field_sets.len() {
                    let Some(mut iter) = self.field_sets[j].iter_set() else {
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

            // Carry: reset this field to its first element and continue to the next field.
            let Some(mut iter) = self.field_sets[idx].iter_set() else {
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

        // Exhausted all fields: this was the last element.
        self.done = true;
        Some(out)
    }
}

impl Iterator for RecordSetOwnedIterator {
    type Item = Value;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        if self.field_sets.is_empty() {
            self.done = true;
            return Some(Value::Record(RecordValue::new()));
        }

        let mut entries = Vec::with_capacity(self.record_fields.len());
        for &(field_id, idx) in &self.record_fields {
            entries.push((field_id, self.current[idx].clone()));
        }
        let out = Value::Record(RecordValue::from_sorted_entries(entries));

        for idx in (0..self.field_sets.len()).rev() {
            if let Some(next_val) = self.iters.get_mut(idx).and_then(std::iter::Iterator::next) {
                self.current[idx] = next_val;

                for j in (idx + 1)..self.field_sets.len() {
                    let Some(mut iter) = self.field_sets[j].iter_set_owned() else {
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

            let Some(mut iter) = self.field_sets[idx].iter_set_owned() else {
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
