// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RecordBuilder, trait impls, and RecordIter for RecordValue.
//!
//! Extracted from the former `record.rs` as part of #3309 to keep each file
//! under the 500-line target. `RecordValue` core type and methods now live in
//! `record/mod.rs`.

use super::record::RecordValue;
use super::Value;
use smallvec::SmallVec;
use std::sync::Arc;
use tla_core::{intern_name, resolve_name_id, NameId};

/// Builder for constructing RecordValue incrementally.
///
/// Collects field-value pairs and sorts them when building the final RecordValue.
///
/// Part of #3805: Uses SmallVec<[(NameId, Value); 6]> to avoid heap allocation for
/// records with <= 6 fields (the vast majority in TLA+ -- most state records have
/// 3-6 fields like `[pc, stack, x, y]`).
pub struct RecordBuilder {
    entries: SmallVec<[(NameId, Value); 6]>,
}

impl RecordBuilder {
    /// Create a new empty builder
    pub fn new() -> Self {
        RecordBuilder {
            entries: SmallVec::new(),
        }
    }

    /// Create a new builder with pre-allocated capacity
    pub fn with_capacity(capacity: usize) -> Self {
        RecordBuilder {
            entries: SmallVec::with_capacity(capacity),
        }
    }

    /// Add a field-value pair by NameId
    pub fn insert(&mut self, field: NameId, value: Value) {
        self.entries.push((field, value));
    }

    /// Add a field-value pair by string name (interned)
    pub fn insert_str(&mut self, field: &str, value: Value) {
        self.entries.push((intern_name(field), value));
    }

    /// Add a field-value pair by Arc<str> name (interned)
    pub fn insert_arc(&mut self, field: &Arc<str>, value: Value) {
        self.entries.push((intern_name(field), value));
    }

    /// Build the RecordValue, sorting entries by NameId.
    ///
    /// Uses `into_vec()` for efficient Vec conversion: no-op when already
    /// spilled to heap, single alloc + copy when inline.
    pub fn build(mut self) -> RecordValue {
        self.entries.sort_by_key(|(k, _)| *k);
        RecordValue::from_sorted_entries(self.entries.into_vec())
    }
}

impl Default for RecordBuilder {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Trait impls for RecordValue
// ============================================================================

impl From<Vec<(String, Value)>> for RecordValue {
    fn from(entries: Vec<(String, Value)>) -> Self {
        let mut id_entries: Vec<(NameId, Value)> = entries
            .into_iter()
            .map(|(k, v)| (intern_name(&k), v))
            .collect();
        id_entries.sort_by_key(|(k, _)| *k);
        RecordValue::from_sorted_entries(id_entries)
    }
}

impl Default for RecordValue {
    fn default() -> Self {
        Self::new()
    }
}

impl PartialEq for RecordValue {
    fn eq(&self, other: &Self) -> bool {
        // Fast path: pointer equality
        if Arc::ptr_eq(&self.entries, &other.entries) {
            return true;
        }
        self.entries == other.entries
    }
}

impl Eq for RecordValue {}

impl PartialOrd for RecordValue {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RecordValue {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Fast path: pointer equality
        if Arc::ptr_eq(&self.entries, &other.entries) {
            return std::cmp::Ordering::Equal;
        }
        // NameId comparison is O(1) integer comparison per field
        self.entries.cmp(&other.entries)
    }
}

impl std::hash::Hash for RecordValue {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.entries.hash(state);
    }
}

impl std::fmt::Debug for RecordValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map()
            .entries(self.entries.iter().map(|(k, v)| {
                let name = resolve_name_id(*k);
                (name, v)
            }))
            .finish()
    }
}

impl FromIterator<(NameId, Value)> for RecordValue {
    fn from_iter<I: IntoIterator<Item = (NameId, Value)>>(iter: I) -> Self {
        let mut entries: Vec<_> = iter.into_iter().collect();
        entries.sort_by_key(|(k, _)| *k);
        RecordValue::from_sorted_entries(entries)
    }
}

impl FromIterator<(Arc<str>, Value)> for RecordValue {
    fn from_iter<I: IntoIterator<Item = (Arc<str>, Value)>>(iter: I) -> Self {
        let mut entries: Vec<_> = iter
            .into_iter()
            .map(|(k, v)| (intern_name(&k), v))
            .collect();
        entries.sort_by_key(|(k, _)| *k);
        RecordValue::from_sorted_entries(entries)
    }
}

impl<'a> IntoIterator for &'a RecordValue {
    type Item = (NameId, &'a Value);
    type IntoIter = RecordIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        RecordIter {
            inner: self.entries.iter(),
        }
    }
}

/// Iterator over RecordValue entries, yielding (NameId, &Value).
pub struct RecordIter<'a> {
    inner: std::slice::Iter<'a, (NameId, Value)>,
}

impl<'a> Iterator for RecordIter<'a> {
    type Item = (NameId, &'a Value);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, v)| (*k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl ExactSizeIterator for RecordIter<'_> {}
