// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::Value;
use super::RecordValue;
use std::sync::Arc;
use tla_core::{intern_name, resolve_name_id, NameId};

impl RecordValue {
    /// Get a field value by NameId.
    ///
    /// Uses linear scan for records with <= 8 fields (the common case in TLA+
    /// protocol specs) and binary search for larger records. Linear scan is
    /// faster for small records due to sequential cache-line access and no
    /// branch misprediction from binary search pivots. This matches TLC's
    /// `RecordValue.select()` which always uses linear scan.
    /// Part of #3073.
    #[inline]
    pub fn get_by_id(&self, field: NameId) -> Option<&Value> {
        if self.entries.len() <= 8 {
            for (k, v) in self.entries.iter() {
                if *k == field {
                    return Some(v);
                }
            }
            None
        } else {
            self.entries
                .binary_search_by_key(&field, |(k, _)| *k)
                .ok()
                .map(|idx| &self.entries[idx].1)
        }
    }

    /// Get a field value by name string (O(log n) via binary search after interning)
    ///
    /// Convenience wrapper that interns the field name first. For hot paths where
    /// the NameId is already available, use `get_by_id()` instead.
    #[inline]
    pub fn get(&self, field: &str) -> Option<&Value> {
        let id = intern_name(field);
        self.get_by_id(id)
    }

    /// Check if a field exists by NameId.
    /// Uses linear scan for small records, binary search for large. Part of #3073.
    #[inline]
    pub(crate) fn contains_key_id(&self, field: NameId) -> bool {
        if self.entries.len() <= 8 {
            self.entries.iter().any(|(k, _)| *k == field)
        } else {
            self.entries
                .binary_search_by_key(&field, |(k, _)| *k)
                .is_ok()
        }
    }

    /// Check if a field exists by name string
    #[inline]
    pub fn contains_key(&self, field: &str) -> bool {
        let id = intern_name(field);
        self.contains_key_id(id)
    }

    /// Iterate over field NameIds
    pub fn keys(&self) -> impl Iterator<Item = NameId> + '_ {
        self.entries.iter().map(|(k, _)| *k)
    }

    /// Iterate over field name strings (resolving NameId)
    pub fn key_strings(&self) -> impl Iterator<Item = Arc<str>> + '_ {
        self.entries.iter().map(|(k, _)| resolve_name_id(*k))
    }

    /// Iterate over field values
    pub fn values(&self) -> impl Iterator<Item = &Value> {
        self.entries.iter().map(|(_, v)| v)
    }

    /// Iterate over (NameId, value) pairs
    pub fn iter(&self) -> impl Iterator<Item = (NameId, &Value)> {
        self.entries.iter().map(|(k, v)| (*k, v))
    }

    /// Iterate over (field_name_string, value) pairs (resolving NameId)
    ///
    /// Use this for display, error messages, and fingerprinting.
    /// For hot-path comparison/sorting, use `iter()` which returns NameId.
    pub fn iter_str(&self) -> impl Iterator<Item = (Arc<str>, &Value)> {
        self.entries.iter().map(|(k, v)| (resolve_name_id(*k), v))
    }
}
