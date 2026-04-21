// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array-backed record type for TLA+ records with `NameId`-keyed field names.
//!
//! `RecordValue` keeps fields in a sorted contiguous array for fast lookup,
//! cache-friendly iteration, and copy-on-write `EXCEPT` updates.

mod lookup;
mod mutation;

use super::functions::FP_UNSET;
use super::Value;
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};
use std::sync::Arc;
use tla_core::{intern_name, NameId};

/// Array-backed record for TLA+ records with `NameId`-keyed field names.
///
/// Fields stay sorted by `NameId` inside an `Arc<Vec<_>>`, which gives fast
/// integer-keyed lookup, cache-friendly iteration, and copy-on-write updates.
pub struct RecordValue {
    /// Sorted unique `(field_id, value)` pairs; `pub(super)` for `record_impls.rs`.
    pub(super) entries: Arc<Vec<(NameId, Value)>>,
    /// Additive fingerprint cache for nested `EXCEPT` / state dedup updates.
    additive_fp: AtomicU64,
}

impl Clone for RecordValue {
    fn clone(&self) -> Self {
        RecordValue {
            entries: self.entries.clone(),
            additive_fp: AtomicU64::new(self.additive_fp.load(AtomicOrdering::Relaxed)),
        }
    }
}

impl RecordValue {
    /// Find the index of a field in the entries.
    /// Linear scan for <= 8 entries, binary search for larger. Part of #3073.
    #[inline]
    fn find_field_idx(&self, field: NameId) -> Option<usize> {
        if self.entries.len() <= 8 {
            self.entries.iter().position(|(k, _)| *k == field)
        } else {
            self.entries.binary_search_by_key(&field, |(k, _)| *k).ok()
        }
    }

    /// Reset caches after a mutation, optionally seeding the additive cache.
    /// Part of #3221: mirrors FuncValue::reset_caches_with_additive.
    #[inline]
    fn reset_caches_with_additive(&mut self, additive_fp: Option<u64>) {
        self.additive_fp
            .store(additive_fp.unwrap_or(FP_UNSET), AtomicOrdering::Relaxed);
    }

    /// Create an empty record
    pub(crate) fn new() -> Self {
        RecordValue {
            entries: Arc::new(Vec::new()),
            additive_fp: AtomicU64::new(FP_UNSET),
        }
    }

    /// Create a record from pre-sorted field-value pairs (NameId keys)
    /// Caller must ensure entries are sorted by NameId
    pub fn from_sorted_entries(entries: Vec<(NameId, Value)>) -> Self {
        RecordValue {
            entries: Arc::new(entries),
            additive_fp: AtomicU64::new(FP_UNSET),
        }
    }

    /// Create a record from pre-sorted field-value pairs (string keys, interned)
    /// Caller must ensure entries are sorted by field name (will be re-sorted by NameId)
    pub fn from_sorted_str_entries(entries: Vec<(Arc<str>, Value)>) -> Self {
        let mut id_entries: Vec<(NameId, Value)> = entries
            .into_iter()
            .map(|(k, v)| (intern_name(&k), v))
            .collect();
        id_entries.sort_by_key(|(k, _)| *k);
        RecordValue {
            entries: Arc::new(id_entries),
            additive_fp: AtomicU64::new(FP_UNSET),
        }
    }

    /// Get the number of fields
    #[inline]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Check if the record is empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Get the cached additive fingerprint if already computed.
    /// Part of #3221: commutative hash for state-level dedup.
    #[inline]
    pub fn get_additive_fp(&self) -> Option<u64> {
        let cached = self.additive_fp.load(AtomicOrdering::Relaxed);
        (cached != FP_UNSET).then_some(cached)
    }

    /// Cache the additive fingerprint. Returns the fingerprint.
    /// Part of #3221: commutative hash for state-level dedup.
    #[inline]
    pub fn cache_additive_fp(&self, fp: u64) -> u64 {
        let _ = self.additive_fp.compare_exchange(
            FP_UNSET,
            fp,
            AtomicOrdering::Relaxed,
            AtomicOrdering::Relaxed,
        );
        fp
    }

    /// Check if two RecordValues share the same underlying storage (pointer equality)
    #[inline]
    pub(crate) fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.entries, &other.entries)
    }

    /// Return a stable identity key for the underlying storage Arc.
    ///
    /// Part of #3337: Used by `WorkerFpMemo` to cache fingerprints by
    /// pointer identity without needing `AtomicU64` embedded caches.
    #[inline]
    pub fn storage_ptr_identity(&self) -> usize {
        Arc::as_ptr(&self.entries).cast::<()>() as usize
    }
}
