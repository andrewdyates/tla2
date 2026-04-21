// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::{functions::FP_UNSET, Value};
use super::RecordValue;
use crate::dedup_fingerprint::{additive_record_entry_hash, splitmix64};
use std::sync::atomic::AtomicU64;
use std::sync::Arc;
use tla_core::{intern_name, NameId};

impl RecordValue {
    /// Create a new record with one field inserted or updated (NameId key)
    /// Part of #3221: preserves additive cache through replace and insert.
    ///
    /// Part of #3964: Avoid `Arc::clone + Arc::make_mut` pattern which always
    /// clones the inner Vec (the clone bumps refcount to 2, then make_mut sees
    /// refcount > 1 and clones). Instead, directly clone the Vec into a new Arc,
    /// saving one atomic increment + one atomic CAS.
    pub fn insert(&self, field: NameId, value: Value) -> Self {
        // Binary search on the shared Arc (immutable access)
        match self.entries.binary_search_by_key(&field, |(k, _)| *k) {
            Ok(idx) => {
                // Replace existing field
                let old_value = &self.entries[idx].1;
                if *old_value == value {
                    return self.clone();
                }
                let updated_additive = self.get_additive_fp().and_then(|fp| {
                    let old_hash = additive_record_entry_hash(field, old_value).ok()?;
                    let new_hash = additive_record_entry_hash(field, &value).ok()?;
                    Some(fp.wrapping_sub(old_hash).wrapping_add(new_hash))
                });
                // Direct Vec clone into new Arc — avoids the Arc::clone + Arc::make_mut
                // dance which always triggers a clone (refcount is 2 after Arc::clone).
                let mut new_vec = (*self.entries).clone();
                new_vec[idx].1 = value;
                RecordValue {
                    entries: Arc::new(new_vec),
                    additive_fp: AtomicU64::new(updated_additive.unwrap_or(FP_UNSET)),
                }
            }
            Err(idx) => {
                // Insert new field - adjust length term and add entry
                let updated_additive = self.get_additive_fp().and_then(|fp| {
                    let old_len = self.entries.len();
                    let new_len = old_len + 1;
                    let new_hash = additive_record_entry_hash(field, &value).ok()?;
                    Some(
                        fp.wrapping_sub(splitmix64(old_len as u64))
                            .wrapping_add(splitmix64(new_len as u64))
                            .wrapping_add(new_hash),
                    )
                });
                // Direct Vec clone + insert — avoids Arc::clone + Arc::make_mut overhead.
                let mut new_vec = (*self.entries).clone();
                new_vec.insert(idx, (field, value));
                RecordValue {
                    entries: Arc::new(new_vec),
                    additive_fp: AtomicU64::new(updated_additive.unwrap_or(FP_UNSET)),
                }
            }
        }
    }

    /// Create a new record with one field inserted or updated, consuming self.
    ///
    /// Takes ownership so the caller can benefit from `Arc::get_mut` when the
    /// record is uniquely owned (refcount == 1). This avoids cloning the entries
    /// Vec entirely in the common case where the caller's value is being moved.
    ///
    /// Part of #3964: COW-optimized insert for owned records.
    pub fn insert_owned(mut self, field: NameId, value: Value) -> Self {
        match self.entries.binary_search_by_key(&field, |(k, _)| *k) {
            Ok(idx) => {
                if self.entries[idx].1 == value {
                    return self;
                }
                let updated_additive = self.get_additive_fp().and_then(|fp| {
                    let old_hash = additive_record_entry_hash(field, &self.entries[idx].1).ok()?;
                    let new_hash = additive_record_entry_hash(field, &value).ok()?;
                    Some(fp.wrapping_sub(old_hash).wrapping_add(new_hash))
                });
                // Arc::get_mut succeeds when we're the sole owner (no clone needed).
                if let Some(entries) = Arc::get_mut(&mut self.entries) {
                    entries[idx].1 = value;
                } else {
                    let mut new_vec = (*self.entries).clone();
                    new_vec[idx].1 = value;
                    self.entries = Arc::new(new_vec);
                }
                self.reset_caches_with_additive(updated_additive);
                self
            }
            Err(idx) => {
                let updated_additive = self.get_additive_fp().and_then(|fp| {
                    let old_len = self.entries.len();
                    let new_len = old_len + 1;
                    let new_hash = additive_record_entry_hash(field, &value).ok()?;
                    Some(
                        fp.wrapping_sub(splitmix64(old_len as u64))
                            .wrapping_add(splitmix64(new_len as u64))
                            .wrapping_add(new_hash),
                    )
                });
                if let Some(entries) = Arc::get_mut(&mut self.entries) {
                    entries.insert(idx, (field, value));
                } else {
                    let mut new_vec = (*self.entries).clone();
                    new_vec.insert(idx, (field, value));
                    self.entries = Arc::new(new_vec);
                }
                self.reset_caches_with_additive(updated_additive);
                self
            }
        }
    }

    /// Create a new record with one field inserted or updated (string key)
    pub fn insert_str(&self, field: &str, value: Value) -> Self {
        self.insert(intern_name(field), value)
    }

    /// Alias for insert (OrdMap compatibility)
    #[inline]
    pub fn update(&self, field: NameId, value: Value) -> Self {
        self.insert(field, value)
    }

    /// Update an existing field's value by NameId without allocating a new key.
    ///
    /// Takes ownership so the caller can benefit from `Arc::make_mut` when the
    /// record is uniquely owned (for example, nested EXCEPT updates in the
    /// evaluator hot path).
    ///
    /// Missing fields are a no-op to match TLA+ record EXCEPT semantics.
    /// Part of #3221: preserves additive cache through delta update.
    #[inline]
    pub fn update_existing_field_id(mut self, field: NameId, value: Value) -> Self {
        let Some(idx) = self.find_field_idx(field) else {
            return self;
        };
        if self.entries[idx].1 == value {
            return self;
        }
        let updated_additive = self.get_additive_fp().and_then(|fp| {
            let old_hash = additive_record_entry_hash(field, &self.entries[idx].1).ok()?;
            let new_hash = additive_record_entry_hash(field, &value).ok()?;
            Some(fp.wrapping_sub(old_hash).wrapping_add(new_hash))
        });
        // Part of #3964: Use Arc::get_mut (non-atomic check) when refcount == 1,
        // falling back to Arc::make_mut only when shared. Since this method takes
        // `self` by value, the caller's move typically makes the Arc uniquely owned.
        if let Some(entries) = Arc::get_mut(&mut self.entries) {
            entries[idx].1 = value;
        } else {
            Arc::make_mut(&mut self.entries)[idx].1 = value;
        }
        self.reset_caches_with_additive(updated_additive);
        self
    }

    /// Update an existing field's value by name string.
    ///
    /// Missing fields are a no-op to match TLA+ record EXCEPT semantics.
    #[inline]
    pub fn update_existing_field(&self, field: &str, value: Value) -> Self {
        self.clone()
            .update_existing_field_id(intern_name(field), value)
    }

    /// Take the value at the given field out of the record, replacing it with
    /// a lightweight placeholder. Returns `(old_value, position, old_entry_hash)`
    /// for later restoration via [`restore_at`].
    ///
    /// Used by `apply_except_spec` to avoid cloning inner values during nested
    /// EXCEPT evaluation. By moving the value out instead of cloning, the inner
    /// `Arc` refcount stays at 1 so recursive `Arc::make_mut` calls are free.
    ///
    /// After calling this, the record is in an inconsistent state. The caller
    /// MUST call `restore_at` before using the record, or drop it on error.
    /// Part of #3168, #3221.
    #[inline]
    pub fn take_at_field_id(&mut self, field: NameId) -> Option<(Value, usize, Option<u64>)> {
        let idx = self.find_field_idx(field)?;
        let old_entry_hash = self
            .get_additive_fp()
            .and_then(|_| additive_record_entry_hash(field, &self.entries[idx].1).ok());
        // Part of #3964: Use Arc::get_mut (non-atomic) when refcount == 1.
        let entries = if let Some(e) = Arc::get_mut(&mut self.entries) {
            e
        } else {
            Arc::make_mut(&mut self.entries)
        };
        let old_val = std::mem::replace(&mut entries[idx].1, Value::Bool(false));
        Some((old_val, idx, old_entry_hash))
    }

    /// Restore a value at the given position after a [`take_at_field_id`] call.
    /// Uses the pre-take entry hash to preserve the cached additive fingerprint.
    /// Part of #3168, #3221.
    #[inline]
    pub fn restore_at(&mut self, idx: usize, old_entry_hash: Option<u64>, value: Value) {
        let field_id = self.entries[idx].0;
        let updated_additive = old_entry_hash.and_then(|old_hash| {
            self.get_additive_fp().and_then(|fp| {
                let new_hash = additive_record_entry_hash(field_id, &value).ok()?;
                Some(fp.wrapping_sub(old_hash).wrapping_add(new_hash))
            })
        });
        // Part of #3964: Arc::get_mut fast path for non-atomic check.
        if let Some(entries) = Arc::get_mut(&mut self.entries) {
            entries[idx].1 = value;
        } else {
            Arc::make_mut(&mut self.entries)[idx].1 = value;
        }
        self.reset_caches_with_additive(updated_additive);
    }
}
