// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::Value;
use super::{additive_cache_val, FuncTakeSource, FuncValue, FP_UNSET};
use crate::dedup_fingerprint::additive_entry_hash;
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};
use std::sync::{Arc, OnceLock};

impl Clone for FuncValue {
    fn clone(&self) -> Self {
        let tlc_cache = OnceLock::new();
        if let Some(normalized) = self.tlc_normalized.get() {
            let _ = tlc_cache.set(Arc::clone(normalized));
        }
        FuncValue {
            domain: Arc::clone(&self.domain),
            values: Arc::clone(&self.values),
            overrides: self.overrides.clone(),
            additive_fp: AtomicU64::new(self.additive_fp.load(AtomicOrdering::Relaxed)),
            tlc_normalized: tlc_cache,
        }
    }
}

impl FuncValue {
    #[inline]
    pub(super) fn store_additive_cache(&self, additive_fp: Option<u64>) {
        self.additive_fp
            .store(additive_cache_val(additive_fp), AtomicOrdering::Relaxed);
    }

    #[inline]
    pub(super) fn cached_additive_after_replace(
        &self,
        idx: usize,
        old_value: &Value,
        new_value: &Value,
    ) -> Option<u64> {
        let key = &self.domain[idx];
        self.get_additive_fp().and_then(|fp| {
            let old_hash = additive_entry_hash(key, old_value).ok()?;
            let new_hash = additive_entry_hash(key, new_value).ok()?;
            Some(fp.wrapping_sub(old_hash).wrapping_add(new_hash))
        })
    }

    /// Take the value at the given key out of the function, replacing it with
    /// a lightweight placeholder. Returns `(old_value, position, old_entry_hash, source)`
    /// for later restoration via [`restore_at`].
    ///
    /// Part of #3386: overlay-aware — if the value comes from the overlay,
    /// removes only the winning override entry without materializing. If the
    /// value comes from the base array, uses `Arc::make_mut` for COW.
    ///
    /// Used by `apply_except_spec` to avoid cloning inner values during nested
    /// EXCEPT evaluation. By moving the value out instead of cloning, the inner
    /// `Arc` refcount stays at 1 so recursive `Arc::make_mut` calls are free.
    ///
    /// After calling this, the function is in an inconsistent state. The caller
    /// MUST call `restore_at` before using the function, or drop it on error.
    /// Part of #3168.
    #[inline]
    pub fn take_at(&mut self, arg: &Value) -> Option<(Value, usize, Option<u64>, FuncTakeSource)> {
        let idx = self.domain.binary_search_by(|k| k.cmp(arg)).ok()?;

        // Part of #3386: Check overlay first — if the value comes from an
        // override, remove just that entry without materializing the base.
        if let Some(ref mut overrides) = self.overrides {
            if let Some(pos) = overrides.iter().rposition(|&(oidx, _)| oidx == idx) {
                let (_, old_val) = overrides.remove(pos);
                if overrides.is_empty() {
                    self.overrides = None;
                }
                let old_entry_hash = self
                    .get_additive_fp()
                    .and_then(|_| additive_entry_hash(&self.domain[idx], &old_val).ok());
                return Some((old_val, idx, old_entry_hash, FuncTakeSource::Overlay));
            }
        }

        // Value comes from base array. Materialize any remaining overlay
        // entries before mutating the base to avoid losing them.
        self.materialize();
        let old_entry_hash = self
            .get_additive_fp()
            .and_then(|_| additive_entry_hash(&self.domain[idx], &self.values[idx]).ok());
        // Part of #3964: Use Arc::get_mut (non-atomic check) when refcount == 1,
        // falling back to Arc::make_mut only when shared.
        let values = if let Some(v) = Arc::get_mut(&mut self.values) {
            v
        } else {
            Arc::make_mut(&mut self.values)
        };
        let old_val = std::mem::replace(&mut values[idx], Value::Bool(false));
        Some((old_val, idx, old_entry_hash, FuncTakeSource::Base))
    }

    /// Restore a value at the given position after a [`take_at`] call.
    /// Part of #3386: source-aware — overlay-sourced values are pushed back
    /// as override entries, preserving the lazy representation.
    /// Updates the additive fingerprint cache; TLC domain order is unchanged.
    /// Part of #3168.
    #[inline]
    pub fn restore_at(
        &mut self,
        idx: usize,
        old_entry_hash: Option<u64>,
        source: FuncTakeSource,
        value: Value,
    ) {
        let updated_additive = old_entry_hash.and_then(|old_hash| {
            self.get_additive_fp().and_then(|fp| {
                let key = &self.domain[idx];
                let new_hash = additive_entry_hash(key, &value).ok()?;
                Some(fp.wrapping_sub(old_hash).wrapping_add(new_hash))
            })
        });
        match source {
            FuncTakeSource::Overlay => {
                let overrides = self
                    .overrides
                    .get_or_insert_with(|| Box::new(Vec::with_capacity(2)));
                overrides.push((idx, value));
            }
            FuncTakeSource::Base => {
                // Part of #3964: Arc::get_mut fast path for non-atomic check.
                if let Some(values) = Arc::get_mut(&mut self.values) {
                    values[idx] = value;
                } else {
                    Arc::make_mut(&mut self.values)[idx] = value;
                }
            }
        }
        self.store_additive_cache(updated_additive);
    }

    /// Singleton empty function.
    fn empty() -> &'static FuncValue {
        static EMPTY: OnceLock<FuncValue> = OnceLock::new();
        EMPTY.get_or_init(|| FuncValue {
            domain: Arc::<[Value]>::from([]),
            values: Arc::new(Vec::new()),
            overrides: None,
            additive_fp: AtomicU64::new(FP_UNSET),
            tlc_normalized: OnceLock::new(),
        })
    }

    /// Create a function from pre-sorted (key, value) pairs.
    /// Entries must be sorted by key and unique.
    pub fn from_sorted_entries(entries: Vec<(Value, Value)>) -> Self {
        if entries.is_empty() {
            return FuncValue::empty().clone();
        }
        #[cfg(feature = "memory-stats")]
        crate::value::memory_stats::inc_func_entries(entries.len());

        let (domain, values): (Vec<Value>, Vec<Value>) = entries.into_iter().unzip();

        FuncValue {
            domain: domain.into(),
            values: Arc::new(values),
            overrides: None,
            additive_fp: AtomicU64::new(FP_UNSET),
            tlc_normalized: OnceLock::new(),
        }
    }

    /// Get the cached additive fingerprint if already computed.
    /// Part of #3168: commutative hash for state-level dedup.
    #[inline]
    pub fn get_additive_fp(&self) -> Option<u64> {
        let cached = self.additive_fp.load(AtomicOrdering::Relaxed);
        (cached != FP_UNSET).then_some(cached)
    }

    /// Cache the additive fingerprint. Returns the cached value.
    /// Part of #3168: commutative hash for state-level dedup.
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
}
