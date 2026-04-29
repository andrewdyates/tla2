// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Mutation and nested-EXCEPT helpers for `IntIntervalFunc`.
//!
//! Handles `[f EXCEPT ![x] = y]` with COW optimization, interning for small
//! functions, and additive-fingerprint maintenance. Split from
//! `int_interval_func.rs` as part of #3443.

use super::IntIntervalFunc;
use crate::dedup_fingerprint::additive_int_entry_hash;
use crate::value::functions::FP_UNSET;
use crate::value::{
    intern_int_func_array, try_get_interned_modified, Value, MAX_INTERN_INT_FUNC_SIZE,
};
use num_traits::ToPrimitive;
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};
use std::sync::Arc;

impl IntIntervalFunc {
    /// Check whether an EXCEPT operation would actually change the function.
    /// Returns `false` for out-of-domain keys and same-value updates.
    /// Part of #3386: used by compiled-guard no-op fast path.
    #[inline]
    pub fn would_except_change(&self, arg: &Value, new_val: &Value) -> bool {
        let idx = match arg {
            Value::SmallInt(n) => *n,
            Value::Int(n) => match n.to_i64() {
                Some(i) => i,
                None => return false,
            },
            _ => return false,
        };
        if idx < self.min || idx > self.max {
            return false;
        }
        self.values[(idx - self.min) as usize] != *new_val
    }

    /// Take the value at a given integer key out of the function.
    /// Returns `(old_value, array_index, old_entry_hash)` for later restoration
    /// via [`restore_at`].
    ///
    /// Part of #3073, #3168: move-out for nested EXCEPT evaluation.
    #[inline]
    pub fn take_at(&mut self, arg: &Value) -> Option<(Value, usize, Option<u64>)> {
        let idx = match arg {
            Value::SmallInt(n) => *n,
            Value::Int(n) => n.to_i64()?,
            _ => return None,
        };
        if idx < self.min || idx > self.max {
            return None;
        }
        let arr_idx = (idx - self.min) as usize;
        let old_entry_hash = self
            .get_additive_fp()
            .and_then(|_| additive_int_entry_hash(idx, &self.values[arr_idx]).ok());
        // Part of #3964: Use Arc::get_mut (non-atomic check) when refcount == 1.
        let entries = if let Some(v) = Arc::get_mut(&mut self.values) {
            v
        } else {
            Arc::make_mut(&mut self.values)
        };
        let old_val = std::mem::replace(&mut entries[arr_idx], Value::Bool(false));
        Some((old_val, arr_idx, old_entry_hash))
    }

    /// Restore a value at the given array position after a [`take_at`] call.
    /// Uses the pre-take entry hash to preserve a cached additive fingerprint.
    /// Part of #3073, #3168.
    #[inline]
    pub fn restore_at(&mut self, arr_idx: usize, old_entry_hash: Option<u64>, value: Value) {
        let updated_additive = old_entry_hash.and_then(|old_hash| {
            self.get_additive_fp().and_then(|fp| {
                let key = self
                    .min
                    .checked_add(arr_idx as i64)
                    .expect("invariant: IntIntervalFunc index stays within i64 domain");
                let new_hash = additive_int_entry_hash(key, &value).ok()?;
                Some(fp.wrapping_sub(old_hash).wrapping_add(new_hash))
            })
        });
        // Part of #3964: Arc::get_mut fast path for non-atomic check.
        if let Some(values) = Arc::get_mut(&mut self.values) {
            values[arr_idx] = value;
        } else {
            Arc::make_mut(&mut self.values)[arr_idx] = value;
        }
        self.reset_caches_with_additive(updated_additive);
    }

    #[inline]
    fn cached_additive_after_replace(
        &self,
        arr_idx: usize,
        old_value: &Value,
        new_value: &Value,
    ) -> Option<u64> {
        let key = self
            .min
            .checked_add(arr_idx as i64)
            .expect("invariant: IntIntervalFunc index stays within i64 domain");
        self.get_additive_fp().and_then(|fp| {
            let old_hash = additive_int_entry_hash(key, old_value).ok()?;
            let new_hash = additive_int_entry_hash(key, new_value).ok()?;
            Some(fp.wrapping_sub(old_hash).wrapping_add(new_hash))
        })
    }

    #[inline]
    fn reset_caches_with_additive(&mut self, additive_fp: Option<u64>) {
        self.additive_fp
            .store(additive_fp.unwrap_or(FP_UNSET), AtomicOrdering::Relaxed);
    }

    /// Update the function at a single point: [f EXCEPT ![x] = y]
    ///
    /// Returns an IntIntervalFunc with the updated value. Uses interning for small
    /// functions to deduplicate memory when shared.
    #[inline]
    pub fn except(self, arg: Value, value: Value) -> Self {
        #[cfg(feature = "memory-stats")]
        memory_stats::inc_int_func_except();

        let idx = match &arg {
            Value::SmallInt(n) => *n,
            Value::Int(n) => match n.to_i64() {
                Some(i) => i,
                None => return self,
            },
            _ => return self,
        };
        if idx < self.min || idx > self.max {
            return self;
        }
        let arr_idx = (idx - self.min) as usize;
        // Short-circuit: if value unchanged, return self (preserves cached fingerprint)
        let old_value = &self.values[arr_idx];
        if *old_value == value {
            return self;
        }
        let updated_additive = self.cached_additive_after_replace(arr_idx, old_value, &value);

        // Part of #3316: Skip interning when the thread-local flag is set
        // (simulation mode). Interning adds per-EXCEPT overhead (hash all values
        // + DashMap lookup) that's wasteful for unique random-trace states.
        // Fall through to the plain COW path (lines 239-242 equivalent).
        if crate::value::intern_tables::skip_int_func_interning() {
            let mut new_self = self;
            // Part of #3964: Arc::get_mut fast path for non-atomic check.
            if let Some(values) = Arc::get_mut(&mut new_self.values) {
                values[arr_idx] = value;
            } else {
                Arc::make_mut(&mut new_self.values)[arr_idx] = value;
            }
            new_self.reset_caches_with_additive(updated_additive);
            return new_self;
        }

        // For small functions, try to find an already-interned version first
        // This avoids allocating a new Vec when we would just return an existing one
        if self.values.len() <= MAX_INTERN_INT_FUNC_SIZE {
            // Fast path: check if the modified version is already interned
            if let Some(interned) =
                try_get_interned_modified(self.min, self.max, &self.values, arr_idx, &value)
            {
                return IntIntervalFunc {
                    min: self.min,
                    max: self.max,
                    values: interned,
                    additive_fp: AtomicU64::new(updated_additive.unwrap_or(FP_UNSET)),
                };
            }

            // Medium path: if we're the sole owner, modify in place (COW)
            // If refcount == 1, the value is NOT in the intern table (which would add +1)
            // so we can safely modify in place, then intern the result
            if Arc::strong_count(&self.values) == 1 {
                let mut new_self = self;
                // Part of #3964: Arc::get_mut is guaranteed to succeed here since
                // we just checked strong_count == 1. Avoids the atomic CAS in make_mut.
                Arc::get_mut(&mut new_self.values).expect("refcount == 1")[arr_idx] = value;
                // Extract Vec and re-intern with new fingerprint
                let vec = Arc::try_unwrap(new_self.values).unwrap_or_else(|arc| (*arc).clone());
                let interned = intern_int_func_array(new_self.min, new_self.max, vec);
                return IntIntervalFunc {
                    min: new_self.min,
                    max: new_self.max,
                    values: interned,
                    additive_fp: AtomicU64::new(updated_additive.unwrap_or(FP_UNSET)),
                };
            }

            // Slow path: clone the values array and intern it
            let mut new_values: Vec<Value> = self.values.to_vec();
            new_values[arr_idx] = value;
            let interned = intern_int_func_array(self.min, self.max, new_values);
            return IntIntervalFunc {
                min: self.min,
                max: self.max,
                values: interned,
                additive_fp: AtomicU64::new(updated_additive.unwrap_or(FP_UNSET)),
            };
        }

        // For larger functions, use COW
        #[cfg(feature = "memory-stats")]
        if Arc::strong_count(&self.values) > 1 {
            memory_stats::inc_int_func_except_clone();
        }
        let mut new_self = self;
        // Part of #3964: Arc::get_mut fast path for non-atomic check.
        if let Some(values) = Arc::get_mut(&mut new_self.values) {
            values[arr_idx] = value;
        } else {
            Arc::make_mut(&mut new_self.values)[arr_idx] = value;
        }
        new_self.reset_caches_with_additive(updated_additive);
        new_self
    }
}
