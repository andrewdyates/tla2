// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::Value;
use super::FuncValue;
use std::sync::Arc;

impl FuncValue {
    /// Maximum overlay entries before materialization is forced.
    /// Threshold of 4: typical TLA+ EXCEPT has 1-3 clauses.
    const MAX_OVERLAY_SIZE: usize = 4;

    /// Part of #3371: Lazy EXCEPT overlay — O(1) append instead of O(n) clone.
    fn except_existing(mut self, idx: usize, value: Value) -> Self {
        let old_value = self.get_value_at(idx);
        if *old_value == value {
            return self;
        }
        let updated_additive = self.cached_additive_after_replace(idx, old_value, &value);

        // Part of #3371: Use overlay path when below threshold.
        let overlay_len = self.overrides.as_ref().map_or(0, |v| v.len());
        if overlay_len >= Self::MAX_OVERLAY_SIZE {
            // Materialize overlay first, then mutate values directly.
            self.materialize();
            #[cfg(feature = "memory-stats")]
            if Arc::strong_count(&self.values) > 1 {
                crate::value::memory_stats::inc_func_except_clone();
            }
            // Part of #3964: Arc::get_mut fast path for non-atomic check.
            if let Some(values) = Arc::get_mut(&mut self.values) {
                values[idx] = value;
            } else {
                Arc::make_mut(&mut self.values)[idx] = value;
            }
        } else {
            // O(1) overlay append — no values Vec clone.
            let overrides = self
                .overrides
                .get_or_insert_with(|| Box::new(Vec::with_capacity(2)));
            overrides.push((idx, value));
        }

        self.store_additive_cache(updated_additive);
        // Note: tlc_normalized (domain index permutation) is NOT invalidated here.
        // EXCEPT changes values, not domain keys, so the TLC sort order is stable.
        self
    }

    /// Get the logical value at position `idx`, checking overlay first.
    /// Last override wins for duplicate indices.
    #[inline]
    pub fn get_value_at(&self, idx: usize) -> &Value {
        if let Some(ref overrides) = self.overrides {
            for &(oidx, ref val) in overrides.iter().rev() {
                if oidx == idx {
                    return val;
                }
            }
        }
        &self.values[idx]
    }

    /// Check if overlay is active.
    #[inline]
    pub fn has_overlay(&self) -> bool {
        self.overrides.is_some()
    }

    /// Collapse overlay into values Vec. Called by comparison, normalization,
    /// and any path that needs direct values array access.
    pub fn materialize(&mut self) {
        if let Some(overrides) = self.overrides.take() {
            // Part of #3964: Use Arc::get_mut (non-atomic check) when refcount == 1,
            // falling back to Arc::make_mut only when shared.
            let values = if let Some(v) = Arc::get_mut(&mut self.values) {
                v
            } else {
                Arc::make_mut(&mut self.values)
            };
            for (idx, val) in *overrides {
                values[idx] = val;
            }
        }
    }

    /// Apply the function to an argument (lookup by key).
    /// Part of #3371: overlay-aware.
    pub fn apply(&self, arg: &Value) -> Option<&Value> {
        self.domain
            .binary_search_by(|k| k.cmp(arg))
            .ok()
            .map(|idx| self.get_value_at(idx))
    }

    /// Update the function at a single point: [f EXCEPT ![x] = y]
    ///
    /// Takes ownership for copy-on-write (COW) optimization: when the caller
    /// is the sole owner (Arc refcount == 1), modifies entries in place via
    /// `Arc::make_mut` instead of cloning. For chained EXCEPTs like
    /// `[f EXCEPT ![a]=1, ![b]=2, ![c]=3]`, the first creates a new FuncValue
    /// (clone required, original shared with state store), but subsequent
    /// EXCEPTs on the temporary modify in place — reducing O(k*n) to O(n).
    /// Part of #3073 Phase 2.
    pub fn except(self, arg: Value, value: Value) -> Self {
        #[cfg(feature = "memory-stats")]
        crate::value::memory_stats::inc_func_except();

        match self.domain.binary_search_by(|k| k.cmp(&arg)) {
            Ok(idx) => self.except_existing(idx, value),
            Err(_) => {
                // Key not in domain - return unchanged (TLA+ function semantics)
                self
            }
        }
    }

    /// Check whether an EXCEPT operation would actually change the function.
    /// Returns `false` for out-of-domain keys and same-value updates.
    /// Part of #3386: used by compiled-guard no-op fast path to avoid cloning
    /// borrowed/shared function values for semantic no-ops.
    #[inline]
    pub fn would_except_change(&self, arg: &Value, new_val: &Value) -> bool {
        match self.domain.binary_search_by(|k| k.cmp(arg)) {
            Ok(idx) => *self.get_value_at(idx) != *new_val,
            Err(_) => false,
        }
    }
}
