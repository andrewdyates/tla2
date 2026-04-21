// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `SeqValue` flat-view materialization, fingerprint caching, and mutation helpers.

use super::super::Value;
use super::{SeqValue, SEQ_VALUE_FP_UNSET};
use std::sync::atomic::Ordering as AtomicOrdering;
use std::sync::{Arc, OnceLock};

impl SeqValue {
    #[inline]
    fn materialize_flat_view(&self) -> Arc<[Value]> {
        Arc::from(self.elements.iter().cloned().collect::<Vec<_>>())
    }

    #[inline]
    pub(crate) fn flat_slice(&self) -> &[Value] {
        self.flat_view
            .get_or_init(|| self.materialize_flat_view())
            .as_ref()
    }

    #[cfg(test)]
    pub(crate) fn cached_flat_view(&self) -> Option<&Arc<[Value]>> {
        self.flat_view.get()
    }

    /// Convert to a Vec (for backward compatibility and operations that need slices).
    #[inline]
    pub fn to_vec(&self) -> Vec<Value> {
        self.flat_slice().to_vec()
    }

    // ========================================================================
    // Fingerprint caching
    // ========================================================================

    /// Get cached additive (dedup) fingerprint if available.
    #[inline]
    pub fn get_additive_fp(&self) -> Option<u64> {
        let cached = self.additive_fp.load(AtomicOrdering::Relaxed);
        (cached != SEQ_VALUE_FP_UNSET).then_some(cached)
    }

    /// Cache an additive (dedup) fingerprint value.
    #[inline]
    pub fn cache_additive_fp(&self, fp: u64) -> u64 {
        let _ = self.additive_fp.compare_exchange(
            SEQ_VALUE_FP_UNSET,
            fp,
            AtomicOrdering::Relaxed,
            AtomicOrdering::Relaxed,
        );
        fp
    }

    /// Check if two SeqValues share the same underlying storage (pointer equality).
    /// Note: im::Vector uses structural sharing, so this checks if they share the same root.
    #[inline]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        #[cfg(feature = "im")]
        {
            self.elements.ptr_eq(&other.elements)
        }
        #[cfg(not(feature = "im"))]
        {
            std::ptr::eq(self, other)
        }
    }

    /// Take the value at a 0-based index, replacing it with a placeholder.
    /// Returns the old value for the caller to use in recursive EXCEPT evaluation.
    ///
    /// This enables the take/restore pattern used by nested EXCEPT evaluation.
    /// By moving the value out instead of cloning, the inner Arc refcount stays
    /// at 1 so recursive `Arc::make_mut` calls are free (no clone).
    ///
    /// After calling this, the sequence is in an inconsistent state. The caller
    /// MUST call `restore_at` before using the sequence, or drop it on error.
    /// Part of #3168.
    #[inline]
    pub fn take_at(&mut self, index: usize) -> Option<Value> {
        let slot = self.elements.get_mut(index)?;
        Some(std::mem::replace(slot, Value::Bool(false)))
    }

    /// Restore a value at the given 0-based index after a [`take_at`] call.
    /// Resets cached fingerprint and flat view.
    /// Part of #3168.
    #[inline]
    pub fn restore_at(&mut self, index: usize, value: Value) {
        if let Some(slot) = self.elements.get_mut(index) {
            *slot = value;
        }
        self.reset_cache();
    }

    /// Reset cached fingerprints and flat view after mutation.
    /// Part of #3168.
    #[inline]
    fn reset_cache(&mut self) {
        self.additive_fp
            .store(SEQ_VALUE_FP_UNSET, AtomicOrdering::Relaxed);
        self.flat_view = OnceLock::new();
    }

    /// Update element at index (0-indexed) - O(log n) with structural sharing.
    ///
    /// Returns a new SeqValue with the element at `index` replaced by `value`.
    /// Uses im::Vector's structural sharing for efficient updates.
    ///
    /// # Panics
    /// Panics if index >= len().
    #[inline]
    pub fn except(&self, index: usize, value: Value) -> Self {
        Self::with_elements(self.elements.update(index, value))
    }

    /// Update element at index (0-indexed) with short-circuit - O(log n).
    ///
    /// Returns a new SeqValue if the value changed, or clones self if unchanged.
    #[inline]
    pub fn except_if_changed(&self, index: usize, value: Value) -> Self {
        if let Some(existing) = self.elements.get(index) {
            if existing == &value {
                return self.clone();
            }
        }
        self.except(index, value)
    }
}
