// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-invariant proof tracking for CDEMC cooperative invariant skip.
//!
//! Tracks which individual invariants have been proved safe by PDR,
//! enabling BFS to skip only proved invariants while continuing to
//! check unproved ones.

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

/// Per-invariant proof tracking for CDEMC cooperative invariant skip.
///
/// Tracks which individual invariants have been proved safe by PDR,
/// enabling BFS to skip only proved invariants while continuing to
/// check unproved ones. This is more granular than the binary
/// `invariants_proved` flag which requires ALL invariants proved.
///
/// Thread-safe: each slot is an independent `AtomicBool`, so PDR can
/// mark invariants proved concurrently with BFS reads. The `all_proved`
/// field caches the "all slots true" state to keep the fast path (all
/// proved) a single atomic load.
///
/// Part of #3773.
pub(crate) struct PerInvariantProofState {
    /// Per-invariant proof status. Index matches `config.invariants` order.
    slots: Vec<AtomicBool>,
    /// Cached "all invariants proved" flag. Set to true when the last
    /// unproved invariant is marked proved. This avoids scanning `slots`
    /// on every BFS successor when all invariants are proved.
    all_proved: AtomicBool,
    /// Number of invariants that have been proved. Used to efficiently
    /// detect when all slots are proved without scanning.
    proved_count: AtomicUsize,
}

impl PerInvariantProofState {
    /// Create a new per-invariant proof tracker for `count` invariants.
    pub(crate) fn new(count: usize) -> Self {
        let slots = (0..count).map(|_| AtomicBool::new(false)).collect();
        Self {
            slots,
            all_proved: AtomicBool::new(count == 0),
            proved_count: AtomicUsize::new(0),
        }
    }

    /// Mark invariant at `index` as proved by PDR.
    ///
    /// Returns `true` if this was a new proof (previously unproved).
    /// Thread-safe: uses compare-exchange to avoid double-counting.
    pub(crate) fn mark_proved(&self, index: usize) -> bool {
        if index >= self.slots.len() {
            return false;
        }
        // Only count if transitioning from false to true.
        if self.slots[index]
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
        {
            let new_count = self.proved_count.fetch_add(1, Ordering::AcqRel) + 1;
            if new_count >= self.slots.len() {
                self.all_proved.store(true, Ordering::Release);
            }
            true
        } else {
            false
        }
    }

    /// Mark ALL invariants as proved (e.g., when PDR proves the conjunction).
    pub(crate) fn mark_all_proved(&self) {
        for slot in &self.slots {
            slot.store(true, Ordering::Release);
        }
        self.proved_count.store(self.slots.len(), Ordering::Release);
        self.all_proved.store(true, Ordering::Release);
    }

    /// Check whether invariant at `index` has been proved.
    #[inline]
    pub(crate) fn is_proved(&self, index: usize) -> bool {
        if index >= self.slots.len() {
            return false;
        }
        self.slots[index].load(Ordering::Acquire)
    }

    /// Check whether ALL invariants have been proved (fast path).
    #[inline]
    pub(crate) fn all_proved(&self) -> bool {
        self.all_proved.load(Ordering::Acquire)
    }

    /// Number of invariants that have been proved so far.
    pub(crate) fn proved_count(&self) -> usize {
        self.proved_count.load(Ordering::Acquire)
    }

    /// Total number of tracked invariants.
    pub(crate) fn total_count(&self) -> usize {
        self.slots.len()
    }

    /// Collect indices of unproved invariants into the provided vector.
    ///
    /// Used by BFS to build the subset of invariants that still need
    /// per-state checking. The vector is cleared and re-populated.
    pub(crate) fn collect_unproved_indices(&self, out: &mut Vec<usize>) {
        out.clear();
        for (i, slot) in self.slots.iter().enumerate() {
            if !slot.load(Ordering::Acquire) {
                out.push(i);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_per_invariant_new_zero() {
        // Zero invariants should be trivially all-proved
        let state = PerInvariantProofState::new(0);
        assert!(state.all_proved());
        assert_eq!(state.proved_count(), 0);
        assert_eq!(state.total_count(), 0);
    }

    #[test]
    fn test_per_invariant_mark_and_check() {
        let state = PerInvariantProofState::new(3);
        assert!(!state.all_proved());
        assert_eq!(state.proved_count(), 0);

        assert!(state.mark_proved(0));
        assert!(state.is_proved(0));
        assert!(!state.is_proved(1));
        assert_eq!(state.proved_count(), 1);

        assert!(state.mark_proved(1));
        assert!(state.mark_proved(2));
        assert!(state.all_proved());
        assert_eq!(state.proved_count(), 3);
    }

    #[test]
    fn test_per_invariant_double_mark_no_double_count() {
        let state = PerInvariantProofState::new(2);
        assert!(state.mark_proved(0));
        assert!(!state.mark_proved(0)); // already proved
        assert_eq!(state.proved_count(), 1);
    }

    #[test]
    fn test_per_invariant_out_of_bounds() {
        let state = PerInvariantProofState::new(2);
        assert!(!state.is_proved(5));
        assert!(!state.mark_proved(5));
    }

    #[test]
    fn test_per_invariant_mark_all_proved() {
        let state = PerInvariantProofState::new(3);
        state.mark_all_proved();
        assert!(state.all_proved());
        assert!(state.is_proved(0));
        assert!(state.is_proved(1));
        assert!(state.is_proved(2));
        assert_eq!(state.proved_count(), 3);
    }

    #[test]
    fn test_per_invariant_collect_unproved() {
        let state = PerInvariantProofState::new(4);
        state.mark_proved(1);
        state.mark_proved(3);
        let mut unproved = Vec::new();
        state.collect_unproved_indices(&mut unproved);
        assert_eq!(unproved, vec![0, 2]);
    }
}
