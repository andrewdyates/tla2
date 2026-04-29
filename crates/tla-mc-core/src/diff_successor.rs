// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Generic diff-based successor state representation.
//!
//! `DiffSuccessor<K, V>` stores only the changed slots of a successor state
//! relative to its parent, avoiding full state cloning during enumeration.
//! The full state can be materialized later (only for unique states, typically
//! ~5% of successors in model checking workloads).
//!
//! This module is domain-agnostic: `K` is the index type (e.g., `VarIndex` for
//! TLA+, `PlaceIdx` for Petri nets) and `V` is the value/delta type.
//!
//! # Performance
//!
//! Uses `SmallVec<[(K, V); 4]>` so that transitions touching 1-4 slots stay
//! entirely on the stack, eliminating heap allocation for the common case.

use smallvec::SmallVec;

/// Inline capacity for diff changes.
///
/// Most transitions change 1-4 variables/places. Keeping changes inline
/// avoids heap allocation for the common case, reducing allocator pressure
/// in the hot path.
pub const DIFF_INLINE_CAPACITY: usize = 4;

/// Type alias for the changes storage.
///
/// `SmallVec` stores up to [`DIFF_INLINE_CAPACITY`] entries inline (on the
/// stack). When the number of changes exceeds this, it spills to the heap
/// transparently.
pub type DiffChanges<K, V> = SmallVec<[(K, V); DIFF_INLINE_CAPACITY]>;

/// A compact representation of a successor state as a diff from a parent state.
///
/// Only the changed (key, value) pairs and the result fingerprint are stored.
/// The full state is materialized on demand via [`DiffSuccessor::materialize`].
///
/// # Type Parameters
///
/// - `K`: Index/key type (e.g., variable index, place index). Must be `Copy`
///   so that keys can be cheaply duplicated during materialization.
/// - `V`: Value/delta type (e.g., TLA+ `Value`, token count `u64`).
///
/// # Fingerprint
///
/// The `fingerprint` field holds a pre-computed deduplication fingerprint of
/// the result state, or `0` as a placeholder when fingerprinting is deferred.
/// The fingerprint type `F` is generic to support different fingerprint widths
/// (u64, u128, etc.).
#[derive(Clone)]
pub struct DiffSuccessor<K, V, F = u64> {
    /// Fingerprint of the result state (0 if deferred).
    pub fingerprint: F,
    /// Changes from the parent state: `(index, new_value)`.
    ///
    /// Uses `SmallVec` to avoid heap allocation for small change sets.
    pub changes: DiffChanges<K, V>,
}

impl<K, V, F: Default> DiffSuccessor<K, V, F> {
    /// Create a new `DiffSuccessor` with the given fingerprint and changes.
    #[inline]
    pub fn new(fingerprint: F, changes: DiffChanges<K, V>) -> Self {
        Self {
            fingerprint,
            changes,
        }
    }

    /// Create a `DiffSuccessor` from changes only, with a placeholder fingerprint.
    ///
    /// The fingerprint field is set to `F::default()` (typically zero).
    /// Callers should compute the actual fingerprint before use in dedup checks.
    #[inline]
    pub fn from_changes(changes: DiffChanges<K, V>) -> Self {
        Self {
            fingerprint: F::default(),
            changes,
        }
    }
}

impl<K, V, F> DiffSuccessor<K, V, F>
where
    K: Copy,
{
    /// Materialize this diff into a full state by applying changes to the parent.
    ///
    /// The `apply` closure receives `(state, key, value)` for each change and
    /// should write `value` into `state` at position `key`.
    ///
    /// Returns the mutated state with the fingerprint.
    #[inline]
    pub fn materialize<S, A>(self, mut parent: S, mut apply: A) -> (S, F)
    where
        A: FnMut(&mut S, K, V),
    {
        for (key, value) in self.changes {
            apply(&mut parent, key, value);
        }
        (parent, self.fingerprint)
    }

    /// Materialize this diff into an existing target state, reusing its allocation.
    ///
    /// The `copy_parent` closure initializes `target` from the parent state.
    /// Then each change is applied via the `apply` closure.
    #[inline]
    pub fn materialize_into<S, C, A>(self, target: &mut S, copy_parent: C, mut apply: A) -> F
    where
        C: FnOnce(&mut S),
        A: FnMut(&mut S, K, V),
    {
        copy_parent(target);
        for (key, value) in self.changes {
            apply(target, key, value);
        }
        self.fingerprint
    }

    /// Return the number of changed slots.
    #[inline]
    #[must_use]
    pub fn num_changes(&self) -> usize {
        self.changes.len()
    }

    /// Return `true` if this diff contains no changes (stuttering transition).
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.changes.is_empty()
    }
}

/// Compute an incremental fingerprint by XOR-folding per-slot contributions.
///
/// Given a base `combined_xor` (the XOR-fold of the parent state), this function
/// XOR-outs old slot contributions and XOR-ins new slot contributions for each
/// changed slot.
///
/// # Arguments
///
/// - `base_xor`: The combined XOR fingerprint of the parent state.
/// - `changes`: The `(key, new_value)` pairs.
/// - `old_value_fp`: Closure returning the fingerprint of the old value at `key`.
/// - `new_value_fp`: Closure returning the fingerprint of the new value.
/// - `salt`: Closure returning a per-slot salt for `key` (for mixing).
///
/// # Returns
///
/// The updated `combined_xor` after applying all changes.
#[inline]
pub fn incremental_xor_fingerprint<K, V, OldFp, NewFp, Salt>(
    base_xor: u64,
    changes: &[(K, V)],
    mut old_value_fp: OldFp,
    mut new_value_fp: NewFp,
    mut salt: Salt,
) -> u64
where
    K: Copy,
    OldFp: FnMut(K) -> u64,
    NewFp: FnMut(&V) -> u64,
    Salt: FnMut(K) -> u64,
{
    let mut combined_xor = base_xor;
    for (key, new_val) in changes {
        let old_fp = old_value_fp(*key);
        let new_fp = new_value_fp(new_val);
        if old_fp != new_fp {
            let s = salt(*key);
            let old_contrib = s.wrapping_mul(old_fp.wrapping_add(1));
            let new_contrib = s.wrapping_mul(new_fp.wrapping_add(1));
            combined_xor ^= old_contrib ^ new_contrib;
        }
    }
    combined_xor
}

/// Finalize a combined XOR value into a fingerprint using FNV-style mixing.
///
/// This matches the finalization used in tla-check: multiply by a prime and
/// fold the upper bits back in. The exact prime is caller-chosen so that
/// different domains can use different finalizers if needed.
#[inline]
#[must_use]
pub fn finalize_xor(combined_xor: u64, prime: u64) -> u64 {
    let h = combined_xor.wrapping_mul(prime);
    h ^ (h >> 32)
}

impl<K, V, F> std::fmt::Debug for DiffSuccessor<K, V, F>
where
    F: std::fmt::LowerHex,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "DiffSuccessor(fp={:016x}, {} changes)",
            self.fingerprint,
            self.changes.len()
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A simple index type for testing (mimics PlaceIdx / VarIndex).
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    struct Idx(u32);

    // ---------------------------------------------------------------
    // Construction tests
    // ---------------------------------------------------------------

    #[test]
    fn test_new_diff_successor() {
        let changes: DiffChanges<Idx, i64> = smallvec::smallvec![(Idx(0), 10), (Idx(2), 30),];
        let diff = DiffSuccessor::new(0xABCD_u64, changes);
        assert_eq!(diff.fingerprint, 0xABCD);
        assert_eq!(diff.num_changes(), 2);
        assert!(!diff.is_empty());
    }

    #[test]
    fn test_from_changes_placeholder_fingerprint() {
        let changes: DiffChanges<Idx, i64> = smallvec::smallvec![(Idx(1), 42)];
        let diff = DiffSuccessor::<Idx, i64>::from_changes(changes);
        assert_eq!(diff.fingerprint, 0_u64);
        assert_eq!(diff.num_changes(), 1);
    }

    #[test]
    fn test_empty_diff() {
        let diff = DiffSuccessor::<Idx, i64>::from_changes(DiffChanges::new());
        assert!(diff.is_empty());
        assert_eq!(diff.num_changes(), 0);
    }

    // ---------------------------------------------------------------
    // Materialization tests
    // ---------------------------------------------------------------

    #[test]
    fn test_materialize_produces_correct_state() {
        // Parent state: [100, 200, 300, 400]
        let parent = vec![100_i64, 200, 300, 400];
        let changes: DiffChanges<Idx, i64> = smallvec::smallvec![(Idx(1), 999), (Idx(3), 777),];
        let diff = DiffSuccessor::new(0xFF_u64, changes);

        let (result, fp) = diff.materialize(parent, |state, key, value| {
            state[key.0 as usize] = value;
        });

        assert_eq!(result, vec![100, 999, 300, 777]);
        assert_eq!(fp, 0xFF);
    }

    #[test]
    fn test_materialize_into_reuses_allocation() {
        let parent = vec![10_i64, 20, 30];
        let changes: DiffChanges<Idx, i64> = smallvec::smallvec![(Idx(0), 99)];
        let diff = DiffSuccessor::new(0x42_u64, changes);

        let mut target = vec![0_i64; 3]; // pre-allocated buffer
        let fp = diff.materialize_into(
            &mut target,
            |t| t.clone_from_slice(&parent),
            |state, key, value| {
                state[key.0 as usize] = value;
            },
        );

        assert_eq!(target, vec![99, 20, 30]);
        assert_eq!(fp, 0x42);
    }

    // ---------------------------------------------------------------
    // Incremental fingerprint tests
    // ---------------------------------------------------------------

    #[test]
    fn test_incremental_fingerprint_matches_full_computation() {
        // Simulate a state with 4 slots, each having a "fingerprint" equal to value.
        let parent_values: Vec<u64> = vec![10, 20, 30, 40];
        let salts: Vec<u64> = vec![7, 13, 19, 29];

        // Compute base combined_xor from parent.
        let base_xor: u64 = parent_values
            .iter()
            .zip(salts.iter())
            .map(|(v, s)| s.wrapping_mul(v.wrapping_add(1)))
            .fold(0_u64, |acc, x| acc ^ x);

        // Changes: slot 1 goes from 20 -> 99, slot 3 goes from 40 -> 55.
        let changes: Vec<(Idx, u64)> = vec![(Idx(1), 99), (Idx(3), 55)];

        let updated_xor = incremental_xor_fingerprint(
            base_xor,
            &changes,
            |key| parent_values[key.0 as usize],
            |val| *val,
            |key| salts[key.0 as usize],
        );

        // Compute full-state fingerprint for comparison.
        let mut full_values = parent_values.clone();
        full_values[1] = 99;
        full_values[3] = 55;
        let full_xor: u64 = full_values
            .iter()
            .zip(salts.iter())
            .map(|(v, s)| s.wrapping_mul(v.wrapping_add(1)))
            .fold(0_u64, |acc, x| acc ^ x);

        assert_eq!(updated_xor, full_xor);

        // Finalized fingerprints should also match.
        let prime = 0x00000100000001B3_u64; // FNV prime
        assert_eq!(
            finalize_xor(updated_xor, prime),
            finalize_xor(full_xor, prime)
        );
    }

    #[test]
    fn test_incremental_fingerprint_no_change_is_identity() {
        let parent_values: Vec<u64> = vec![5, 10, 15];
        let salts: Vec<u64> = vec![3, 7, 11];

        let base_xor: u64 = parent_values
            .iter()
            .zip(salts.iter())
            .map(|(v, s)| s.wrapping_mul(v.wrapping_add(1)))
            .fold(0_u64, |acc, x| acc ^ x);

        // Change slot 0 from 5 -> 5 (no actual change).
        let changes: Vec<(Idx, u64)> = vec![(Idx(0), 5)];
        let updated_xor = incremental_xor_fingerprint(
            base_xor,
            &changes,
            |key| parent_values[key.0 as usize],
            |val| *val,
            |key| salts[key.0 as usize],
        );

        assert_eq!(
            updated_xor, base_xor,
            "no-op change should not alter fingerprint"
        );
    }

    // ---------------------------------------------------------------
    // SmallVec inline/spill behavior
    // ---------------------------------------------------------------

    #[test]
    fn test_smallvec_stays_inline_for_small_changes() {
        let mut changes: DiffChanges<Idx, i64> = DiffChanges::new();
        for i in 0..DIFF_INLINE_CAPACITY {
            changes.push((Idx(i as u32), i as i64));
        }
        assert!(
            !changes.spilled(),
            "should stay inline for <= {DIFF_INLINE_CAPACITY} changes"
        );
    }

    #[test]
    fn test_smallvec_spills_for_large_changes() {
        let mut changes: DiffChanges<Idx, i64> = DiffChanges::new();
        for i in 0..=DIFF_INLINE_CAPACITY {
            changes.push((Idx(i as u32), i as i64));
        }
        assert!(
            changes.spilled(),
            "should spill to heap for > {DIFF_INLINE_CAPACITY} changes"
        );
    }

    // ---------------------------------------------------------------
    // finalize_xor
    // ---------------------------------------------------------------

    #[test]
    fn test_finalize_xor_deterministic() {
        let prime = 0x00000100000001B3_u64;
        let a = finalize_xor(12345, prime);
        let b = finalize_xor(12345, prime);
        assert_eq!(a, b);

        // Different inputs produce different outputs.
        let c = finalize_xor(12346, prime);
        assert_ne!(a, c);
    }

    // ---------------------------------------------------------------
    // Debug formatting
    // ---------------------------------------------------------------

    #[test]
    fn test_debug_format() {
        let diff = DiffSuccessor::new(0xDEAD_BEEF_u64, smallvec::smallvec![(Idx(0), 1_i64)]);
        let dbg = format!("{diff:?}");
        assert!(dbg.contains("DiffSuccessor"));
        assert!(dbg.contains("deadbeef"));
        assert!(dbg.contains("1 changes"));
    }
}
