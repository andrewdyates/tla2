// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Contiguous flat state store for cache-friendly BFS iteration.
//!
//! `FlatStateStore` packs `FlatState` buffers into a single contiguous
//! `Vec<i64>` arena. Each state occupies exactly `slots_per_state` i64
//! values at a fixed stride, enabling:
//!
//! 1. **Cache-friendly sequential iteration** — all states are packed
//!    contiguously in memory. BFS frontier iteration scans a single
//!    linear buffer instead of chasing `Box<[i64]>` heap pointers.
//!
//! 2. **Zero per-state allocation overhead** — no `Box`, `Arc`, or
//!    `Vec` metadata per state. The entire frontier is one allocation.
//!
//! 3. **O(1) state access by index** — state `i` is at offset
//!    `i * slots_per_state`. No indirection.
//!
//! 4. **Efficient bulk operations** — `clear()` resets the logical
//!    length without deallocating, so the next BFS level reuses the
//!    same buffer. `reserve()` pre-allocates for expected frontier size.
//!
//! # Design
//!
//! The store holds an `Arc<StateLayout>` and a flat `Vec<i64>` arena.
//! States are appended via `push_flat()` (from `FlatState`) or
//! `push_buffer()` (from raw `&[i64]`). The store does NOT own the
//! `StateLayout` — it borrows it via `Arc` and expects all pushed
//! states to have the same slot count.
//!
//! ## BFS integration
//!
//! ```text
//! Interpreter BFS level N:
//!   for each state in frontier:
//!     generate successors (Value-based)
//!     for each unique successor:
//!       flatten to FlatState via FlatBfsBridge
//!       push to FlatStateStore (next frontier)
//!
//! JIT BFS level N+1:
//!   iterate FlatStateStore as &[i64] slices
//!   pass each slice to compiled BFS step
//! ```
//!
//! Part of #3986: JIT V2 Phase 3 flat state buffer.

use std::sync::Arc;

use super::flat_state::FlatState;
use super::state_layout::StateLayout;

/// Contiguous arena of flat `i64` state buffers.
///
/// All states in the store share the same `StateLayout` and occupy
/// exactly `slots_per_state` i64 values each. The backing buffer
/// is a single `Vec<i64>` for cache-friendly sequential access.
///
/// # Invariants
///
/// - `arena.len() == state_count * slots_per_state`
/// - All pushed buffers have length `== slots_per_state`
/// - `slots_per_state == layout.total_slots()`
///
/// Part of #3986: JIT V2 Phase 3 flat state buffer.
#[derive(Debug, Clone)]
pub(crate) struct FlatStateStore {
    /// Contiguous i64 arena. Length is always `state_count * slots_per_state`.
    arena: Vec<i64>,
    /// Number of i64 slots per state (from the layout).
    slots_per_state: usize,
    /// Number of states currently stored.
    state_count: usize,
    /// Shared layout descriptor.
    layout: Arc<StateLayout>,
}

impl FlatStateStore {
    /// Create an empty store for the given layout.
    ///
    /// No memory is allocated until `push` or `reserve` is called.
    #[must_use]
    pub(crate) fn new(layout: Arc<StateLayout>) -> Self {
        let slots_per_state = layout.total_slots();
        FlatStateStore {
            arena: Vec::new(),
            slots_per_state,
            state_count: 0,
            layout,
        }
    }

    /// Create a store with pre-allocated capacity for `capacity` states.
    ///
    /// Allocates `capacity * slots_per_state` i64 values upfront.
    #[must_use]
    pub(crate) fn with_capacity(layout: Arc<StateLayout>, capacity: usize) -> Self {
        let slots_per_state = layout.total_slots();
        FlatStateStore {
            arena: Vec::with_capacity(capacity * slots_per_state),
            slots_per_state,
            state_count: 0,
            layout,
        }
    }

    /// Push a `FlatState` into the store.
    ///
    /// Returns the index of the newly added state.
    ///
    /// # Panics
    ///
    /// Debug-asserts that the flat state has the correct number of slots.
    pub(crate) fn push_flat(&mut self, flat: &FlatState) -> usize {
        debug_assert_eq!(
            flat.num_slots(),
            self.slots_per_state,
            "FlatStateStore::push_flat: state has {} slots, expected {}",
            flat.num_slots(),
            self.slots_per_state
        );
        self.arena.extend_from_slice(flat.buffer());
        let idx = self.state_count;
        self.state_count += 1;
        idx
    }

    /// Push a raw `&[i64]` buffer into the store.
    ///
    /// Returns the index of the newly added state.
    ///
    /// # Panics
    ///
    /// Debug-asserts that the buffer has the correct number of slots.
    pub(crate) fn push_buffer(&mut self, buffer: &[i64]) -> usize {
        debug_assert_eq!(
            buffer.len(),
            self.slots_per_state,
            "FlatStateStore::push_buffer: buffer has {} slots, expected {}",
            buffer.len(),
            self.slots_per_state
        );
        self.arena.extend_from_slice(buffer);
        let idx = self.state_count;
        self.state_count += 1;
        idx
    }

    /// Get state `i` as a raw `&[i64]` slice.
    ///
    /// Returns `None` if `i >= state_count`.
    #[must_use]
    #[inline]
    pub(crate) fn get(&self, i: usize) -> Option<&[i64]> {
        if i >= self.state_count {
            return None;
        }
        let start = i * self.slots_per_state;
        Some(&self.arena[start..start + self.slots_per_state])
    }

    /// Get state `i` as a `FlatState`.
    ///
    /// Allocates a new `Box<[i64]>` for the flat state. Use `get()` for
    /// zero-copy access when you only need a `&[i64]` reference.
    ///
    /// Returns `None` if `i >= state_count`.
    #[must_use]
    pub(crate) fn get_flat(&self, i: usize) -> Option<FlatState> {
        let slice = self.get(i)?;
        let buffer: Box<[i64]> = slice.to_vec().into_boxed_slice();
        Some(FlatState::from_buffer(buffer, Arc::clone(&self.layout)))
    }

    /// Number of states in the store.
    #[must_use]
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.state_count
    }

    /// Whether the store is empty.
    #[must_use]
    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.state_count == 0
    }

    /// Number of i64 slots per state.
    #[must_use]
    #[inline]
    pub(crate) fn slots_per_state(&self) -> usize {
        self.slots_per_state
    }

    /// Total i64 values stored (state_count * slots_per_state).
    #[must_use]
    #[inline]
    pub(crate) fn total_slots(&self) -> usize {
        self.arena.len()
    }

    /// Total bytes of the backing arena (excluding metadata).
    #[must_use]
    #[inline]
    pub(crate) fn total_bytes(&self) -> usize {
        self.arena.len() * std::mem::size_of::<i64>()
    }

    /// Bytes per state.
    #[must_use]
    #[inline]
    pub(crate) fn bytes_per_state(&self) -> usize {
        self.slots_per_state * std::mem::size_of::<i64>()
    }

    /// Clear all states without deallocating the arena buffer.
    ///
    /// The arena retains its capacity for reuse by the next BFS level.
    /// This is the intended usage pattern: clear between BFS levels,
    /// push new frontier states, iterate.
    pub(crate) fn clear(&mut self) {
        self.arena.clear();
        self.state_count = 0;
    }

    /// Reserve capacity for at least `additional` more states.
    ///
    /// Pre-allocates `additional * slots_per_state` i64 values.
    pub(crate) fn reserve(&mut self, additional: usize) {
        self.arena.reserve(additional * self.slots_per_state);
    }

    /// Current capacity in number of states (before reallocation).
    #[must_use]
    #[inline]
    pub(crate) fn capacity(&self) -> usize {
        if self.slots_per_state == 0 {
            return 0;
        }
        self.arena.capacity() / self.slots_per_state
    }

    /// Iterate over all states as `&[i64]` slices.
    ///
    /// Each item is a slice of `slots_per_state` i64 values representing
    /// one state. Iteration is sequential over the contiguous arena,
    /// maximizing cache locality.
    pub(crate) fn iter(&self) -> FlatStateStoreIter<'_> {
        FlatStateStoreIter {
            arena: &self.arena,
            slots_per_state: self.slots_per_state,
            remaining: self.state_count,
            offset: 0,
        }
    }

    /// Get the shared layout.
    #[must_use]
    #[inline]
    pub(crate) fn layout(&self) -> &Arc<StateLayout> {
        &self.layout
    }

    /// Get the raw arena slice (all states packed contiguously).
    ///
    /// Useful for bulk operations (e.g., passing the entire frontier to
    /// a compiled BFS batch step function).
    #[must_use]
    #[inline]
    pub(crate) fn raw_arena(&self) -> &[i64] {
        &self.arena
    }

    /// Swap-remove state `i` from the store.
    ///
    /// Replaces state `i` with the last state and decrements the count.
    /// O(slots_per_state) for the memcpy. Invalidates the index of the
    /// previously-last state.
    ///
    /// # Panics
    ///
    /// Panics if `i >= state_count`.
    pub(crate) fn swap_remove(&mut self, i: usize) {
        assert!(
            i < self.state_count,
            "FlatStateStore::swap_remove: index {} out of bounds (count {})",
            i,
            self.state_count
        );
        let last = self.state_count - 1;
        if i != last {
            let src_start = last * self.slots_per_state;
            let dst_start = i * self.slots_per_state;
            // Copy last state's slots into the removed state's position.
            self.arena.copy_within(
                src_start..src_start + self.slots_per_state,
                dst_start,
            );
        }
        // Truncate the arena by slots_per_state.
        self.arena
            .truncate(last * self.slots_per_state);
        self.state_count -= 1;
    }
}

/// Iterator over flat states in a `FlatStateStore`.
///
/// Yields `&[i64]` slices of `slots_per_state` i64 values each.
pub(crate) struct FlatStateStoreIter<'a> {
    arena: &'a [i64],
    slots_per_state: usize,
    remaining: usize,
    offset: usize,
}

impl<'a> Iterator for FlatStateStoreIter<'a> {
    type Item = &'a [i64];

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        let start = self.offset;
        let end = start + self.slots_per_state;
        self.offset = end;
        self.remaining -= 1;
        Some(&self.arena[start..end])
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<'a> ExactSizeIterator for FlatStateStoreIter<'a> {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::array_state::ArrayState;
    use crate::state::layout_inference::infer_layout;
    use crate::state::state_layout::VarLayoutKind;
    use crate::var_index::VarRegistry;
    use crate::Value;
    use tla_value::value::IntIntervalFunc;

    fn scalar_layout_3() -> (VarRegistry, Arc<StateLayout>) {
        let registry = VarRegistry::from_names(["x", "y", "z"]);
        let layout = Arc::new(StateLayout::new(
            &registry,
            vec![
                VarLayoutKind::Scalar,
                VarLayoutKind::Scalar,
                VarLayoutKind::Scalar,
            ],
        ));
        (registry, layout)
    }

    fn make_flat(vals: &[i64], layout: &Arc<StateLayout>) -> FlatState {
        FlatState::from_buffer(vals.to_vec().into_boxed_slice(), Arc::clone(layout))
    }

    // ====================================================================
    // Basic operations
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_store_new_empty() {
        let (_reg, layout) = scalar_layout_3();
        let store = FlatStateStore::new(layout);

        assert_eq!(store.len(), 0);
        assert!(store.is_empty());
        assert_eq!(store.slots_per_state(), 3);
        assert_eq!(store.total_slots(), 0);
        assert_eq!(store.total_bytes(), 0);
        assert_eq!(store.bytes_per_state(), 24);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_store_with_capacity() {
        let (_reg, layout) = scalar_layout_3();
        let store = FlatStateStore::with_capacity(Arc::clone(&layout), 100);

        assert_eq!(store.len(), 0);
        assert!(store.is_empty());
        assert!(store.capacity() >= 100);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_store_push_flat_and_get() {
        let (_reg, layout) = scalar_layout_3();
        let mut store = FlatStateStore::new(Arc::clone(&layout));

        let flat = make_flat(&[1, 2, 3], &layout);
        let idx = store.push_flat(&flat);

        assert_eq!(idx, 0);
        assert_eq!(store.len(), 1);
        assert!(!store.is_empty());
        assert_eq!(store.get(0), Some([1, 2, 3].as_slice()));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_store_push_buffer_and_get() {
        let (_reg, layout) = scalar_layout_3();
        let mut store = FlatStateStore::new(Arc::clone(&layout));

        let idx = store.push_buffer(&[10, 20, 30]);
        assert_eq!(idx, 0);
        assert_eq!(store.get(0), Some([10, 20, 30].as_slice()));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_store_push_multiple() {
        let (_reg, layout) = scalar_layout_3();
        let mut store = FlatStateStore::new(Arc::clone(&layout));

        let i0 = store.push_buffer(&[1, 2, 3]);
        let i1 = store.push_buffer(&[4, 5, 6]);
        let i2 = store.push_buffer(&[7, 8, 9]);

        assert_eq!(i0, 0);
        assert_eq!(i1, 1);
        assert_eq!(i2, 2);
        assert_eq!(store.len(), 3);
        assert_eq!(store.total_slots(), 9);
        assert_eq!(store.total_bytes(), 72);

        assert_eq!(store.get(0), Some([1, 2, 3].as_slice()));
        assert_eq!(store.get(1), Some([4, 5, 6].as_slice()));
        assert_eq!(store.get(2), Some([7, 8, 9].as_slice()));
        assert_eq!(store.get(3), None);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_store_get_flat() {
        let (_reg, layout) = scalar_layout_3();
        let mut store = FlatStateStore::new(Arc::clone(&layout));
        store.push_buffer(&[42, -7, 0]);

        let flat = store.get_flat(0).expect("should exist");
        assert_eq!(flat.buffer(), &[42, -7, 0]);
        assert_eq!(flat.num_slots(), 3);
    }

    // ====================================================================
    // Iteration
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_store_iter() {
        let (_reg, layout) = scalar_layout_3();
        let mut store = FlatStateStore::new(Arc::clone(&layout));
        store.push_buffer(&[1, 2, 3]);
        store.push_buffer(&[4, 5, 6]);
        store.push_buffer(&[7, 8, 9]);

        let collected: Vec<&[i64]> = store.iter().collect();
        assert_eq!(collected.len(), 3);
        assert_eq!(collected[0], &[1, 2, 3]);
        assert_eq!(collected[1], &[4, 5, 6]);
        assert_eq!(collected[2], &[7, 8, 9]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_store_iter_exact_size() {
        let (_reg, layout) = scalar_layout_3();
        let mut store = FlatStateStore::new(Arc::clone(&layout));
        store.push_buffer(&[1, 2, 3]);
        store.push_buffer(&[4, 5, 6]);

        let iter = store.iter();
        assert_eq!(iter.len(), 2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_store_iter_empty() {
        let (_reg, layout) = scalar_layout_3();
        let store = FlatStateStore::new(layout);

        let collected: Vec<&[i64]> = store.iter().collect();
        assert!(collected.is_empty());
    }

    // ====================================================================
    // Clear and reuse
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_store_clear_and_reuse() {
        let (_reg, layout) = scalar_layout_3();
        let mut store = FlatStateStore::new(Arc::clone(&layout));

        store.push_buffer(&[1, 2, 3]);
        store.push_buffer(&[4, 5, 6]);
        assert_eq!(store.len(), 2);

        let cap_before = store.capacity();
        store.clear();
        assert_eq!(store.len(), 0);
        assert!(store.is_empty());
        // Capacity should be retained.
        assert!(store.capacity() >= cap_before);

        // Push new states into the cleared store.
        store.push_buffer(&[10, 20, 30]);
        assert_eq!(store.len(), 1);
        assert_eq!(store.get(0), Some([10, 20, 30].as_slice()));
    }

    // ====================================================================
    // Reserve
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_store_reserve() {
        let (_reg, layout) = scalar_layout_3();
        let mut store = FlatStateStore::new(Arc::clone(&layout));

        store.reserve(1000);
        assert!(store.capacity() >= 1000);
        assert_eq!(store.len(), 0);
    }

    // ====================================================================
    // Swap remove
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_store_swap_remove_last() {
        let (_reg, layout) = scalar_layout_3();
        let mut store = FlatStateStore::new(Arc::clone(&layout));
        store.push_buffer(&[1, 2, 3]);
        store.push_buffer(&[4, 5, 6]);

        store.swap_remove(1);
        assert_eq!(store.len(), 1);
        assert_eq!(store.get(0), Some([1, 2, 3].as_slice()));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_store_swap_remove_first() {
        let (_reg, layout) = scalar_layout_3();
        let mut store = FlatStateStore::new(Arc::clone(&layout));
        store.push_buffer(&[1, 2, 3]);
        store.push_buffer(&[4, 5, 6]);
        store.push_buffer(&[7, 8, 9]);

        store.swap_remove(0);
        // State [7,8,9] (last) should replace state [1,2,3] (first).
        assert_eq!(store.len(), 2);
        assert_eq!(store.get(0), Some([7, 8, 9].as_slice()));
        assert_eq!(store.get(1), Some([4, 5, 6].as_slice()));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_store_swap_remove_middle() {
        let (_reg, layout) = scalar_layout_3();
        let mut store = FlatStateStore::new(Arc::clone(&layout));
        store.push_buffer(&[1, 2, 3]);
        store.push_buffer(&[4, 5, 6]);
        store.push_buffer(&[7, 8, 9]);

        store.swap_remove(1);
        assert_eq!(store.len(), 2);
        assert_eq!(store.get(0), Some([1, 2, 3].as_slice()));
        assert_eq!(store.get(1), Some([7, 8, 9].as_slice()));
    }

    // ====================================================================
    // Raw arena access
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_store_raw_arena() {
        let (_reg, layout) = scalar_layout_3();
        let mut store = FlatStateStore::new(Arc::clone(&layout));
        store.push_buffer(&[1, 2, 3]);
        store.push_buffer(&[4, 5, 6]);

        assert_eq!(store.raw_arena(), &[1, 2, 3, 4, 5, 6]);
    }

    // ====================================================================
    // Integration with FlatState roundtrip
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_store_roundtrip_via_flat_state() {
        let registry = VarRegistry::from_names(["pc", "counter"]);
        let func = IntIntervalFunc::new(
            0,
            2,
            vec![Value::SmallInt(10), Value::SmallInt(20), Value::SmallInt(30)],
        );
        let array = ArrayState::from_values(vec![
            Value::SmallInt(1),
            Value::IntFunc(Arc::new(func)),
        ]);
        let layout = Arc::new(infer_layout(&array, &registry));

        // Push via FlatState.
        let flat = FlatState::from_array_state(&array, Arc::clone(&layout));
        let mut store = FlatStateStore::new(Arc::clone(&layout));
        store.push_flat(&flat);

        // Retrieve and verify.
        let retrieved = store.get(0).expect("should exist");
        assert_eq!(retrieved, flat.buffer());

        // Roundtrip back to FlatState and then ArrayState.
        let recovered = store.get_flat(0).expect("should exist");
        let roundtrip = recovered.to_array_state(&registry);
        assert_eq!(
            roundtrip.get(crate::var_index::VarIndex::new(0)),
            Value::SmallInt(1)
        );
        let counter_val = roundtrip.get(crate::var_index::VarIndex::new(1));
        match counter_val {
            Value::IntFunc(ref f) => {
                assert_eq!(f.len(), 3);
                assert_eq!(f.values()[0], Value::SmallInt(10));
                assert_eq!(f.values()[1], Value::SmallInt(20));
                assert_eq!(f.values()[2], Value::SmallInt(30));
            }
            other => panic!("expected IntFunc, got {other:?}"),
        }
    }

    // ====================================================================
    // EWD998-like bulk test (acceptance criterion)
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_store_ewd998_like_bulk() {
        // Simulates pushing 10,000 EWD998-like states (15 slots each) into
        // the store and iterating over them. This validates the cache-friendly
        // sequential access pattern.
        let registry = VarRegistry::from_names([
            "active",
            "color",
            "counter",
            "pending",
            "token_pos",
            "token_q",
            "token_color",
        ]);
        let kinds = vec![
            VarLayoutKind::IntArray {
                lo: 0,
                len: 3,
                elements_are_bool: true,
            },
            VarLayoutKind::IntArray {
                lo: 0,
                len: 3,
                elements_are_bool: false,
            },
            VarLayoutKind::IntArray {
                lo: 0,
                len: 3,
                elements_are_bool: false,
            },
            VarLayoutKind::IntArray {
                lo: 0,
                len: 3,
                elements_are_bool: false,
            },
            VarLayoutKind::Scalar,
            VarLayoutKind::Scalar,
            VarLayoutKind::Scalar,
        ];
        let layout = Arc::new(StateLayout::new(&registry, kinds));
        assert_eq!(layout.total_slots(), 15);

        let mut store = FlatStateStore::with_capacity(Arc::clone(&layout), 10_000);

        // Push 10,000 states with varying content.
        for i in 0..10_000i64 {
            let buf: Vec<i64> = (0..15).map(|slot| i * 15 + slot).collect();
            store.push_buffer(&buf);
        }

        assert_eq!(store.len(), 10_000);
        assert_eq!(store.total_slots(), 150_000);
        assert_eq!(store.total_bytes(), 150_000 * 8);
        assert_eq!(store.bytes_per_state(), 120);
        assert!(
            store.bytes_per_state() < 200,
            "acceptance criterion: <200 bytes per state"
        );

        // Verify all states are accessible and correct.
        for (i, state_buf) in store.iter().enumerate() {
            let expected_first = (i as i64) * 15;
            assert_eq!(state_buf[0], expected_first, "state {i} first slot mismatch");
            assert_eq!(state_buf.len(), 15);
        }

        // Clear and reuse.
        store.clear();
        assert_eq!(store.len(), 0);
        assert!(store.capacity() >= 10_000);
    }

    // ====================================================================
    // Layout accessor
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_store_layout() {
        let (_reg, layout) = scalar_layout_3();
        let store = FlatStateStore::new(Arc::clone(&layout));

        assert_eq!(store.layout().total_slots(), 3);
        assert!(Arc::ptr_eq(store.layout(), &layout));
    }
}
