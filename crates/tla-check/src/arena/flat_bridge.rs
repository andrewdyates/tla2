// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bridge between arena-allocated states and `FlatStateStore`.
//!
//! `ArenaFlatBridge` manages a reusable scratch `Vec<i64>` buffer for
//! flattening successor states into the contiguous `FlatStateStore`
//! arena. Instead of allocating a new `Box<[i64]>` per state (what
//! `FlatState::from_array_state` does), the bridge writes into a
//! reused buffer and pushes a `&[i64]` slice directly.
//!
//! # Usage
//!
//! ```text
//! let mut bridge = ArenaFlatBridge::new(slots_per_state);
//! // For each successor:
//!   bridge.push_raw(flat_buffer, &mut store);   // already-flat i64 data
//! // At end of level:
//!   store.clear();  // reuse next level
//! ```
//!
//! Part of #3990: JIT V2 Phase 7 — per-worker bump arenas, zero malloc.

use crate::state::FlatStateStore;

/// Reusable bridge for pushing states into a `FlatStateStore` without
/// per-state allocation.
///
/// Owns a scratch `Vec<i64>` that is allocated once and reused across
/// all successor pushes within a BFS level (and across levels, since
/// `FlatStateStore::clear()` reuses its backing arena).
///
/// Part of #3990.
#[derive(Debug)]
pub(crate) struct ArenaFlatBridge {
    /// Reusable scratch buffer for state flattening.
    /// Length is always `slots_per_state` when used; capacity is retained.
    scratch: Vec<i64>,
    /// Number of i64 slots per state (from `StateLayout::total_slots()`).
    slots_per_state: usize,
    /// Cumulative count of states pushed through this bridge.
    states_bridged: usize,
}

impl ArenaFlatBridge {
    /// Create a new bridge for states with `slots_per_state` i64 slots.
    #[must_use]
    pub(crate) fn new(slots_per_state: usize) -> Self {
        ArenaFlatBridge {
            scratch: vec![0i64; slots_per_state],
            slots_per_state,
            states_bridged: 0,
        }
    }

    /// Push an already-flat `&[i64]` buffer into the store.
    ///
    /// This is the fast path when the caller already has i64 data (e.g.,
    /// from a `ScratchBuffer` or arena allocation). Zero copies beyond
    /// the `extend_from_slice` inside `FlatStateStore::push_buffer`.
    ///
    /// # Panics
    ///
    /// Debug-asserts that `buffer.len() == slots_per_state`.
    #[inline]
    pub(crate) fn push_raw(&mut self, buffer: &[i64], store: &mut FlatStateStore) -> usize {
        debug_assert_eq!(
            buffer.len(),
            self.slots_per_state,
            "ArenaFlatBridge::push_raw: buffer len {} != slots_per_state {}",
            buffer.len(),
            self.slots_per_state
        );
        self.states_bridged += 1;
        store.push_buffer(buffer)
    }

    /// Access the scratch buffer for in-place state assembly.
    ///
    /// The caller can write i64 slot values into this buffer and then
    /// call `push_scratch(store)` to push it into the store. This
    /// avoids allocating a temporary `Vec<i64>` per successor.
    #[inline]
    pub(crate) fn scratch_mut(&mut self) -> &mut [i64] {
        &mut self.scratch
    }

    /// Push the current scratch buffer contents into the store.
    ///
    /// This is the two-step pattern: (1) write into `scratch_mut()`,
    /// (2) call `push_scratch()` to commit to the store.
    #[inline]
    pub(crate) fn push_scratch(&mut self, store: &mut FlatStateStore) -> usize {
        self.states_bridged += 1;
        store.push_buffer(&self.scratch)
    }

    /// Number of i64 slots per state.
    #[must_use]
    #[inline]
    pub(crate) fn slots_per_state(&self) -> usize {
        self.slots_per_state
    }

    /// Cumulative count of states pushed through this bridge.
    #[must_use]
    #[inline]
    pub(crate) fn states_bridged(&self) -> usize {
        self.states_bridged
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::state::{StateLayout, VarLayoutKind};
    use crate::var_index::VarRegistry;

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

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_arena_flat_bridge_push_raw_basic() {
        let (_reg, layout) = scalar_layout_3();
        let mut store = FlatStateStore::new(Arc::clone(&layout));
        let mut bridge = ArenaFlatBridge::new(3);

        let idx = bridge.push_raw(&[10, 20, 30], &mut store);
        assert_eq!(idx, 0);
        assert_eq!(store.len(), 1);
        assert_eq!(store.get(0), Some([10, 20, 30].as_slice()));
        assert_eq!(bridge.states_bridged(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_arena_flat_bridge_push_raw_multiple() {
        let (_reg, layout) = scalar_layout_3();
        let mut store = FlatStateStore::new(Arc::clone(&layout));
        let mut bridge = ArenaFlatBridge::new(3);

        bridge.push_raw(&[1, 2, 3], &mut store);
        bridge.push_raw(&[4, 5, 6], &mut store);
        bridge.push_raw(&[7, 8, 9], &mut store);

        assert_eq!(store.len(), 3);
        assert_eq!(bridge.states_bridged(), 3);
        assert_eq!(store.get(0), Some([1, 2, 3].as_slice()));
        assert_eq!(store.get(1), Some([4, 5, 6].as_slice()));
        assert_eq!(store.get(2), Some([7, 8, 9].as_slice()));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_arena_flat_bridge_scratch_workflow() {
        let (_reg, layout) = scalar_layout_3();
        let mut store = FlatStateStore::new(Arc::clone(&layout));
        let mut bridge = ArenaFlatBridge::new(3);

        // Write into scratch buffer, then push.
        let scratch = bridge.scratch_mut();
        scratch[0] = 100;
        scratch[1] = 200;
        scratch[2] = 300;
        let idx = bridge.push_scratch(&mut store);

        assert_eq!(idx, 0);
        assert_eq!(store.get(0), Some([100, 200, 300].as_slice()));
        assert_eq!(bridge.states_bridged(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_arena_flat_bridge_scratch_reuse() {
        let (_reg, layout) = scalar_layout_3();
        let mut store = FlatStateStore::new(Arc::clone(&layout));
        let mut bridge = ArenaFlatBridge::new(3);

        // First state.
        {
            let s = bridge.scratch_mut();
            s[0] = 1;
            s[1] = 2;
            s[2] = 3;
        }
        bridge.push_scratch(&mut store);

        // Second state -- reusing the same scratch buffer.
        {
            let s = bridge.scratch_mut();
            s[0] = 4;
            s[1] = 5;
            s[2] = 6;
        }
        bridge.push_scratch(&mut store);

        assert_eq!(store.len(), 2);
        assert_eq!(store.get(0), Some([1, 2, 3].as_slice()));
        assert_eq!(store.get(1), Some([4, 5, 6].as_slice()));
        assert_eq!(bridge.states_bridged(), 2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_arena_flat_bridge_store_clear_and_reuse() {
        let (_reg, layout) = scalar_layout_3();
        let mut store = FlatStateStore::new(Arc::clone(&layout));
        let mut bridge = ArenaFlatBridge::new(3);

        // BFS level 1.
        bridge.push_raw(&[10, 20, 30], &mut store);
        bridge.push_raw(&[40, 50, 60], &mut store);
        assert_eq!(store.len(), 2);

        // Clear store (BFS level boundary), bridge stats persist.
        store.clear();
        assert_eq!(store.len(), 0);
        assert_eq!(bridge.states_bridged(), 2);

        // BFS level 2.
        bridge.push_raw(&[70, 80, 90], &mut store);
        assert_eq!(store.len(), 1);
        assert_eq!(store.get(0), Some([70, 80, 90].as_slice()));
        assert_eq!(bridge.states_bridged(), 3);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_arena_flat_bridge_slots_per_state() {
        let bridge = ArenaFlatBridge::new(7);
        assert_eq!(bridge.slots_per_state(), 7);
        assert_eq!(bridge.states_bridged(), 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_arena_flat_bridge_bulk_push_1000() {
        let (_reg, layout) = scalar_layout_3();
        let mut store = FlatStateStore::with_capacity(Arc::clone(&layout), 1000);
        let mut bridge = ArenaFlatBridge::new(3);

        for i in 0..1000i64 {
            bridge.push_raw(&[i, i * 10, i * 100], &mut store);
        }

        assert_eq!(store.len(), 1000);
        assert_eq!(bridge.states_bridged(), 1000);
        assert_eq!(store.get(0), Some([0, 0, 0].as_slice()));
        assert_eq!(store.get(999), Some([999, 9990, 99900].as_slice()));
    }
}
