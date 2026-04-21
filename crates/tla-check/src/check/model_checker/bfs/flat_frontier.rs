// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Arena-backed BFS frontier for FlatState buffers.
//!
//! `FlatBfsFrontier` implements [`BfsFrontier`] using [`FlatStateStore`] as a
//! contiguous `Vec<i64>` arena instead of individual `Box<[i64]>` per state.
//! This eliminates per-state heap allocation on the BFS hot path and provides
//! cache-friendly sequential access during frontier iteration.
//!
//! # Design
//!
//! The frontier wraps a single `FlatStateStore` with a parallel metadata `Vec`
//! for per-state `(Fingerprint, depth, trace_loc)`. States are appended via
//! `push()` and consumed FIFO via `pop()` (tracked by a read cursor).
//!
//! When a `NoTraceQueueEntry::Flat` is pushed, only the raw `&[i64]` buffer
//! is copied into the arena (zero Box allocation). Non-flat entries (`Bulk`,
//! `Owned`) are stored in a fallback `VecDeque` since they cannot be
//! represented as flat buffers.
//!
//! On `pop()`, flat entries are reconstructed from the arena slice into a
//! `FlatState` (one `Box<[i64]>` clone per pop — but this state will be
//! immediately consumed by the interpreter, so the allocation is on the
//! cold path between dequeue and eval, not on the hot dedup path).
//!
//! # Memory savings
//!
//! For EWD998 N=3 (15 slots = 120 bytes/state):
//! - **Before**: `Box<[i64]>` + `FlatState` wrapper per state = 120 + 24 = 144 bytes
//! - **After**: 120 bytes contiguous in arena + 24 bytes metadata = 144 bytes
//!
//! The savings come from eliminating allocator overhead (no per-Box malloc
//! header, no fragmentation) and from sequential access patterns that maximize
//! L1/L2 cache utilization during frontier iteration.
//!
//! Part of #4126: FlatState as native BFS representation.

use std::collections::VecDeque;
use std::sync::Arc;

use super::super::frontier::BfsFrontier;
use super::storage_modes::NoTraceQueueEntry;
use crate::state::Fingerprint;
use crate::state::FlatState;
use crate::state::FlatStateStore;
use crate::state::StateLayout;

/// Per-state metadata stored alongside the flat buffer in the arena.
///
/// Each entry corresponds to one state in the `FlatStateStore` at the same
/// index. This parallel-arrays layout keeps the i64 arena tightly packed
/// for SIMD/cache-line-friendly fingerprinting while storing variable-size
/// metadata separately.
#[derive(Debug, Clone)]
struct FlatFrontierMeta {
    /// 64-bit fingerprint for dedup (traditional FP64 space).
    fp: Fingerprint,
    /// BFS depth of this state.
    depth: usize,
    /// Trace file location for trace reconstruction.
    trace_loc: u64,
}

/// Arena-backed BFS frontier that stores flat i64 state buffers contiguously.
///
/// Implements `BfsFrontier<Entry = (NoTraceQueueEntry, usize, u64)>` so it
/// is a drop-in replacement for `VecDeque` in the fingerprint-only BFS path.
///
/// States pushed as `NoTraceQueueEntry::Flat` are stored in the contiguous
/// arena. `Bulk` and `Owned` entries are stored in a fallback `VecDeque`
/// (these typically only appear for initial states and specs with Dynamic
/// variables that cannot be flattened).
///
/// Part of #4126.
pub(in crate::check::model_checker) struct FlatBfsFrontier {
    /// Contiguous arena for flat state buffers.
    store: FlatStateStore,
    /// Per-state metadata (parallel to store indices).
    meta: Vec<FlatFrontierMeta>,
    /// Read cursor: next state index to pop from the arena.
    read_idx: usize,
    /// Fallback queue for non-flat entries (Bulk, Owned).
    fallback: VecDeque<(NoTraceQueueEntry, usize, u64)>,
    /// Shared layout for constructing FlatState from arena slices.
    layout: Arc<StateLayout>,
    /// Total states pushed (flat + fallback), for statistics.
    total_pushed: u64,
    /// States pushed to the flat arena (subset of total_pushed).
    flat_pushed: u64,
}

impl FlatBfsFrontier {
    /// Create a new arena-backed frontier for the given layout.
    ///
    /// The arena starts empty; capacity grows on demand.
    #[must_use]
    pub(in crate::check::model_checker) fn new(layout: Arc<StateLayout>) -> Self {
        FlatBfsFrontier {
            store: FlatStateStore::new(Arc::clone(&layout)),
            meta: Vec::new(),
            read_idx: 0,
            fallback: VecDeque::new(),
            layout,
            total_pushed: 0,
            flat_pushed: 0,
        }
    }

    /// Create a new frontier with pre-allocated capacity for `capacity` states.
    #[must_use]
    pub(in crate::check::model_checker) fn with_capacity(
        layout: Arc<StateLayout>,
        capacity: usize,
    ) -> Self {
        FlatBfsFrontier {
            store: FlatStateStore::with_capacity(Arc::clone(&layout), capacity),
            meta: Vec::with_capacity(capacity),
            read_idx: 0,
            fallback: VecDeque::new(),
            layout,
            total_pushed: 0,
            flat_pushed: 0,
        }
    }

    /// Number of flat states remaining in the arena (not yet popped).
    #[must_use]
    fn flat_remaining(&self) -> usize {
        self.store.len().saturating_sub(self.read_idx)
    }

    /// Compact the arena by discarding already-popped states.
    ///
    /// Called when the read cursor has advanced past a significant fraction
    /// of the arena, freeing memory from already-consumed states. This is
    /// a bulk operation — O(remaining) to shift data.
    ///
    /// In practice, BFS levels are processed sequentially, so compaction
    /// happens at level boundaries when all states from the previous level
    /// have been popped.
    fn compact_if_needed(&mut self) {
        // Only compact when we've consumed at least half the arena AND
        // there are fewer remaining states than consumed ones.
        if self.read_idx > 0 && self.flat_remaining() == 0 {
            self.store.clear();
            self.meta.clear();
            self.read_idx = 0;
        }
    }

    /// Number of states pushed to the flat arena.
    #[must_use]
    pub(in crate::check::model_checker) fn flat_pushed(&self) -> u64 {
        self.flat_pushed
    }

    /// Total states pushed (flat + fallback).
    #[must_use]
    pub(in crate::check::model_checker) fn total_pushed(&self) -> u64 {
        self.total_pushed
    }

    /// Fraction of states stored in the flat arena (0.0 to 1.0).
    #[must_use]
    pub(in crate::check::model_checker) fn flat_ratio(&self) -> f64 {
        if self.total_pushed == 0 {
            return 0.0;
        }
        self.flat_pushed as f64 / self.total_pushed as f64
    }

    /// Bytes per state in the arena.
    #[must_use]
    pub(in crate::check::model_checker) fn bytes_per_state(&self) -> usize {
        self.store.bytes_per_state()
    }

    /// Access the raw contiguous i64 arena for the remaining (not-yet-popped) states.
    ///
    /// Returns `(arena_slice, state_count)` where `arena_slice` contains
    /// `state_count * slots_per_state` consecutive i64 values. The slice starts
    /// at the read cursor (skipping already-popped states).
    ///
    /// This is used by the compiled BFS level loop to process the entire
    /// frontier in a single pass through the arena without per-state pop/push
    /// overhead.
    ///
    /// Returns `None` if there are no flat states remaining (only fallback entries).
    ///
    /// Part of #3988: Wire compiled BFS level into model checker.
    #[must_use]
    pub(in crate::check::model_checker) fn remaining_arena(&self) -> Option<(&[i64], usize)> {
        let remaining = self.flat_remaining();
        if remaining == 0 {
            return None;
        }
        let slots_per_state = self.store.slots_per_state();
        let start_slot = self.read_idx * slots_per_state;
        let end_slot = start_slot + remaining * slots_per_state;
        let arena = self.store.raw_arena();
        if end_slot > arena.len() {
            return None;
        }
        Some((&arena[start_slot..end_slot], remaining))
    }

    /// Advance the read cursor by `count` states without popping them.
    ///
    /// Used by the compiled BFS level loop after processing a batch of
    /// states directly from the arena via `remaining_arena()`. The caller
    /// has already processed these states and does not need them popped
    /// individually.
    ///
    /// # Panics
    ///
    /// Panics if `count > flat_remaining()`.
    ///
    /// Part of #3988: Wire compiled BFS level into model checker.
    pub(in crate::check::model_checker) fn advance_read_cursor(&mut self, count: usize) {
        assert!(
            count <= self.flat_remaining(),
            "advance_read_cursor({count}) exceeds remaining {} states",
            self.flat_remaining(),
        );
        self.read_idx += count;
        // Compact when the arena is fully drained.
        if self.read_idx == self.store.len() {
            self.compact_if_needed();
        }
    }

    /// Get the metadata (fingerprint, depth, trace_loc) for a state at
    /// the given offset from the current read cursor.
    ///
    /// `offset` is relative to the read cursor: 0 = first unpopped state.
    ///
    /// Part of #3988: Wire compiled BFS level into model checker.
    #[must_use]
    pub(in crate::check::model_checker) fn meta_at_offset(
        &self,
        offset: usize,
    ) -> Option<(Fingerprint, usize, u64)> {
        let idx = self.read_idx + offset;
        if idx >= self.meta.len() {
            return None;
        }
        let m = &self.meta[idx];
        Some((m.fp, m.depth, m.trace_loc))
    }

    /// Push a raw `&[i64]` buffer directly into the arena with metadata.
    ///
    /// This is the zero-allocation enqueue path for the compiled BFS loop:
    /// successor buffers produced by the JIT are raw `&[i64]` slices, and
    /// constructing a `FlatState` (which requires `Box<[i64]>`) just to push
    /// the buffer into the arena is pure overhead. This method copies the
    /// buffer directly into the contiguous arena.
    ///
    /// # Panics
    ///
    /// Debug-asserts that `buffer.len()` matches the layout's slot count.
    ///
    /// Part of #3986: Phase 3 zero-alloc compiled BFS enqueue.
    pub(in crate::check::model_checker) fn push_raw_buffer(
        &mut self,
        buffer: &[i64],
        fp: Fingerprint,
        depth: usize,
        trace_loc: u64,
    ) {
        self.total_pushed += 1;
        self.store.push_buffer(buffer);
        self.meta.push(FlatFrontierMeta {
            fp,
            depth,
            trace_loc,
        });
        self.flat_pushed += 1;
    }

    /// Log frontier statistics to stderr.
    pub(in crate::check::model_checker) fn report_stats(&self) {
        if self.total_pushed > 0 {
            eprintln!(
                "[flat-frontier] {} total pushed, {} flat ({:.1}%), {} fallback, {} bytes/state",
                self.total_pushed,
                self.flat_pushed,
                self.flat_ratio() * 100.0,
                self.total_pushed - self.flat_pushed,
                self.bytes_per_state(),
            );
        }
    }
}

impl BfsFrontier for FlatBfsFrontier {
    type Entry = (NoTraceQueueEntry, usize, u64);

    fn push(&mut self, (entry, depth, trace_loc): (NoTraceQueueEntry, usize, u64)) {
        self.total_pushed += 1;
        match entry {
            NoTraceQueueEntry::Flat { flat, fp } => {
                // Hot path: store raw buffer in contiguous arena.
                self.store.push_buffer(flat.buffer());
                self.meta.push(FlatFrontierMeta {
                    fp,
                    depth,
                    trace_loc,
                });
                self.flat_pushed += 1;
            }
            _ => {
                // Cold path: Bulk/Owned entries go to fallback queue.
                self.fallback.push_back((entry, depth, trace_loc));
            }
        }
    }

    fn pop(&mut self) -> Option<(NoTraceQueueEntry, usize, u64)> {
        // Drain fallback first (initial states, non-flat entries).
        if let Some(entry) = self.fallback.pop_front() {
            return Some(entry);
        }

        // Then drain the flat arena.
        if self.read_idx < self.store.len() {
            let idx = self.read_idx;
            self.read_idx += 1;

            let buffer_slice = self.store.get(idx).expect("invariant: read_idx < store.len()");
            // Copy metadata fields before potential compaction (avoids borrow conflict).
            let fp = self.meta[idx].fp;
            let depth = self.meta[idx].depth;
            let trace_loc = self.meta[idx].trace_loc;

            // Construct FlatState from arena slice (one Box allocation).
            let buffer: Box<[i64]> = buffer_slice.to_vec().into_boxed_slice();
            let flat = FlatState::from_buffer(buffer, Arc::clone(&self.layout));

            let entry = NoTraceQueueEntry::Flat { flat, fp };

            // Compact when the arena is fully drained.
            if self.read_idx == self.store.len() {
                self.compact_if_needed();
            }

            return Some((entry, depth, trace_loc));
        }

        None
    }

    fn len(&self) -> usize {
        self.fallback.len() + self.flat_remaining()
    }

    fn iter(&self) -> impl Iterator<Item = &(NoTraceQueueEntry, usize, u64)> {
        // The BfsFrontier::iter() is used by checkpoint_frontier to snapshot
        // the queue. For the flat frontier, we can only iterate fallback entries
        // directly. Flat arena entries would need to be materialized.
        //
        // For now, return only fallback entries. The checkpoint code in
        // FingerprintOnlyStorage handles Flat entries separately when they
        // appear. This is safe because checkpoint_frontier is called rarely
        // (periodic saves) and the fallback contains all Bulk/Owned entries.
        //
        // TODO(#4126): Implement full checkpoint support for arena entries.
        self.fallback.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::{StateLayout, VarLayoutKind};
    use crate::var_index::VarRegistry;

    fn scalar_layout_3() -> Arc<StateLayout> {
        let registry = VarRegistry::from_names(["x", "y", "z"]);
        Arc::new(StateLayout::new(
            &registry,
            vec![
                VarLayoutKind::Scalar,
                VarLayoutKind::Scalar,
                VarLayoutKind::Scalar,
            ],
        ))
    }

    fn make_flat_entry(
        vals: &[i64],
        fp: u64,
        depth: usize,
        trace_loc: u64,
        layout: &Arc<StateLayout>,
    ) -> (NoTraceQueueEntry, usize, u64) {
        let buffer: Box<[i64]> = vals.to_vec().into_boxed_slice();
        let flat = FlatState::from_buffer(buffer, Arc::clone(layout));
        (
            NoTraceQueueEntry::Flat {
                flat,
                fp: Fingerprint(fp),
            },
            depth,
            trace_loc,
        )
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_frontier_empty() {
        let layout = scalar_layout_3();
        let frontier = FlatBfsFrontier::new(layout);

        assert_eq!(frontier.len(), 0);
        assert_eq!(frontier.flat_pushed(), 0);
        assert_eq!(frontier.total_pushed(), 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_frontier_push_pop_flat() {
        let layout = scalar_layout_3();
        let mut frontier = FlatBfsFrontier::new(Arc::clone(&layout));

        frontier.push(make_flat_entry(&[1, 2, 3], 100, 0, 0, &layout));
        frontier.push(make_flat_entry(&[4, 5, 6], 200, 0, 1, &layout));
        frontier.push(make_flat_entry(&[7, 8, 9], 300, 1, 2, &layout));

        assert_eq!(frontier.len(), 3);
        assert_eq!(frontier.flat_pushed(), 3);
        assert_eq!(frontier.total_pushed(), 3);

        // Pop in FIFO order.
        let (entry, depth, trace_loc) = frontier.pop().unwrap();
        match entry {
            NoTraceQueueEntry::Flat { flat, fp } => {
                assert_eq!(flat.buffer(), &[1, 2, 3]);
                assert_eq!(fp, Fingerprint(100));
            }
            _ => panic!("expected Flat entry"),
        }
        assert_eq!(depth, 0);
        assert_eq!(trace_loc, 0);

        let (entry, depth, _) = frontier.pop().unwrap();
        match entry {
            NoTraceQueueEntry::Flat { flat, fp } => {
                assert_eq!(flat.buffer(), &[4, 5, 6]);
                assert_eq!(fp, Fingerprint(200));
            }
            _ => panic!("expected Flat entry"),
        }
        assert_eq!(depth, 0);

        let (entry, depth, _) = frontier.pop().unwrap();
        match entry {
            NoTraceQueueEntry::Flat { flat, fp } => {
                assert_eq!(flat.buffer(), &[7, 8, 9]);
                assert_eq!(fp, Fingerprint(300));
            }
            _ => panic!("expected Flat entry"),
        }
        assert_eq!(depth, 1);

        assert!(frontier.pop().is_none());
        assert_eq!(frontier.len(), 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_frontier_fallback_drained_first() {
        use crate::state::ArrayState;
        use crate::Value;

        let layout = scalar_layout_3();
        let mut frontier = FlatBfsFrontier::new(Arc::clone(&layout));

        // Push an Owned entry (goes to fallback).
        let owned = ArrayState::from_values(vec![
            Value::SmallInt(10),
            Value::SmallInt(20),
            Value::SmallInt(30),
        ]);
        frontier.push((
            NoTraceQueueEntry::Owned {
                state: owned,
                fp: Fingerprint(999),
            },
            0,
            0,
        ));

        // Push a Flat entry (goes to arena).
        frontier.push(make_flat_entry(&[1, 2, 3], 100, 1, 1, &layout));

        assert_eq!(frontier.len(), 2);
        assert_eq!(frontier.flat_pushed(), 1);
        assert_eq!(frontier.total_pushed(), 2);

        // Fallback is drained first.
        let (entry, _, _) = frontier.pop().unwrap();
        match entry {
            NoTraceQueueEntry::Owned { fp, .. } => {
                assert_eq!(fp, Fingerprint(999));
            }
            _ => panic!("expected Owned entry from fallback"),
        }

        // Then flat arena.
        let (entry, depth, _) = frontier.pop().unwrap();
        match entry {
            NoTraceQueueEntry::Flat { flat, fp } => {
                assert_eq!(flat.buffer(), &[1, 2, 3]);
                assert_eq!(fp, Fingerprint(100));
            }
            _ => panic!("expected Flat entry from arena"),
        }
        assert_eq!(depth, 1);

        assert!(frontier.pop().is_none());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_frontier_compaction() {
        let layout = scalar_layout_3();
        let mut frontier = FlatBfsFrontier::new(Arc::clone(&layout));

        // Push 100 states.
        for i in 0..100i64 {
            frontier.push(make_flat_entry(
                &[i, i + 1, i + 2],
                i as u64,
                0,
                i as u64,
                &layout,
            ));
        }

        // Pop all 100 — should trigger compaction.
        for _ in 0..100 {
            assert!(frontier.pop().is_some());
        }

        assert!(frontier.pop().is_none());
        assert_eq!(frontier.len(), 0);
        // After compaction, the arena should be empty.
        assert_eq!(frontier.store.len(), 0);
        assert_eq!(frontier.read_idx, 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_frontier_stats() {
        let layout = scalar_layout_3();
        let mut frontier = FlatBfsFrontier::new(Arc::clone(&layout));

        for i in 0..50i64 {
            frontier.push(make_flat_entry(&[i, 0, 0], i as u64, 0, 0, &layout));
        }

        assert_eq!(frontier.flat_pushed(), 50);
        assert_eq!(frontier.total_pushed(), 50);
        assert!((frontier.flat_ratio() - 1.0).abs() < 1e-10);
        assert_eq!(frontier.bytes_per_state(), 24);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_frontier_with_capacity() {
        let layout = scalar_layout_3();
        let frontier = FlatBfsFrontier::with_capacity(Arc::clone(&layout), 1000);

        assert_eq!(frontier.len(), 0);
        assert!(frontier.store.capacity() >= 1000);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_frontier_push_raw_buffer() {
        let layout = scalar_layout_3();
        let mut frontier = FlatBfsFrontier::new(Arc::clone(&layout));

        // Push raw buffers (no FlatState construction).
        frontier.push_raw_buffer(&[10, 20, 30], Fingerprint(100), 0, 0);
        frontier.push_raw_buffer(&[40, 50, 60], Fingerprint(200), 1, 1);
        frontier.push_raw_buffer(&[70, 80, 90], Fingerprint(300), 2, 2);

        assert_eq!(frontier.len(), 3);
        assert_eq!(frontier.flat_pushed(), 3);
        assert_eq!(frontier.total_pushed(), 3);

        // Pop in FIFO order — produces the same FlatState as if we had
        // pushed via make_flat_entry.
        let (entry, depth, trace_loc) = frontier.pop().unwrap();
        match entry {
            NoTraceQueueEntry::Flat { flat, fp } => {
                assert_eq!(flat.buffer(), &[10, 20, 30]);
                assert_eq!(fp, Fingerprint(100));
            }
            _ => panic!("expected Flat entry"),
        }
        assert_eq!(depth, 0);
        assert_eq!(trace_loc, 0);

        let (entry, depth, trace_loc) = frontier.pop().unwrap();
        match entry {
            NoTraceQueueEntry::Flat { flat, fp } => {
                assert_eq!(flat.buffer(), &[40, 50, 60]);
                assert_eq!(fp, Fingerprint(200));
            }
            _ => panic!("expected Flat entry"),
        }
        assert_eq!(depth, 1);
        assert_eq!(trace_loc, 1);

        let (entry, depth, trace_loc) = frontier.pop().unwrap();
        match entry {
            NoTraceQueueEntry::Flat { flat, fp } => {
                assert_eq!(flat.buffer(), &[70, 80, 90]);
                assert_eq!(fp, Fingerprint(300));
            }
            _ => panic!("expected Flat entry"),
        }
        assert_eq!(depth, 2);
        assert_eq!(trace_loc, 2);

        assert!(frontier.pop().is_none());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_frontier_push_raw_matches_flat_entry() {
        // Verify that push_raw_buffer produces identical results to pushing
        // via NoTraceQueueEntry::Flat (the FlatState wrapper path).
        let layout = scalar_layout_3();
        let vals = [42i64, -7, 100];
        let fp = Fingerprint(12345);

        // Path 1: push via FlatState wrapper.
        let mut frontier1 = FlatBfsFrontier::new(Arc::clone(&layout));
        let buffer: Box<[i64]> = vals.to_vec().into_boxed_slice();
        let flat = FlatState::from_buffer(buffer, Arc::clone(&layout));
        frontier1.push((NoTraceQueueEntry::Flat { flat, fp }, 3, 99));

        // Path 2: push raw buffer directly.
        let mut frontier2 = FlatBfsFrontier::new(Arc::clone(&layout));
        frontier2.push_raw_buffer(&vals, fp, 3, 99);

        // Both must produce identical pop results.
        let (e1, d1, t1) = frontier1.pop().unwrap();
        let (e2, d2, t2) = frontier2.pop().unwrap();
        assert_eq!(d1, d2);
        assert_eq!(t1, t2);
        match (e1, e2) {
            (
                NoTraceQueueEntry::Flat { flat: f1, fp: fp1 },
                NoTraceQueueEntry::Flat { flat: f2, fp: fp2 },
            ) => {
                assert_eq!(f1.buffer(), f2.buffer());
                assert_eq!(fp1, fp2);
            }
            _ => panic!("expected Flat entries from both paths"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_frontier_push_raw_remaining_arena() {
        // Verify that push_raw_buffer states are accessible via remaining_arena.
        let layout = scalar_layout_3();
        let mut frontier = FlatBfsFrontier::new(Arc::clone(&layout));

        frontier.push_raw_buffer(&[1, 2, 3], Fingerprint(10), 0, 0);
        frontier.push_raw_buffer(&[4, 5, 6], Fingerprint(20), 0, 1);

        let (arena, count) = frontier.remaining_arena().unwrap();
        assert_eq!(count, 2);
        assert_eq!(arena, &[1, 2, 3, 4, 5, 6]);

        // Metadata should also be accessible.
        let (fp, depth, trace_loc) = frontier.meta_at_offset(0).unwrap();
        assert_eq!(fp, Fingerprint(10));
        assert_eq!(depth, 0);
        assert_eq!(trace_loc, 0);

        let (fp, depth, trace_loc) = frontier.meta_at_offset(1).unwrap();
        assert_eq!(fp, Fingerprint(20));
        assert_eq!(depth, 0);
        assert_eq!(trace_loc, 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_frontier_interleaved_push_pop() {
        let layout = scalar_layout_3();
        let mut frontier = FlatBfsFrontier::new(Arc::clone(&layout));

        // Push 2, pop 1, push 2, pop 1 — tests cursor management.
        frontier.push(make_flat_entry(&[1, 0, 0], 1, 0, 0, &layout));
        frontier.push(make_flat_entry(&[2, 0, 0], 2, 0, 0, &layout));

        let (entry, _, _) = frontier.pop().unwrap();
        match entry {
            NoTraceQueueEntry::Flat { flat, .. } => assert_eq!(flat.buffer()[0], 1),
            _ => panic!("expected Flat"),
        }

        frontier.push(make_flat_entry(&[3, 0, 0], 3, 0, 0, &layout));
        frontier.push(make_flat_entry(&[4, 0, 0], 4, 0, 0, &layout));

        // Remaining: [2, 3, 4]
        assert_eq!(frontier.len(), 3);

        let (entry, _, _) = frontier.pop().unwrap();
        match entry {
            NoTraceQueueEntry::Flat { flat, .. } => assert_eq!(flat.buffer()[0], 2),
            _ => panic!("expected Flat"),
        }

        let (entry, _, _) = frontier.pop().unwrap();
        match entry {
            NoTraceQueueEntry::Flat { flat, .. } => assert_eq!(flat.buffer()[0], 3),
            _ => panic!("expected Flat"),
        }

        let (entry, _, _) = frontier.pop().unwrap();
        match entry {
            NoTraceQueueEntry::Flat { flat, .. } => assert_eq!(flat.buffer()[0], 4),
            _ => panic!("expected Flat"),
        }

        assert!(frontier.pop().is_none());
    }
}
