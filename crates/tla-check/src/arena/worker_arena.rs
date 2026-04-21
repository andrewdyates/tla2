// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-worker bump arena for successor state allocation.
//!
//! Replaces per-successor `Box<[CompactValue]>` heap allocations with O(1) bump
//! allocation from a per-worker arena. Since ~95% of successor states are
//! duplicates (already in the seen-set), their `Box` allocations are immediately
//! freed. Arena allocation avoids both the malloc and free overhead for these
//! transient states.
//!
//! # Lifecycle
//!
//! 1. Worker thread calls `init_worker_arena()` at startup.
//! 2. During successor generation: `alloc_compact_values()` bumps the arena cursor.
//! 3. States passing dedup are "promoted" to heap storage via `promote_to_heap()`.
//! 4. After a BFS level completes: `worker_arena_reset()` reclaims all memory in O(1).
//!
//! # Thread Safety
//!
//! Each worker thread owns its own `WorkerArena`. No cross-thread sharing.
//! Access is through `with_worker_arena()` which uses a thread-local RefCell.
//!
//! # CPU Savings Target
//!
//! Profile shows mi_malloc+mi_free = 5.5% CPU, Value::drop = 4.5% CPU (combined 10%).
//! Arena allocation eliminates per-object malloc/free for the ~95% of successor
//! states that are discarded after dedup.
//!
//! # Part of #3990

use std::cell::{Cell, RefCell};

use tla_value::CompactValue;

use crate::state::{ArrayState, Fingerprint};

/// Default arena capacity: 4MB.
///
/// Each CompactValue is 8 bytes. A state with 10 variables uses 80 bytes.
/// 4MB supports ~50,000 transient successor states per BFS level before
/// needing a new chunk. BFS levels typically process thousands of states,
/// each generating a few successors.
const DEFAULT_CAPACITY: usize = 4 * 1024 * 1024;

// ============================================================================
// WorkerArena — bumpalo-based implementation
// ============================================================================

#[cfg(feature = "bumpalo")]
pub(crate) struct WorkerArena {
    bump: bumpalo::Bump,
    allocated_bytes: Cell<usize>,
    allocation_count: Cell<usize>,
    reset_count: Cell<usize>,
}

#[cfg(feature = "bumpalo")]
impl WorkerArena {
    /// Create a new worker arena with default capacity (4MB).
    pub(crate) fn new() -> Self {
        Self::with_capacity(DEFAULT_CAPACITY)
    }

    /// Create a worker arena with the given byte capacity.
    pub(crate) fn with_capacity(bytes: usize) -> Self {
        WorkerArena {
            bump: bumpalo::Bump::with_capacity(bytes),
            allocated_bytes: Cell::new(0),
            allocation_count: Cell::new(0),
            reset_count: Cell::new(0),
        }
    }

    /// Allocate a CompactValue slice from the arena, cloning from source.
    ///
    /// Returns a reference to arena-allocated memory. The slice is valid until
    /// the next `reset()` call.
    ///
    /// Note: CompactValue is not Copy (compound types hold Box<Value>), so we
    /// use `alloc_slice_fill_iter` with `.cloned()`.
    /// Scaffolding for arena promotion path (#3990).
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn alloc_compact_values(&self, src: &[CompactValue]) -> &[CompactValue] {
        if src.is_empty() {
            return &[];
        }
        let size = std::mem::size_of_val(src);
        self.allocated_bytes.set(self.allocated_bytes.get() + size);
        self.allocation_count.set(self.allocation_count.get() + 1);
        self.bump.alloc_slice_fill_iter(src.iter().cloned())
    }

    /// Allocate a mutable CompactValue slice from the arena, cloning from source.
    ///
    /// Returns a mutable reference for in-place patching by the caller.
    /// Scaffolding for arena promotion path (#3990).
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn alloc_compact_values_mut(&self, src: &[CompactValue]) -> &mut [CompactValue] {
        if src.is_empty() {
            return &mut [];
        }
        let size = std::mem::size_of_val(src);
        self.allocated_bytes.set(self.allocated_bytes.get() + size);
        self.allocation_count.set(self.allocation_count.get() + 1);
        self.bump.alloc_slice_fill_iter(src.iter().cloned())
    }

    /// Allocate a CompactValue slice from the arena, cloning base values and
    /// applying patches in one pass.
    ///
    /// This is the fast path for diff-based successor generation: instead of
    /// cloning the entire `Box<[CompactValue]>` and then patching, we allocate
    /// once in the arena and write the patched values directly.
    /// Scaffolding for arena promotion path (#3990).
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn alloc_compact_values_with_patches(
        &self,
        base: &[CompactValue],
        patches: &[(usize, CompactValue)],
    ) -> &[CompactValue] {
        if base.is_empty() {
            return &[];
        }
        let size = std::mem::size_of_val(base);
        self.allocated_bytes.set(self.allocated_bytes.get() + size);
        self.allocation_count.set(self.allocation_count.get() + 1);

        // Allocate a mutable slice and clone base values
        let dest = self.bump.alloc_slice_fill_iter(base.iter().cloned());

        // Apply patches (cloning the CompactValue)
        for &(idx, ref value) in patches {
            dest[idx] = value.clone();
        }

        dest
    }

    /// Promote an arena-allocated slice to heap storage.
    ///
    /// Creates a `Box<[CompactValue]>` that independently owns its memory.
    /// Used when a successor state passes dedup and needs to persist in the
    /// seen-set beyond the current BFS level.
    /// Scaffolding for arena promotion path (#3990).
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn promote_to_heap(slice: &[CompactValue]) -> Box<[CompactValue]> {
        slice.to_vec().into_boxed_slice()
    }

    /// Reset the arena, reclaiming all memory in O(1).
    ///
    /// All previously-allocated slices become invalid. Callers must not hold
    /// references across reset boundaries.
    pub(crate) fn reset(&mut self) {
        self.bump.reset();
        self.reset_count.set(self.reset_count.get() + 1);
    }

    /// Total bytes allocated from this arena (cumulative across resets).
    pub(crate) fn allocated_bytes(&self) -> usize {
        self.allocated_bytes.get()
    }

    /// Total individual allocations from this arena (cumulative).
    pub(crate) fn allocation_count(&self) -> usize {
        self.allocation_count.get()
    }

    /// Number of reset calls performed.
    pub(crate) fn reset_count(&self) -> usize {
        self.reset_count.get()
    }

    /// Current chunk capacity of the underlying bump allocator.
    pub(crate) fn chunk_capacity(&self) -> usize {
        self.bump.chunk_capacity()
    }
}

// ============================================================================
// WorkerArena — Vec-based fallback (no bumpalo)
// ============================================================================

#[cfg(not(feature = "bumpalo"))]
pub(crate) struct WorkerArena {
    allocated_bytes: Cell<usize>,
    allocation_count: Cell<usize>,
    reset_count: Cell<usize>,
}

#[cfg(not(feature = "bumpalo"))]
impl WorkerArena {
    pub(crate) fn new() -> Self {
        Self::with_capacity(0)
    }

    pub(crate) fn with_capacity(_bytes: usize) -> Self {
        WorkerArena {
            allocated_bytes: Cell::new(0),
            allocation_count: Cell::new(0),
            reset_count: Cell::new(0),
        }
    }

    #[inline]
    #[allow(dead_code)]
    pub(crate) fn alloc_compact_values(&self, src: &[CompactValue]) -> &[CompactValue] {
        if src.is_empty() {
            return &[];
        }
        let size = std::mem::size_of_val(src);
        self.allocated_bytes.set(self.allocated_bytes.get() + size);
        self.allocation_count.set(self.allocation_count.get() + 1);
        // Fallback: leak a Box to get a 'static reference
        Box::leak(src.to_vec().into_boxed_slice())
    }

    #[inline]
    #[allow(dead_code)]
    pub(crate) fn alloc_compact_values_mut(&self, src: &[CompactValue]) -> &mut [CompactValue] {
        if src.is_empty() {
            return &mut [];
        }
        let size = std::mem::size_of_val(src);
        self.allocated_bytes.set(self.allocated_bytes.get() + size);
        self.allocation_count.set(self.allocation_count.get() + 1);
        Box::leak(src.to_vec().into_boxed_slice())
    }

    #[inline]
    #[allow(dead_code)]
    pub(crate) fn alloc_compact_values_with_patches(
        &self,
        base: &[CompactValue],
        patches: &[(usize, CompactValue)],
    ) -> &[CompactValue] {
        if base.is_empty() {
            return &[];
        }
        let size = std::mem::size_of_val(base);
        self.allocated_bytes.set(self.allocated_bytes.get() + size);
        self.allocation_count.set(self.allocation_count.get() + 1);
        let mut vec = base.to_vec();
        for &(idx, ref value) in patches {
            vec[idx] = *value;
        }
        Box::leak(vec.into_boxed_slice())
    }

    #[inline]
    #[allow(dead_code)]
    pub(crate) fn promote_to_heap(slice: &[CompactValue]) -> Box<[CompactValue]> {
        slice.to_vec().into_boxed_slice()
    }

    pub(crate) fn reset(&mut self) {
        // Fallback: leaked memory cannot be reclaimed
        self.reset_count.set(self.reset_count.get() + 1);
    }

    pub(crate) fn allocated_bytes(&self) -> usize {
        self.allocated_bytes.get()
    }

    pub(crate) fn allocation_count(&self) -> usize {
        self.allocation_count.get()
    }

    pub(crate) fn reset_count(&self) -> usize {
        self.reset_count.get()
    }

    pub(crate) fn chunk_capacity(&self) -> usize {
        0
    }
}

// ============================================================================
// ArenaArrayState — temporary arena-backed state for successor evaluation
// ============================================================================

/// A temporary array state backed by arena memory.
///
/// Unlike `ArrayState` which owns a `Box<[CompactValue]>`, `ArenaArrayState`
/// borrows a `&[CompactValue]` slice from the worker arena. This avoids
/// per-successor heap allocation for the ~95% of states discarded after dedup.
///
/// States that pass dedup are promoted to heap-owned `ArrayState` via `promote()`.
/// Scaffolding for arena promotion path (#3990).
#[allow(dead_code)]
pub(crate) struct ArenaArrayState<'a> {
    /// CompactValue slice borrowed from the worker arena.
    values: &'a [CompactValue],
    /// Pre-computed fingerprint (from diff or full computation).
    fingerprint: Option<Fingerprint>,
    /// Pre-computed combined_xor for incremental fingerprint updates.
    combined_xor: Option<u64>,
}

#[allow(dead_code)]
impl<'a> ArenaArrayState<'a> {
    /// Create a new arena-backed state from an arena-allocated slice.
    #[inline]
    pub(crate) fn new(values: &'a [CompactValue]) -> Self {
        ArenaArrayState {
            values,
            fingerprint: None,
            combined_xor: None,
        }
    }

    /// Create a new arena-backed state with pre-computed fingerprint.
    #[inline]
    pub(crate) fn with_fingerprint(
        values: &'a [CompactValue],
        fp: Fingerprint,
        combined_xor: u64,
    ) -> Self {
        ArenaArrayState {
            values,
            fingerprint: Some(fp),
            combined_xor: Some(combined_xor),
        }
    }

    /// Access the CompactValue slice.
    #[inline]
    pub(crate) fn values(&self) -> &[CompactValue] {
        self.values
    }

    /// Get the pre-computed fingerprint, if available.
    #[inline]
    pub(crate) fn fingerprint(&self) -> Option<Fingerprint> {
        self.fingerprint
    }

    /// Get the pre-computed combined_xor, if available.
    #[inline]
    pub(crate) fn combined_xor(&self) -> Option<u64> {
        self.combined_xor
    }

    /// Number of variables in this state.
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.values.len()
    }

    /// Promote this arena-backed state to a heap-owned `ArrayState`.
    ///
    /// Used when the state passes dedup and needs to persist in the seen-set.
    /// Creates a new `Box<[CompactValue]>` and copies the arena data.
    pub(crate) fn promote(self) -> ArrayState {
        use crate::state::ArrayStateFpCache;

        let heap_values: Box<[CompactValue]> = self.values.to_vec().into_boxed_slice();
        let fp_cache = match (self.fingerprint, self.combined_xor) {
            (Some(fp), Some(xor)) => Some(ArrayStateFpCache {
                combined_xor: xor,
                fingerprint: fp,
                value_fps: None,
            }),
            _ => None,
        };

        ArrayState {
            values: heap_values,
            fp_cache,
        }
    }
}

// ============================================================================
// Thread-local arena access
// ============================================================================

thread_local! {
    static WORKER_ARENA: RefCell<Option<WorkerArena>> = const { RefCell::new(None) };
}

/// Initialize the thread-local worker arena for this worker thread.
///
/// Called once per worker thread at startup. The arena persists for the
/// lifetime of the thread, reusing chunks across BFS levels.
pub(crate) fn init_worker_arena() {
    WORKER_ARENA.with(|cell| {
        let mut borrow = cell.borrow_mut();
        if borrow.is_none() {
            *borrow = Some(WorkerArena::new());
        }
    });
}

/// Access the thread-local worker arena.
///
/// Returns `None` if the arena has not been initialized (e.g., in test contexts
/// or non-worker threads).
pub(crate) fn with_worker_arena<R>(f: impl FnOnce(&mut WorkerArena) -> R) -> Option<R> {
    WORKER_ARENA.with(|cell| {
        let mut borrow = cell.borrow_mut();
        borrow.as_mut().map(f)
    })
}

/// Reset the thread-local worker arena, reclaiming all transient state memory.
///
/// Called at BFS level boundaries (after all successors from a level have been
/// processed and new states have been promoted to the seen-set).
pub(crate) fn worker_arena_reset() {
    with_worker_arena(|arena| arena.reset());
}

/// Report worker arena stats to stderr if `TLA2_WORKER_ARENA_STATS=1`.
///
/// Called at the end of BFS exploration.
pub(crate) fn report_worker_arena_stats() {
    if !{
        static WORKER_ARENA_STATS: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        *WORKER_ARENA_STATS.get_or_init(|| {
            std::env::var("TLA2_WORKER_ARENA_STATS").as_deref() == Ok("1")
        })
    } {
        return;
    }
    with_worker_arena(|arena| {
        eprintln!("=== Worker Arena Stats ===");
        eprintln!("  Allocations:  {}", arena.allocation_count());
        eprintln!(
            "  Bytes total:  {} ({:.1} MB)",
            arena.allocated_bytes(),
            arena.allocated_bytes() as f64 / (1024.0 * 1024.0)
        );
        eprintln!("  Chunk capacity: {} KB", arena.chunk_capacity() / 1024);
        eprintln!("  Resets: {}", arena.reset_count());
        if arena.allocation_count() > 0 {
            eprintln!(
                "  Avg bytes/alloc: {:.0}",
                arena.allocated_bytes() as f64 / arena.allocation_count() as f64
            );
        }
        if arena.reset_count() > 0 {
            eprintln!(
                "  Avg allocs/level: {:.0}",
                arena.allocation_count() as f64 / arena.reset_count() as f64
            );
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cv(v: i64) -> CompactValue {
        CompactValue::from(v)
    }

    fn cv_bool(v: bool) -> CompactValue {
        CompactValue::from(v)
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_worker_arena_basic_alloc() {
        let arena = WorkerArena::new();
        let src = [cv_bool(true), cv_bool(false), cv(42)];
        let slice = arena.alloc_compact_values(&src);
        assert_eq!(slice.len(), 3);
        assert_eq!(slice[0], cv_bool(true));
        assert_eq!(slice[1], cv_bool(false));
        assert_eq!(slice[2], cv(42));
        assert_eq!(arena.allocation_count(), 1);
        assert!(arena.allocated_bytes() > 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_worker_arena_empty_alloc() {
        let arena = WorkerArena::new();
        let slice = arena.alloc_compact_values(&[]);
        assert!(slice.is_empty());
        assert_eq!(arena.allocation_count(), 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_worker_arena_alloc_with_patches() {
        let arena = WorkerArena::new();
        let base = [cv(1), cv(2), cv(3)];
        let patches = [(1, cv(42))];
        let slice = arena.alloc_compact_values_with_patches(&base, &patches);
        assert_eq!(slice.len(), 3);
        assert_eq!(slice[0], cv(1));
        assert_eq!(slice[1], cv(42)); // patched
        assert_eq!(slice[2], cv(3));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_worker_arena_promote_to_heap() {
        let arena = WorkerArena::new();
        let src = [cv(99), cv_bool(true)];
        let slice = arena.alloc_compact_values(&src);
        let boxed = WorkerArena::promote_to_heap(slice);
        assert_eq!(boxed.len(), 2);
        assert_eq!(boxed[0], cv(99));
        assert_eq!(boxed[1], cv_bool(true));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_worker_arena_reset() {
        let mut arena = WorkerArena::new();
        let _s1 = arena.alloc_compact_values(&[cv(1)]);
        let _s2 = arena.alloc_compact_values(&[cv(2)]);
        assert_eq!(arena.allocation_count(), 2);
        arena.reset();
        assert_eq!(arena.reset_count(), 1);
        // After reset, arena is ready for new allocations
        let _s3 = arena.alloc_compact_values(&[cv(3)]);
        assert_eq!(arena.allocation_count(), 3); // cumulative
    }

    #[cfg(feature = "bumpalo")]
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_worker_arena_capacity() {
        let arena = WorkerArena::with_capacity(1024 * 1024);
        // Should have pre-allocated capacity
        assert!(arena.chunk_capacity() >= 1024 * 1024);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_arena_array_state_basic() {
        let arena = WorkerArena::new();
        let src = [cv(10), cv(20), cv_bool(true)];
        let slice = arena.alloc_compact_values(&src);
        let state = ArenaArrayState::new(slice);
        assert_eq!(state.len(), 3);
        assert_eq!(state.values()[0], cv(10));
        assert!(state.fingerprint().is_none());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_arena_array_state_with_fingerprint() {
        let arena = WorkerArena::new();
        let src = [cv(1), cv(2)];
        let slice = arena.alloc_compact_values(&src);
        let fp = Fingerprint(0xDEADBEEF);
        let state = ArenaArrayState::with_fingerprint(slice, fp, 0x12345678);
        assert_eq!(state.fingerprint(), Some(fp));
        assert_eq!(state.combined_xor(), Some(0x12345678));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_arena_array_state_promote() {
        let arena = WorkerArena::new();
        let src = [cv(42), cv_bool(false)];
        let slice = arena.alloc_compact_values(&src);
        let fp = Fingerprint(0xCAFEBABE);
        let arena_state = ArenaArrayState::with_fingerprint(slice, fp, 0xABCD);
        let promoted = arena_state.promote();
        assert_eq!(promoted.len(), 2);
        assert_eq!(promoted.values()[0], cv(42));
        assert_eq!(promoted.values()[1], cv_bool(false));
        // Verify fingerprint was preserved
        assert_eq!(promoted.cached_fingerprint(), Some(fp));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_worker_arena_thread_local() {
        // Initialize the thread-local arena
        init_worker_arena();

        // Allocate via thread-local
        let result = with_worker_arena(|arena| {
            let src = [cv(7)];
            let slice = arena.alloc_compact_values(&src);
            slice[0].clone()
        });
        assert_eq!(result, Some(cv(7)));

        // Reset via thread-local
        worker_arena_reset();
        let reset_count = with_worker_arena(|arena| arena.reset_count());
        assert_eq!(reset_count, Some(1));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_worker_arena_many_allocs() {
        let arena = WorkerArena::new();
        let base: Vec<CompactValue> = (0..10).map(|_| cv(0)).collect();

        // Simulate 10K successor allocations
        for i in 0..10_000 {
            let slice = arena.alloc_compact_values(&base);
            assert_eq!(slice.len(), 10);
            // Verify first allocation still works (arena doesn't corrupt)
            if i == 0 {
                assert_eq!(slice[0], cv(0));
            }
        }

        assert_eq!(arena.allocation_count(), 10_000);
        // 10 CompactValues * 8 bytes * 10K = 800KB
        assert_eq!(arena.allocated_bytes(), 10 * 8 * 10_000);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_worker_arena_alloc_mut() {
        let arena = WorkerArena::new();
        let src = [cv(1), cv(2)];
        let slice = arena.alloc_compact_values_mut(&src);
        // Mutate in place
        slice[0] = cv(99);
        assert_eq!(slice[0], cv(99));
        assert_eq!(slice[1], cv(2));
    }

    // ========================================================================
    // Integration tests: full BFS lifecycle simulation
    // Part of #3990: JIT V2 Phase 7 — per-worker bump arenas, zero malloc
    // ========================================================================

    /// Simulate a BFS level: allocate 100 successor states, promote 5% to
    /// heap (simulating dedup pass), reset arena, verify promoted states
    /// survive reset and arena is reusable.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_worker_arena_bfs_level_lifecycle() {
        let mut arena = WorkerArena::new();
        let state_len = 10;

        // Generate 100 successor states in the arena.
        let mut arena_slices: Vec<&[CompactValue]> = Vec::new();
        for i in 0..100 {
            let src: Vec<CompactValue> = (0..state_len).map(|v| cv(i * 10 + v)).collect();
            let slice = arena.alloc_compact_values(&src);
            arena_slices.push(slice);
        }
        assert_eq!(arena.allocation_count(), 100);
        assert_eq!(
            arena.allocated_bytes(),
            100 * state_len as usize * std::mem::size_of::<CompactValue>()
        );

        // Simulate dedup: 95% are duplicates (discarded), 5% are new.
        // Promote the 5 new states to heap storage.
        let promoted_indices = [3, 17, 42, 78, 95];
        let mut promoted: Vec<Box<[CompactValue]>> = Vec::new();
        for &idx in &promoted_indices {
            let boxed = WorkerArena::promote_to_heap(arena_slices[idx]);
            promoted.push(boxed);
        }

        // Verify promoted states have correct values.
        for (pi, &idx) in promoted_indices.iter().enumerate() {
            let boxed = &promoted[pi];
            assert_eq!(boxed.len(), state_len as usize);
            for v in 0..state_len {
                assert_eq!(boxed[v as usize], cv(idx as i64 * 10 + v));
            }
        }

        // Reset the arena (simulating BFS level boundary).
        arena.reset();
        assert_eq!(arena.reset_count(), 1);

        // Promoted states must survive arena reset.
        for (pi, &idx) in promoted_indices.iter().enumerate() {
            assert_eq!(promoted[pi][0], cv(idx as i64 * 10));
        }

        // Arena is reusable for next BFS level.
        let src2 = [cv(999), cv(1000)];
        let slice2 = arena.alloc_compact_values(&src2);
        assert_eq!(slice2[0], cv(999));
        assert_eq!(arena.allocation_count(), 101); // cumulative
    }

    /// Test the ArenaArrayState → ArrayState promote cycle with fingerprint
    /// preservation, verifying that promoted states are independent of arena
    /// lifetime.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_arena_array_state_dedup_promote_cycle() {
        let mut arena = WorkerArena::new();

        // Allocate state values in arena.
        let src = [cv(100), cv(200), cv_bool(true), cv(400)];
        let slice = arena.alloc_compact_values(&src);

        // Create ArenaArrayState with fingerprint.
        let fp = Fingerprint(0xDEAD_BEEF_CAFE_BABE);
        let xor = 0x1234_5678_ABCD_EF01;
        let arena_state = ArenaArrayState::with_fingerprint(slice, fp, xor);

        // Verify arena state metadata.
        assert_eq!(arena_state.len(), 4);
        assert_eq!(arena_state.fingerprint(), Some(fp));
        assert_eq!(arena_state.combined_xor(), Some(xor));
        assert_eq!(arena_state.values()[0], cv(100));
        assert_eq!(arena_state.values()[3], cv(400));

        // Promote to heap-owned ArrayState.
        let promoted = arena_state.promote();
        assert_eq!(promoted.len(), 4);
        assert_eq!(promoted.values()[0], cv(100));
        assert_eq!(promoted.values()[1], cv(200));
        assert_eq!(promoted.cached_fingerprint(), Some(fp));

        // Reset arena — promoted ArrayState must survive.
        arena.reset();
        assert_eq!(promoted.values()[0], cv(100));
        assert_eq!(promoted.values()[3], cv(400));
        assert_eq!(promoted.cached_fingerprint(), Some(fp));
    }

    /// Stress test: simulate 10 BFS levels with 1000 allocations per level.
    /// Verify cumulative stats and arena reuse across multiple resets.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_worker_arena_high_volume_with_periodic_reset() {
        let mut arena = WorkerArena::new();
        let state_len: usize = 8;
        let levels = 10;
        let allocs_per_level = 1000;

        for level in 0..levels {
            for i in 0..allocs_per_level {
                let src: Vec<CompactValue> = (0..state_len)
                    .map(|v| cv((level * allocs_per_level + i) as i64 * 10 + v as i64))
                    .collect();
                let slice = arena.alloc_compact_values(&src);
                assert_eq!(slice.len(), state_len);
            }
            arena.reset();
        }

        // Stats are cumulative across resets.
        assert_eq!(arena.allocation_count(), levels * allocs_per_level);
        assert_eq!(arena.reset_count(), levels);
        assert_eq!(
            arena.allocated_bytes(),
            levels * allocs_per_level * state_len * std::mem::size_of::<CompactValue>()
        );
    }

    /// Full thread-local lifecycle: init → alloc → reset → stats.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_worker_arena_thread_local_full_lifecycle() {
        // Initialize the thread-local arena.
        init_worker_arena();

        // Phase 1: Allocate multiple states via thread-local.
        for i in 0..50 {
            let result = with_worker_arena(|arena| {
                let src: Vec<CompactValue> = (0..5).map(|v| cv(i * 5 + v)).collect();
                let slice = arena.alloc_compact_values(&src);
                assert_eq!(slice.len(), 5);
                slice[0].clone()
            });
            assert_eq!(result, Some(cv(i * 5)));
        }

        // Verify allocation count.
        let alloc_count = with_worker_arena(|arena| arena.allocation_count());
        assert!(alloc_count.unwrap() >= 50);

        // Phase 2: Reset at level boundary.
        worker_arena_reset();
        let reset_count = with_worker_arena(|arena| arena.reset_count());
        assert!(reset_count.unwrap() >= 1);

        // Phase 3: Allocate again after reset.
        let result = with_worker_arena(|arena| {
            let src = [cv(777)];
            let slice = arena.alloc_compact_values(&src);
            slice[0].clone()
        });
        assert_eq!(result, Some(cv(777)));
    }

    /// Test alloc_compact_values_with_patches in a BFS successor scenario:
    /// base state + diff patches produces correct patched state.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_worker_arena_diff_patch_successor() {
        let arena = WorkerArena::new();

        // Base state: [10, 20, 30, 40, 50]
        let base = [cv(10), cv(20), cv(30), cv(40), cv(50)];

        // Diff patches: change index 1 to 99, index 3 to 88.
        let patches = [(1, cv(99)), (3, cv(88))];
        let patched = arena.alloc_compact_values_with_patches(&base, &patches);

        assert_eq!(patched.len(), 5);
        assert_eq!(patched[0], cv(10)); // unchanged
        assert_eq!(patched[1], cv(99)); // patched
        assert_eq!(patched[2], cv(30)); // unchanged
        assert_eq!(patched[3], cv(88)); // patched
        assert_eq!(patched[4], cv(50)); // unchanged
        assert_eq!(arena.allocation_count(), 1);
    }
}
