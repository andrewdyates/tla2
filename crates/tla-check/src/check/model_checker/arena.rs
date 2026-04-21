// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Mmap-backed state storage primitives for BFS workers.

use std::fmt;
use std::io;
use std::mem::size_of;
use std::ptr::{self, NonNull};
use std::slice;
use std::sync::atomic::{AtomicUsize, Ordering};

const I64_BYTES: usize = size_of::<i64>();
const CACHE_LINE_BYTES: usize = 64;
const CACHE_PADDING_BYTES: usize = CACHE_LINE_BYTES - size_of::<AtomicUsize>();

fn checked_mul(lhs: usize, rhs: usize, context: &str) -> usize {
    lhs.checked_mul(rhs)
        .unwrap_or_else(|| panic!("{context} overflow: {lhs} * {rhs}"))
}

fn checked_add(lhs: usize, rhs: usize, context: &str) -> usize {
    lhs.checked_add(rhs)
        .unwrap_or_else(|| panic!("{context} overflow: {lhs} + {rhs}"))
}

fn map_anon(byte_len: usize, owner: &str) -> NonNull<u8> {
    assert!(byte_len != 0, "{owner} requires a non-zero mmap size");

    // SAFETY: Requests a private anonymous read/write mapping. `byte_len > 0`,
    // the file descriptor is ignored for `MAP_ANON`, and the kernel returns a
    // page-aligned base pointer on success.
    let ptr = unsafe {
        libc::mmap(
            ptr::null_mut(),
            byte_len,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_ANON | libc::MAP_PRIVATE,
            -1,
            0,
        )
    };

    if ptr == libc::MAP_FAILED {
        panic!(
            "{owner} mmap failed for {byte_len} bytes: {}",
            io::Error::last_os_error()
        );
    }

    // SAFETY: `ptr != MAP_FAILED`, so `mmap` returned a valid, non-null base
    // address for a live mapping owned by this process.
    unsafe { NonNull::new_unchecked(ptr.cast::<u8>()) }
}

#[repr(C)]
pub(crate) struct WorkerArena {
    base_ptr: NonNull<u8>,
    byte_len: usize,
    cursor_bytes: usize,
    generation: AtomicUsize,
}

// SAFETY: A `WorkerArena` is exclusively owned by one BFS worker thread.
// The `NonNull<u8>` points to a process-private mmap region. Sending the
// arena to another thread (e.g., during thread pool initialization) is safe
// because only one thread accesses it at a time via `&mut self`.
unsafe impl Send for WorkerArena {}

impl WorkerArena {
    pub(crate) fn new(capacity_i64s: usize) -> Self {
        assert!(
            capacity_i64s != 0,
            "WorkerArena capacity must be greater than 0"
        );

        let byte_len = checked_mul(capacity_i64s, I64_BYTES, "WorkerArena byte capacity");
        let base_ptr = map_anon(byte_len, "WorkerArena");

        Self {
            base_ptr,
            byte_len,
            cursor_bytes: 0,
            generation: AtomicUsize::new(0),
        }
    }

    pub(crate) fn alloc_state(&mut self, state_len: usize) -> &mut [i64] {
        // Capture diagnostics before the mutable borrow in try_alloc_state.
        let byte_len = self.byte_len;
        let cursor_bytes = self.cursor_bytes;
        match self.try_alloc_state(state_len) {
            Some(slot) => slot,
            None => {
                let alloc_bytes = state_len * I64_BYTES;
                panic!(
                    "WorkerArena out of memory: requested {alloc_bytes} bytes with {} bytes remaining",
                    byte_len.saturating_sub(cursor_bytes)
                );
            }
        }
    }

    /// Try to bump-allocate a flat state buffer from the arena.
    ///
    /// Returns `None` if the arena does not have enough capacity for `state_len`
    /// i64 words. Callers should fall back to heap allocation (e.g., `Vec<i64>`)
    /// when this returns `None` and log a warning on first occurrence.
    ///
    /// This is the fallback-safe counterpart of [`alloc_state`], which panics on
    /// exhaustion. BFS workers should prefer `try_alloc_state` so that specs with
    /// unexpectedly large BFS levels degrade gracefully to heap allocation instead
    /// of crashing.
    ///
    /// Part of #3990.
    pub(crate) fn try_alloc_state(&mut self, state_len: usize) -> Option<&mut [i64]> {
        if state_len == 0 {
            return Some(&mut []);
        }

        let alloc_bytes = checked_mul(state_len, I64_BYTES, "WorkerArena allocation size");
        let next_cursor = checked_add(
            self.cursor_bytes,
            alloc_bytes,
            "WorkerArena cursor advancement",
        );
        if next_cursor > self.byte_len {
            return None;
        }

        // SAFETY: `self.cursor_bytes <= self.byte_len` and `next_cursor <= self.byte_len`
        // were checked above, so the computed sub-slice lies fully within the mmap.
        // `cursor_bytes` always advances in multiples of `size_of::<i64>()`, so the
        // resulting pointer preserves `i64` alignment.
        let ptr = unsafe { self.base_ptr.as_ptr().add(self.cursor_bytes).cast::<i64>() };
        self.cursor_bytes = next_cursor;

        // SAFETY: `ptr` points to `state_len` contiguous `i64` values inside the live
        // mmap owned by this arena, and `&mut self` guarantees exclusive access while
        // the returned slice is alive.
        Some(unsafe { slice::from_raw_parts_mut(ptr, state_len) })
    }

    pub(crate) fn reset(&mut self) {
        self.cursor_bytes = 0;
        self.generation.fetch_add(1, Ordering::Relaxed);
    }

    pub(crate) fn generation(&self) -> usize {
        self.generation.load(Ordering::Relaxed)
    }

    /// Number of i64 words currently allocated (cursor position / 8).
    #[inline]
    pub(crate) fn used_words(&self) -> usize {
        self.cursor_bytes / I64_BYTES
    }

    /// Total capacity in i64 words.
    #[inline]
    pub(crate) fn capacity_words(&self) -> usize {
        self.byte_len / I64_BYTES
    }

    /// Remaining capacity in i64 words.
    #[inline]
    pub(crate) fn remaining_words(&self) -> usize {
        self.capacity_words() - self.used_words()
    }
}

impl fmt::Debug for WorkerArena {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WorkerArena")
            .field("base_ptr", &self.base_ptr)
            .field("byte_len", &self.byte_len)
            .field("cursor_bytes", &self.cursor_bytes)
            .field("generation", &self.generation())
            .finish()
    }
}

impl Drop for WorkerArena {
    fn drop(&mut self) {
        // SAFETY: `base_ptr` and `byte_len` come from a successful `mmap` call in `new`,
        // have not been unmapped yet, and describe the full extent of the mapping.
        let ret = unsafe { libc::munmap(self.base_ptr.as_ptr().cast(), self.byte_len) };
        debug_assert_eq!(
            ret,
            0,
            "WorkerArena munmap failed: {}",
            io::Error::last_os_error()
        );
    }
}

#[repr(C, align(64))]
struct CachePaddedAtomicUsize {
    value: AtomicUsize,
    _padding: [u8; CACHE_PADDING_BYTES],
}

impl CachePaddedAtomicUsize {
    const fn new(value: usize) -> Self {
        Self {
            value: AtomicUsize::new(value),
            _padding: [0; CACHE_PADDING_BYTES],
        }
    }
}

/// Mmap-backed fixed-size ring buffer for `[i64]` state vectors.
///
/// # MPMC (Multi-Producer Multi-Consumer) Design
///
/// `FlatQueue` implements a **lock-free bounded MPMC** queue using the
/// Vyukov per-slot sequence counter algorithm. Any number of threads may
/// call [`push`](FlatQueue::push) and [`pop`](FlatQueue::pop) concurrently.
///
/// **Algorithm (Dmitry Vyukov, "Bounded MPMC queue", 2010):**
/// - Each slot has a sequence counter initialized to its index.
/// - **Push:** Load `tail`, check the slot's sequence. If `seq == tail`
///   the slot is free; CAS `tail` to `tail + 1` to claim it. Write data,
///   then set the slot's sequence to `tail + 1` to signal consumers.
///   If `seq < tail` the queue is full; return `false`.
/// - **Pop:** Load `head`, check the slot's sequence. If `seq == head + 1`
///   the data is ready; CAS `head` to `head + 1` to claim it. Read data,
///   then set the slot's sequence to `head + capacity` to recycle the slot.
///   If `seq == head` the queue is empty; return `None`.
///
/// The CAS loop retries on contention (another thread claimed the same
/// position). This is lock-free: at least one thread makes progress per
/// CAS round.
///
/// For parallel BFS with N workers, this can be used directly as a shared
/// frontier queue, or via [`FlatQueuePool`] which manages per-worker queues
/// with level-synchronization barriers and work redistribution.
#[repr(C)]
pub(crate) struct FlatQueue {
    base_ptr: NonNull<u8>,
    byte_len: usize,
    state_len: usize,
    state_stride_bytes: usize,
    capacity: usize,
    mask: usize,
    head: CachePaddedAtomicUsize,
    tail: CachePaddedAtomicUsize,
    /// Per-slot sequence counters for Vyukov MPMC coordination.
    /// Slot `i` is initialized to sequence `i`. After a push at position `p`,
    /// the slot's sequence becomes `p + 1`. After a pop at position `p`, the
    /// slot's sequence becomes `p + capacity`.
    sequences: NonNull<AtomicUsize>,
    /// Byte length of the sequences mmap region.
    sequences_byte_len: usize,
}

// SAFETY: `FlatQueue` owns its mmap-backed buffer and per-slot sequence array.
// All concurrent access is mediated through CAS on head/tail and per-slot
// sequence counters. The queue never exposes references into the backing
// buffer, so moving it to another thread does not violate aliasing.
unsafe impl Send for FlatQueue {}

// SAFETY: Shared access is sound because `push` and `pop` use the Vyukov MPMC
// protocol: CAS on head/tail claims exclusive ownership of a slot, and per-slot
// sequence counters provide acquire/release synchronization between producers
// and consumers. Multiple producers and multiple consumers are safe.
unsafe impl Sync for FlatQueue {}

impl FlatQueue {
    pub(crate) fn new(capacity: usize, state_len: usize) -> Self {
        assert!(capacity != 0, "FlatQueue capacity must be greater than 0");
        assert!(state_len != 0, "FlatQueue state_len must be greater than 0");

        let capacity = capacity
            .checked_next_power_of_two()
            .unwrap_or_else(|| panic!("FlatQueue capacity overflow: {capacity}"));
        let state_stride_bytes = checked_mul(state_len, I64_BYTES, "FlatQueue state stride");
        let byte_len = checked_mul(capacity, state_stride_bytes, "FlatQueue backing size");
        let base_ptr = map_anon(byte_len, "FlatQueue");

        // Allocate per-slot sequence counters via mmap.
        let seq_bytes = checked_mul(
            capacity,
            size_of::<AtomicUsize>(),
            "FlatQueue sequence array size",
        );
        let seq_ptr = map_anon(seq_bytes, "FlatQueue sequences");

        // Initialize each slot's sequence to its index.
        // SAFETY: `seq_ptr` points to `capacity` AtomicUsize-sized slots in a
        // fresh zero-initialized mmap. We cast to `*mut AtomicUsize` and write
        // the initial sequence value for each slot.
        for i in 0..capacity {
            unsafe {
                let slot = seq_ptr
                    .as_ptr()
                    .cast::<AtomicUsize>()
                    .add(i);
                (*slot).store(i, Ordering::Relaxed);
            }
        }

        Self {
            base_ptr,
            byte_len,
            state_len,
            state_stride_bytes,
            capacity,
            mask: capacity - 1,
            head: CachePaddedAtomicUsize::new(0),
            tail: CachePaddedAtomicUsize::new(0),
            sequences: seq_ptr.cast(),
            sequences_byte_len: seq_bytes,
        }
    }

    fn slot_ptr(&self, index: usize) -> *mut i64 {
        let slot_index = index & self.mask;
        let byte_offset = checked_mul(slot_index, self.state_stride_bytes, "FlatQueue slot offset");

        // SAFETY: `slot_index < capacity`, so `byte_offset < byte_len`. The base pointer
        // comes from `mmap`, which is page-aligned, and each stride is a multiple of
        // `size_of::<i64>()`, so the cast preserves alignment.
        unsafe { self.base_ptr.as_ptr().add(byte_offset).cast::<i64>() }
    }

    /// Returns a reference to the sequence counter for the given slot index.
    ///
    /// # Safety
    ///
    /// `slot_index` must be `< self.capacity`.
    #[inline]
    fn slot_sequence(&self, slot_index: usize) -> &AtomicUsize {
        debug_assert!(slot_index < self.capacity);
        // SAFETY: `slot_index < capacity` ensures the pointer is within the
        // sequences mmap region. The region is aligned to `AtomicUsize` by
        // mmap's page alignment guarantee.
        unsafe { &*self.sequences.as_ptr().add(slot_index) }
    }

    /// Push a state vector into the queue. Returns `false` if the queue is full.
    ///
    /// Thread-safe: multiple producers may call `push` concurrently.
    pub(crate) fn push(&self, state: &[i64]) -> bool {
        assert_eq!(
            state.len(),
            self.state_len,
            "FlatQueue push expected state_len {}, got {}",
            self.state_len,
            state.len()
        );

        loop {
            let pos = self.tail.value.load(Ordering::Relaxed);
            let slot_index = pos & self.mask;
            let seq = self.slot_sequence(slot_index).load(Ordering::Acquire);

            if seq == pos {
                // Slot is free for this position. Try to claim it.
                if self
                    .tail
                    .value
                    .compare_exchange_weak(pos, pos + 1, Ordering::Relaxed, Ordering::Relaxed)
                    .is_ok()
                {
                    // We claimed position `pos`. Write data.
                    let dst = self.slot_ptr(pos);

                    // SAFETY: We own exclusive access to this slot via the CAS
                    // on tail + sequence protocol. The slot index is within
                    // bounds and the sequence check ensures no consumer is
                    // reading this slot.
                    unsafe {
                        ptr::copy_nonoverlapping(state.as_ptr(), dst, self.state_len);
                    }

                    // Signal consumers: set sequence to pos + 1.
                    self.slot_sequence(slot_index)
                        .store(pos + 1, Ordering::Release);
                    return true;
                }
                // CAS failed — another producer claimed this position. Retry.
            } else if seq.wrapping_sub(pos) > self.capacity {
                // The sequence is behind our position, meaning the slot is still
                // occupied by a consumer from a previous lap. Queue is full.
                return false;
            }
            // Otherwise another producer is writing to this slot (seq < pos but
            // within one lap). Spin and retry with a fresh tail load.
            std::hint::spin_loop();
        }
    }

    /// Pop a state vector from the queue into `out`. Returns `None` if empty.
    ///
    /// Thread-safe: multiple consumers may call `pop` concurrently.
    pub(crate) fn pop(&self, out: &mut [i64]) -> Option<()> {
        assert_eq!(
            out.len(),
            self.state_len,
            "FlatQueue pop expected state_len {}, got {}",
            self.state_len,
            out.len()
        );

        loop {
            let pos = self.head.value.load(Ordering::Relaxed);
            let slot_index = pos & self.mask;
            let seq = self.slot_sequence(slot_index).load(Ordering::Acquire);
            let expected = pos + 1;

            if seq == expected {
                // Slot has data ready for this position. Try to claim it.
                if self
                    .head
                    .value
                    .compare_exchange_weak(pos, pos + 1, Ordering::Relaxed, Ordering::Relaxed)
                    .is_ok()
                {
                    // We claimed position `pos`. Read data.
                    let src = self.slot_ptr(pos);

                    // SAFETY: The sequence check guarantees the producer has
                    // finished writing to this slot. We own exclusive read
                    // access via the CAS on head. `out` has `state_len` elems.
                    unsafe {
                        ptr::copy_nonoverlapping(src, out.as_mut_ptr(), self.state_len);
                    }

                    // Recycle: set sequence to pos + capacity.
                    self.slot_sequence(slot_index)
                        .store(pos + self.capacity, Ordering::Release);
                    return Some(());
                }
                // CAS failed — another consumer claimed this position. Retry.
            } else if seq == pos {
                // The slot's sequence equals the head position, meaning no
                // producer has written to it yet. Queue is empty.
                return None;
            }
            // Otherwise a producer is still writing to this slot (seq between
            // pos and pos + 1 in modular arithmetic). Spin and retry.
            std::hint::spin_loop();
        }
    }

    pub(crate) fn len(&self) -> usize {
        let head = self.head.value.load(Ordering::Acquire);
        let tail = self.tail.value.load(Ordering::Acquire);
        tail.saturating_sub(head)
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Total slot capacity (always a power of two).
    #[inline]
    pub(crate) fn capacity(&self) -> usize {
        self.capacity
    }

    /// Number of i64 words per state slot.
    #[inline]
    pub(crate) fn state_len(&self) -> usize {
        self.state_len
    }

    /// Reset the queue to empty, discarding all enqueued states.
    ///
    /// # Safety contract
    ///
    /// Must be called when **no** concurrent `push` or `pop` is in progress.
    /// Typically used at a BFS level-synchronization barrier.
    pub(crate) fn reset(&self) {
        self.head.value.store(0, Ordering::Relaxed);
        self.tail.value.store(0, Ordering::Relaxed);
        // Reinitialize per-slot sequences to their index.
        for i in 0..self.capacity {
            self.slot_sequence(i).store(i, Ordering::Relaxed);
        }
    }
}

impl fmt::Debug for FlatQueue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FlatQueue")
            .field("base_ptr", &self.base_ptr)
            .field("byte_len", &self.byte_len)
            .field("state_len", &self.state_len)
            .field("state_stride_bytes", &self.state_stride_bytes)
            .field("capacity", &self.capacity)
            .field("head", &self.head.value.load(Ordering::Relaxed))
            .field("tail", &self.tail.value.load(Ordering::Relaxed))
            .field("len", &self.len())
            .finish()
    }
}

impl Drop for FlatQueue {
    fn drop(&mut self) {
        // SAFETY: `base_ptr` and `byte_len` were returned by `mmap` in `new` and still
        // describe the owned mapping at drop time.
        let ret = unsafe { libc::munmap(self.base_ptr.as_ptr().cast(), self.byte_len) };
        debug_assert_eq!(
            ret,
            0,
            "FlatQueue munmap failed: {}",
            io::Error::last_os_error()
        );
        // SAFETY: `sequences` and `sequences_byte_len` were returned by `mmap` in `new`.
        let ret = unsafe {
            libc::munmap(
                self.sequences.as_ptr().cast(),
                self.sequences_byte_len,
            )
        };
        debug_assert_eq!(
            ret,
            0,
            "FlatQueue sequences munmap failed: {}",
            io::Error::last_os_error()
        );
    }
}

/// Pool of per-worker [`FlatQueue`] instances for parallel BFS.
///
/// Each BFS worker owns one queue (the worker pushes successor states to its
/// local queue, and pops from it for the next BFS level). The underlying
/// `FlatQueue` is MPMC-safe, so cross-worker stealing is possible in future
/// phases. Between BFS levels, [`redistribute`](FlatQueuePool::redistribute)
/// rebalances work across workers so no single queue starves.
///
/// This design minimizes contention by keeping most push/pop traffic local to
/// each worker's queue, with cross-worker communication at level barriers
/// where all workers are quiescent.
pub(crate) struct FlatQueuePool {
    queues: Vec<FlatQueue>,
    state_len: usize,
}

impl FlatQueuePool {
    /// Create a pool of `num_workers` queues, each with `capacity_per_worker`
    /// slots for states of `state_len` i64 words.
    pub(crate) fn new(num_workers: usize, capacity_per_worker: usize, state_len: usize) -> Self {
        assert!(num_workers > 0, "FlatQueuePool requires at least 1 worker");
        let queues = (0..num_workers)
            .map(|_| FlatQueue::new(capacity_per_worker, state_len))
            .collect();
        Self { queues, state_len }
    }

    /// Returns a reference to the queue for the given worker index.
    ///
    /// # Panics
    ///
    /// Panics if `worker_id >= num_workers()`.
    #[inline]
    pub(crate) fn queue(&self, worker_id: usize) -> &FlatQueue {
        &self.queues[worker_id]
    }

    /// Number of workers (queues) in the pool.
    #[inline]
    pub(crate) fn num_workers(&self) -> usize {
        self.queues.len()
    }

    /// Number of i64 words per state.
    #[inline]
    pub(crate) fn state_len(&self) -> usize {
        self.state_len
    }

    /// Total number of states across all queues.
    pub(crate) fn total_len(&self) -> usize {
        self.queues.iter().map(FlatQueue::len).sum()
    }

    /// Returns `true` if every queue in the pool is empty.
    pub(crate) fn all_empty(&self) -> bool {
        self.queues.iter().all(FlatQueue::is_empty)
    }

    /// Reset all queues to empty. Must be called at a level barrier when all
    /// workers are quiescent.
    pub(crate) fn reset_all(&self) {
        for q in &self.queues {
            q.reset();
        }
    }

    /// Redistribute states across worker queues for load balancing.
    ///
    /// Call this at a BFS level-synchronization barrier after all workers have
    /// finished producing successors and before the next level begins consuming.
    /// All workers must be quiescent (no concurrent push/pop).
    ///
    /// The algorithm:
    /// 1. Drain all states from all queues into a temporary buffer.
    /// 2. Reset all queues.
    /// 3. Round-robin assign states back to queues evenly.
    ///
    /// This is O(total_states) in both time and temporary memory. For very large
    /// frontiers this could be optimized to an in-place steal, but for Phase 7
    /// MVP correctness and simplicity take priority.
    pub(crate) fn redistribute(&self) {
        let total = self.total_len();
        if total == 0 {
            return;
        }

        // Drain all queues into a flat buffer.
        let mut buf = vec![0i64; total * self.state_len];
        let mut offset = 0;
        let mut tmp = vec![0i64; self.state_len];
        for q in &self.queues {
            while q.pop(&mut tmp).is_some() {
                buf[offset..offset + self.state_len].copy_from_slice(&tmp);
                offset += self.state_len;
            }
        }
        let state_count = offset / self.state_len;

        // Reset all queues (already empty from draining, but reset counters).
        self.reset_all();

        // Round-robin distribute states back.
        let num_workers = self.queues.len();
        for (i, chunk) in buf[..offset].chunks_exact(self.state_len).enumerate() {
            let target = i % num_workers;
            let pushed = self.queues[target].push(chunk);
            debug_assert!(
                pushed,
                "FlatQueuePool redistribute: queue {target} full after {i}/{state_count} states \
                 (capacity {})",
                self.queues[target].capacity()
            );
        }
    }
}

impl fmt::Debug for FlatQueuePool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FlatQueuePool")
            .field("num_workers", &self.queues.len())
            .field("state_len", &self.state_len)
            .field("total_len", &self.total_len())
            .field(
                "per_queue_len",
                &self.queues.iter().map(FlatQueue::len).collect::<Vec<_>>(),
            )
            .finish()
    }
}

/// Pool of per-worker [`WorkerArena`] instances for parallel BFS.
///
/// Each BFS worker owns one arena from which it bump-allocates successor state
/// buffers during a single BFS level. At the level barrier, `reset_all()` bulk-
/// frees every allocation simultaneously — O(1) per worker, zero per-state
/// `free()` calls. This is the "bulk-free at BFS level boundaries" pattern from
/// the Phase 7 design.
///
/// The pool owns `num_workers` arenas. Workers access their arena via
/// `arena_mut(worker_id)`.
///
/// ## Fallback on Exhaustion
///
/// When a worker's arena is exhausted (`try_alloc_state` returns `None`), the
/// caller should fall back to heap allocation (`vec![0i64; state_len]`) and
/// log a warning on first occurrence. The `fallback_count` stat tracks how many
/// times fallback occurred across all workers. A non-zero fallback count at the
/// end of BFS suggests increasing the per-worker arena capacity.
///
/// Part of #3990.
pub(crate) struct ArenaPool {
    arenas: Vec<WorkerArena>,
    /// Cumulative count of fallback-to-heap allocations across all workers.
    fallback_count: AtomicUsize,
}

impl ArenaPool {
    /// Create a pool of `num_workers` arenas, each with `capacity_per_worker_i64s`
    /// words of bump-allocation capacity.
    pub(crate) fn new(num_workers: usize, capacity_per_worker_i64s: usize) -> Self {
        assert!(num_workers > 0, "ArenaPool requires at least 1 worker");
        let arenas = (0..num_workers)
            .map(|_| WorkerArena::new(capacity_per_worker_i64s))
            .collect();
        Self {
            arenas,
            fallback_count: AtomicUsize::new(0),
        }
    }

    /// Exclusive access to the arena for `worker_id`.
    ///
    /// # Panics
    ///
    /// Panics if `worker_id >= num_workers()`.
    #[inline]
    pub(crate) fn arena_mut(&mut self, worker_id: usize) -> &mut WorkerArena {
        &mut self.arenas[worker_id]
    }

    /// Reset all arenas to empty (cursor = 0). Call at BFS level boundaries
    /// when all workers are quiescent. This is the zero-cost bulk-free.
    pub(crate) fn reset_all(&mut self) {
        for arena in &mut self.arenas {
            arena.reset();
        }
    }

    /// Number of workers (arenas) in the pool.
    #[inline]
    pub(crate) fn num_workers(&self) -> usize {
        self.arenas.len()
    }

    /// Total i64 words currently allocated across all arenas.
    pub(crate) fn total_used_words(&self) -> usize {
        self.arenas.iter().map(WorkerArena::used_words).sum()
    }

    /// Total i64 word capacity across all arenas.
    pub(crate) fn total_capacity_words(&self) -> usize {
        self.arenas.iter().map(WorkerArena::capacity_words).sum()
    }

    /// Record a fallback-to-heap allocation (thread-safe).
    ///
    /// Called by BFS workers when `try_alloc_state` returns `None` and the worker
    /// falls back to heap allocation. The first call also emits a warning to stderr.
    pub(crate) fn record_fallback(&self) {
        let prev = self.fallback_count.fetch_add(1, Ordering::Relaxed);
        if prev == 0 {
            eprintln!(
                "[arena-pool] WARNING: worker arena exhausted, falling back to heap allocation. \
                 Consider increasing arena capacity (current: {} words/worker).",
                if self.arenas.is_empty() {
                    0
                } else {
                    self.arenas[0].capacity_words()
                }
            );
        }
    }

    /// Number of fallback-to-heap allocations recorded.
    pub(crate) fn fallback_count(&self) -> usize {
        self.fallback_count.load(Ordering::Relaxed)
    }

    /// Report arena pool statistics to stderr.
    ///
    /// Called at the end of BFS exploration when `TLA2_ARENA_STATS=1`.
    pub(crate) fn report_stats(&self) {
        eprintln!("=== Arena Pool Stats ===");
        eprintln!("  Workers:          {}", self.arenas.len());
        eprintln!("  Total capacity:   {} words ({:.1} MB)",
            self.total_capacity_words(),
            (self.total_capacity_words() * I64_BYTES) as f64 / (1024.0 * 1024.0));
        eprintln!("  Heap fallbacks:   {}", self.fallback_count());
        for (i, arena) in self.arenas.iter().enumerate() {
            eprintln!(
                "  Worker {}: {} / {} words used, generation {}",
                i,
                arena.used_words(),
                arena.capacity_words(),
                arena.generation()
            );
        }
    }
}

impl fmt::Debug for ArenaPool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ArenaPool")
            .field("num_workers", &self.arenas.len())
            .field("total_used_words", &self.total_used_words())
            .field("total_capacity_words", &self.total_capacity_words())
            .field("fallback_count", &self.fallback_count())
            .field(
                "per_arena_used",
                &self
                    .arenas
                    .iter()
                    .map(WorkerArena::used_words)
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

/// Mmap-backed reusable scratch buffer for temporary state assembly.
///
/// During successor generation, each worker needs a temporary `[i64]` buffer to
/// assemble the next state before pushing it into the arena or queue. Using a
/// `Vec<i64>` would allocate/deallocate on every successor — the scratch buffer
/// allocates once (via mmap) and reuses the same memory for every successor.
///
/// Exclusively owned by one worker thread (`&mut self` for writes).
pub(crate) struct ScratchBuffer {
    buf: NonNull<i64>,
    byte_len: usize,
    state_len: usize,
}

// SAFETY: `ScratchBuffer` owns a process-private mmap region. The `NonNull<i64>`
// does not alias any other allocation. Sending to another thread is safe because
// only one thread uses it at a time via `&mut self`.
unsafe impl Send for ScratchBuffer {}

impl ScratchBuffer {
    /// Create a new scratch buffer for states of `state_len` i64 words.
    pub(crate) fn new(state_len: usize) -> Self {
        assert!(
            state_len != 0,
            "ScratchBuffer state_len must be greater than 0"
        );
        let byte_len = checked_mul(state_len, I64_BYTES, "ScratchBuffer byte size");
        let raw = map_anon(byte_len, "ScratchBuffer");

        Self {
            // SAFETY: `map_anon` returns a page-aligned pointer. Page alignment
            // satisfies `i64` alignment (8 bytes). The mapping has `byte_len`
            // bytes = `state_len * 8`, so the cast to `*mut i64` with length
            // `state_len` is valid.
            buf: raw.cast(),
            byte_len,
            state_len,
        }
    }

    /// Read-only view of the buffer contents.
    #[inline]
    pub(crate) fn as_slice(&self) -> &[i64] {
        // SAFETY: `buf` points to `state_len` contiguous i64 values in a live
        // mmap, and `&self` guarantees no mutable alias exists.
        unsafe { slice::from_raw_parts(self.buf.as_ptr(), self.state_len) }
    }

    /// Mutable view of the buffer contents.
    #[inline]
    pub(crate) fn as_mut_slice(&mut self) -> &mut [i64] {
        // SAFETY: `buf` points to `state_len` contiguous i64 values in a live
        // mmap, and `&mut self` guarantees exclusive access.
        unsafe { slice::from_raw_parts_mut(self.buf.as_ptr(), self.state_len) }
    }

    /// Number of i64 words in this buffer.
    #[inline]
    pub(crate) fn state_len(&self) -> usize {
        self.state_len
    }

    /// Zero-fill the buffer contents (useful between successor generations).
    pub(crate) fn zero(&mut self) {
        // SAFETY: `buf` points to `state_len` i64 values in a live mmap, and
        // `&mut self` guarantees exclusive access. Writing zeros is always valid
        // for `i64`.
        unsafe {
            ptr::write_bytes(self.buf.as_ptr(), 0, self.state_len);
        }
    }
}

impl fmt::Debug for ScratchBuffer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ScratchBuffer")
            .field("buf", &self.buf)
            .field("state_len", &self.state_len)
            .field("byte_len", &self.byte_len)
            .finish()
    }
}

impl Drop for ScratchBuffer {
    fn drop(&mut self) {
        // SAFETY: `buf` (cast back to `*mut u8`) and `byte_len` describe the
        // mmap region allocated in `new`. It has not been unmapped yet.
        let ret = unsafe { libc::munmap(self.buf.as_ptr().cast(), self.byte_len) };
        debug_assert_eq!(
            ret,
            0,
            "ScratchBuffer munmap failed: {}",
            io::Error::last_os_error()
        );
    }
}

/// Snapshot of arena allocation statistics for benchmarking.
///
/// Captures before/after state of an arena to measure allocation throughput
/// without heap measurement tools. Used by the `arena_alloc` benchmark.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ArenaBenchStats {
    pub(crate) allocations: usize,
    pub(crate) words_allocated: usize,
    pub(crate) resets: usize,
}

impl ArenaBenchStats {
    /// Measure the cost of `count` bump allocations of `state_len` words each,
    /// with a reset every `reset_every` allocations. Returns stats.
    ///
    /// This is a self-contained benchmark kernel: it creates its own arena,
    /// runs the allocation pattern, and reports results. Zero heap allocations
    /// occur in the hot loop.
    pub(crate) fn run_arena_bench(
        count: usize,
        state_len: usize,
        reset_every: usize,
    ) -> Self {
        assert!(reset_every > 0, "reset_every must be > 0");
        let capacity = checked_mul(reset_every, state_len, "arena bench capacity");
        let mut arena = WorkerArena::new(capacity);
        let mut stats = Self {
            allocations: 0,
            words_allocated: 0,
            resets: 0,
        };

        for i in 0..count {
            if i > 0 && i % reset_every == 0 {
                arena.reset();
                stats.resets += 1;
            }
            let slot = arena.alloc_state(state_len);
            // Touch memory to prevent elision.
            slot[0] = i as i64;
            stats.allocations += 1;
            stats.words_allocated += state_len;
        }

        stats
    }

    /// Measure the cost of `count` heap (Vec) allocations of `state_len` words
    /// each. Each allocation creates and drops a Vec — the current allocator
    /// baseline that arenas replace.
    pub(crate) fn run_heap_bench(count: usize, state_len: usize) -> Self {
        let mut stats = Self {
            allocations: 0,
            words_allocated: 0,
            resets: 0,
        };

        for i in 0..count {
            let mut v = vec![0i64; state_len];
            // Touch memory to prevent elision.
            v[0] = i as i64;
            std::hint::black_box(&v);
            drop(v);
            stats.allocations += 1;
            stats.words_allocated += state_len;
        }

        stats
    }
}

#[cfg(test)]
mod tests {
    use super::{FlatQueue, ScratchBuffer, WorkerArena};
    use std::slice;
    use std::sync::Arc;
    use std::thread;

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_worker_arena_basic_alloc() {
        let mut arena = WorkerArena::new(6);

        let first_ptr = {
            let first = arena.alloc_state(2);
            first.copy_from_slice(&[11, 12]);
            first.as_ptr()
        };
        let second_ptr = {
            let second = arena.alloc_state(3);
            second.copy_from_slice(&[21, 22, 23]);
            second.as_ptr()
        };
        let third = arena.alloc_state(1);
        third.copy_from_slice(&[31]);

        // SAFETY: These pointers were returned from live arena allocations above.
        // The arena has not been reset or dropped, so the memory remains valid.
        unsafe {
            assert_eq!(slice::from_raw_parts(first_ptr, 2), &[11, 12]);
            assert_eq!(slice::from_raw_parts(second_ptr, 3), &[21, 22, 23]);
        }
        assert_eq!(third, &[31]);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_worker_arena_reset() {
        let mut arena = WorkerArena::new(4);

        let first_addr = {
            let first = arena.alloc_state(2);
            first.copy_from_slice(&[1, 2]);
            first.as_mut_ptr() as usize
        };

        arena.reset();

        let second_addr = {
            let second = arena.alloc_state(2);
            second.copy_from_slice(&[3, 4]);
            assert_eq!(second, &[3, 4]);
            second.as_mut_ptr() as usize
        };

        assert_eq!(first_addr, second_addr);
        assert_eq!(arena.generation(), 1);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    #[should_panic(expected = "WorkerArena out of memory")]
    fn test_worker_arena_capacity_exhaustion() {
        let mut arena = WorkerArena::new(4);
        {
            let state = arena.alloc_state(4);
            state.copy_from_slice(&[1, 2, 3, 4]);
        }
        let _ = arena.alloc_state(1);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_worker_arena_accessors() {
        let mut arena = WorkerArena::new(10);
        assert_eq!(arena.capacity_words(), 10);
        assert_eq!(arena.used_words(), 0);
        assert_eq!(arena.remaining_words(), 10);
        assert_eq!(arena.generation(), 0);

        let _ = arena.alloc_state(3);
        assert_eq!(arena.used_words(), 3);
        assert_eq!(arena.remaining_words(), 7);

        arena.reset();
        assert_eq!(arena.used_words(), 0);
        assert_eq!(arena.generation(), 1);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_flat_queue_accessors() {
        let queue = FlatQueue::new(5, 3);
        // capacity rounds up to next power of two
        assert_eq!(queue.capacity(), 8);
        assert_eq!(queue.state_len(), 3);
        assert!(queue.is_empty());
        assert_eq!(queue.len(), 0);

        assert!(queue.push(&[1, 2, 3]));
        assert!(!queue.is_empty());
        assert_eq!(queue.len(), 1);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_flat_queue_push_pop() {
        let queue = FlatQueue::new(4, 3);

        assert!(queue.push(&[1, 2, 3]));
        assert!(queue.push(&[4, 5, 6]));
        assert!(queue.push(&[7, 8, 9]));

        let mut out = [0_i64; 3];
        assert_eq!(queue.pop(&mut out), Some(()));
        assert_eq!(out, [1, 2, 3]);
        assert_eq!(queue.pop(&mut out), Some(()));
        assert_eq!(out, [4, 5, 6]);
        assert_eq!(queue.pop(&mut out), Some(()));
        assert_eq!(out, [7, 8, 9]);
        assert_eq!(queue.pop(&mut out), None);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_flat_queue_empty_pop() {
        let queue = FlatQueue::new(2, 2);
        let mut out = [0_i64; 2];
        assert_eq!(queue.pop(&mut out), None);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_flat_queue_full() {
        let queue = FlatQueue::new(4, 2);

        assert!(queue.push(&[1, 1]));
        assert!(queue.push(&[2, 2]));
        assert!(queue.push(&[3, 3]));
        assert!(queue.push(&[4, 4]));
        assert!(!queue.push(&[5, 5]));
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_flat_queue_wrap_around() {
        let queue = FlatQueue::new(4, 2);
        let mut out = [0_i64; 2];

        assert!(queue.push(&[1, 10]));
        assert!(queue.push(&[2, 20]));
        assert!(queue.push(&[3, 30]));
        assert!(queue.push(&[4, 40]));

        assert_eq!(queue.pop(&mut out), Some(()));
        assert_eq!(out, [1, 10]);
        assert_eq!(queue.pop(&mut out), Some(()));
        assert_eq!(out, [2, 20]);

        assert!(queue.push(&[5, 50]));
        assert!(queue.push(&[6, 60]));

        assert_eq!(queue.pop(&mut out), Some(()));
        assert_eq!(out, [3, 30]);
        assert_eq!(queue.pop(&mut out), Some(()));
        assert_eq!(out, [4, 40]);
        assert_eq!(queue.pop(&mut out), Some(()));
        assert_eq!(out, [5, 50]);
        assert_eq!(queue.pop(&mut out), Some(()));
        assert_eq!(out, [6, 60]);
        assert_eq!(queue.pop(&mut out), None);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_flat_queue_multi_thread() {
        const COUNT: usize = 2048;
        let queue = Arc::new(FlatQueue::new(64, 3));

        let producer_queue = Arc::clone(&queue);
        let producer = thread::spawn(move || {
            for i in 0..COUNT {
                let state = [i as i64, i as i64 + 1, i as i64 + 2];
                while !producer_queue.push(&state) {
                    thread::yield_now();
                }
            }
        });

        let consumer_queue = Arc::clone(&queue);
        let consumer = thread::spawn(move || {
            let mut collected = Vec::with_capacity(COUNT);
            for _ in 0..COUNT {
                let mut out = [0_i64; 3];
                loop {
                    if consumer_queue.pop(&mut out).is_some() {
                        collected.push(out);
                        break;
                    }
                    thread::yield_now();
                }
            }
            collected
        });

        producer.join().expect("producer thread should succeed");
        let collected = consumer.join().expect("consumer thread should succeed");

        assert_eq!(collected.len(), COUNT);
        for (i, state) in collected.iter().enumerate() {
            assert_eq!(*state, [i as i64, i as i64 + 1, i as i64 + 2]);
        }
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(30000))]
    fn test_flat_queue_mpmc_multi_producer() {
        // 4 producers, 1 consumer. Each producer pushes COUNT states with a
        // unique tag in the first i64, so we can verify all arrive.
        const COUNT_PER_PRODUCER: usize = 512;
        const NUM_PRODUCERS: usize = 4;
        const TOTAL: usize = COUNT_PER_PRODUCER * NUM_PRODUCERS;
        let queue = Arc::new(FlatQueue::new(128, 2));

        let mut producers = Vec::new();
        for pid in 0..NUM_PRODUCERS {
            let q = Arc::clone(&queue);
            producers.push(thread::spawn(move || {
                for i in 0..COUNT_PER_PRODUCER {
                    let tag = (pid * COUNT_PER_PRODUCER + i) as i64;
                    let state = [tag, tag * 10];
                    while !q.push(&state) {
                        thread::yield_now();
                    }
                }
            }));
        }

        let consumer_queue = Arc::clone(&queue);
        let consumer = thread::spawn(move || {
            let mut collected = Vec::with_capacity(TOTAL);
            for _ in 0..TOTAL {
                let mut out = [0_i64; 2];
                loop {
                    if consumer_queue.pop(&mut out).is_some() {
                        collected.push(out);
                        break;
                    }
                    thread::yield_now();
                }
            }
            collected
        });

        for p in producers {
            p.join().expect("producer thread should succeed");
        }
        let collected = consumer.join().expect("consumer thread should succeed");

        assert_eq!(collected.len(), TOTAL);
        // Verify all unique tags arrived (order may differ due to concurrency).
        let mut tags: Vec<i64> = collected.iter().map(|s| s[0]).collect();
        tags.sort_unstable();
        let expected_tags: Vec<i64> = (0..TOTAL as i64).collect();
        assert_eq!(tags, expected_tags);
        // Verify second field matches tag * 10.
        for state in &collected {
            assert_eq!(state[1], state[0] * 10);
        }
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(30000))]
    fn test_flat_queue_mpmc_multi_consumer() {
        // 1 producer, 4 consumers. Each consumer collects what it can.
        const TOTAL: usize = 2048;
        const NUM_CONSUMERS: usize = 4;
        let queue = Arc::new(FlatQueue::new(128, 2));

        let producer_queue = Arc::clone(&queue);
        let producer = thread::spawn(move || {
            for i in 0..TOTAL {
                let state = [i as i64, i as i64 + 1000];
                while !producer_queue.push(&state) {
                    thread::yield_now();
                }
            }
        });

        let mut consumers = Vec::new();
        // Use a shared counter so consumers know when to stop.
        let remaining = Arc::new(std::sync::atomic::AtomicUsize::new(TOTAL));
        for _ in 0..NUM_CONSUMERS {
            let q = Arc::clone(&queue);
            let rem = Arc::clone(&remaining);
            consumers.push(thread::spawn(move || {
                let mut collected = Vec::new();
                loop {
                    if rem.load(std::sync::atomic::Ordering::Relaxed) == 0 {
                        break;
                    }
                    let mut out = [0_i64; 2];
                    if q.pop(&mut out).is_some() {
                        collected.push(out);
                        rem.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
                    } else {
                        thread::yield_now();
                    }
                }
                collected
            }));
        }

        producer.join().expect("producer thread should succeed");
        let mut all_collected = Vec::with_capacity(TOTAL);
        for c in consumers {
            all_collected.extend(c.join().expect("consumer thread should succeed"));
        }

        assert_eq!(all_collected.len(), TOTAL);
        // Verify all unique values arrived.
        let mut tags: Vec<i64> = all_collected.iter().map(|s| s[0]).collect();
        tags.sort_unstable();
        let expected: Vec<i64> = (0..TOTAL as i64).collect();
        assert_eq!(tags, expected);
        for state in &all_collected {
            assert_eq!(state[1], state[0] + 1000);
        }
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(30000))]
    fn test_flat_queue_mpmc_full() {
        // 4 producers, 4 consumers, all running simultaneously.
        const COUNT_PER_PRODUCER: usize = 256;
        const NUM_PRODUCERS: usize = 4;
        const NUM_CONSUMERS: usize = 4;
        const TOTAL: usize = COUNT_PER_PRODUCER * NUM_PRODUCERS;
        let queue = Arc::new(FlatQueue::new(64, 1));

        let mut handles = Vec::new();

        // Producers.
        for pid in 0..NUM_PRODUCERS {
            let q = Arc::clone(&queue);
            handles.push(thread::spawn(move || {
                for i in 0..COUNT_PER_PRODUCER {
                    let tag = (pid * COUNT_PER_PRODUCER + i) as i64;
                    while !q.push(&[tag]) {
                        thread::yield_now();
                    }
                }
                Vec::<[i64; 1]>::new() // producers return empty
            }));
        }

        // Consumers.
        let remaining = Arc::new(std::sync::atomic::AtomicUsize::new(TOTAL));
        for _ in 0..NUM_CONSUMERS {
            let q = Arc::clone(&queue);
            let rem = Arc::clone(&remaining);
            handles.push(thread::spawn(move || {
                let mut collected = Vec::new();
                loop {
                    if rem.load(std::sync::atomic::Ordering::Relaxed) == 0 {
                        break;
                    }
                    let mut out = [0_i64; 1];
                    if q.pop(&mut out).is_some() {
                        collected.push(out);
                        rem.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
                    } else {
                        thread::yield_now();
                    }
                }
                collected
            }));
        }

        let mut all_collected = Vec::with_capacity(TOTAL);
        for h in handles {
            all_collected.extend(h.join().expect("thread should succeed"));
        }

        assert_eq!(all_collected.len(), TOTAL);
        let mut tags: Vec<i64> = all_collected.iter().map(|s| s[0]).collect();
        tags.sort_unstable();
        let expected: Vec<i64> = (0..TOTAL as i64).collect();
        assert_eq!(tags, expected);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_flat_queue_reset() {
        let queue = FlatQueue::new(4, 2);
        assert!(queue.push(&[1, 2]));
        assert!(queue.push(&[3, 4]));
        assert_eq!(queue.len(), 2);

        queue.reset();
        assert!(queue.is_empty());
        assert_eq!(queue.len(), 0);

        // Can push again after reset.
        assert!(queue.push(&[5, 6]));
        let mut out = [0_i64; 2];
        assert_eq!(queue.pop(&mut out), Some(()));
        assert_eq!(out, [5, 6]);
    }

    // --- FlatQueuePool tests ---

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_flat_queue_pool_basic() {
        let pool = super::FlatQueuePool::new(4, 16, 3);
        assert_eq!(pool.num_workers(), 4);
        assert_eq!(pool.state_len(), 3);
        assert!(pool.all_empty());
        assert_eq!(pool.total_len(), 0);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_flat_queue_pool_per_worker_push_pop() {
        let pool = super::FlatQueuePool::new(3, 8, 2);

        // Each worker pushes to its own queue.
        pool.queue(0).push(&[10, 11]);
        pool.queue(0).push(&[12, 13]);
        pool.queue(1).push(&[20, 21]);
        pool.queue(2).push(&[30, 31]);
        pool.queue(2).push(&[32, 33]);
        pool.queue(2).push(&[34, 35]);

        assert_eq!(pool.total_len(), 6);
        assert!(!pool.all_empty());

        // Pop from individual queues.
        let mut out = [0i64; 2];
        assert_eq!(pool.queue(0).pop(&mut out), Some(()));
        assert_eq!(out, [10, 11]);
        assert_eq!(pool.queue(1).pop(&mut out), Some(()));
        assert_eq!(out, [20, 21]);
        assert_eq!(pool.queue(1).pop(&mut out), None); // Worker 1 is empty.
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_flat_queue_pool_redistribute_even() {
        let pool = super::FlatQueuePool::new(3, 16, 2);

        // Load all states into worker 0.
        for i in 0..9 {
            pool.queue(0).push(&[i as i64, i as i64 * 10]);
        }
        assert_eq!(pool.queue(0).len(), 9);
        assert_eq!(pool.queue(1).len(), 0);
        assert_eq!(pool.queue(2).len(), 0);

        // Redistribute.
        pool.redistribute();

        // 9 states across 3 workers: 3 each.
        assert_eq!(pool.queue(0).len(), 3);
        assert_eq!(pool.queue(1).len(), 3);
        assert_eq!(pool.queue(2).len(), 3);
        assert_eq!(pool.total_len(), 9);

        // Verify round-robin assignment: states 0,3,6 -> q0; 1,4,7 -> q1; 2,5,8 -> q2.
        let mut out = [0i64; 2];
        pool.queue(0).pop(&mut out);
        assert_eq!(out, [0, 0]);
        pool.queue(0).pop(&mut out);
        assert_eq!(out, [3, 30]);
        pool.queue(0).pop(&mut out);
        assert_eq!(out, [6, 60]);

        pool.queue(1).pop(&mut out);
        assert_eq!(out, [1, 10]);
        pool.queue(1).pop(&mut out);
        assert_eq!(out, [4, 40]);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_flat_queue_pool_redistribute_uneven() {
        let pool = super::FlatQueuePool::new(2, 16, 1);

        // 5 states split across 2 workers: worker 0 gets 3, worker 1 gets 2.
        pool.queue(0).push(&[100]);
        pool.queue(0).push(&[200]);
        pool.queue(0).push(&[300]);
        pool.queue(1).push(&[400]);
        pool.queue(1).push(&[500]);

        pool.redistribute();

        // 5 states round-robin across 2: q0 gets indices 0,2,4 (3 states),
        // q1 gets indices 1,3 (2 states).
        assert_eq!(pool.queue(0).len(), 3);
        assert_eq!(pool.queue(1).len(), 2);
        assert_eq!(pool.total_len(), 5);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_flat_queue_pool_redistribute_empty() {
        let pool = super::FlatQueuePool::new(4, 8, 2);
        // Redistributing an empty pool is a no-op.
        pool.redistribute();
        assert!(pool.all_empty());
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_flat_queue_pool_reset_all() {
        let pool = super::FlatQueuePool::new(2, 8, 2);
        pool.queue(0).push(&[1, 2]);
        pool.queue(1).push(&[3, 4]);
        assert_eq!(pool.total_len(), 2);

        pool.reset_all();
        assert!(pool.all_empty());
    }

    // --- ArenaPool tests ---

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_arena_pool_basic() {
        let mut pool = super::ArenaPool::new(3, 100);
        assert_eq!(pool.num_workers(), 3);
        assert_eq!(pool.total_capacity_words(), 300);
        assert_eq!(pool.total_used_words(), 0);

        // Allocate from different workers — verify isolation.
        let s0 = pool.arena_mut(0).alloc_state(5);
        s0.copy_from_slice(&[10, 20, 30, 40, 50]);

        let s1 = pool.arena_mut(1).alloc_state(3);
        s1.copy_from_slice(&[100, 200, 300]);

        let s2 = pool.arena_mut(2).alloc_state(2);
        s2.copy_from_slice(&[1000, 2000]);

        assert_eq!(pool.total_used_words(), 10); // 5 + 3 + 2
        assert_eq!(pool.arena_mut(0).used_words(), 5);
        assert_eq!(pool.arena_mut(1).used_words(), 3);
        assert_eq!(pool.arena_mut(2).used_words(), 2);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_arena_pool_reset_all() {
        let mut pool = super::ArenaPool::new(2, 50);

        pool.arena_mut(0).alloc_state(10);
        pool.arena_mut(1).alloc_state(20);
        assert_eq!(pool.total_used_words(), 30);

        let gen0_before = pool.arena_mut(0).generation();
        let gen1_before = pool.arena_mut(1).generation();

        pool.reset_all();

        assert_eq!(pool.total_used_words(), 0);
        assert_eq!(pool.arena_mut(0).generation(), gen0_before + 1);
        assert_eq!(pool.arena_mut(1).generation(), gen1_before + 1);

        // Can allocate again after reset.
        let s = pool.arena_mut(0).alloc_state(5);
        s.copy_from_slice(&[1, 2, 3, 4, 5]);
        assert_eq!(s, &[1, 2, 3, 4, 5]);
    }

    // --- ScratchBuffer tests ---

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_scratch_buffer_basic() {
        let mut scratch = ScratchBuffer::new(4);
        assert_eq!(scratch.state_len(), 4);

        // Write and read back.
        let buf = scratch.as_mut_slice();
        buf.copy_from_slice(&[11, 22, 33, 44]);
        assert_eq!(scratch.as_slice(), &[11, 22, 33, 44]);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_scratch_buffer_zero() {
        let mut scratch = ScratchBuffer::new(3);
        let buf = scratch.as_mut_slice();
        buf.copy_from_slice(&[99, 88, 77]);
        assert_eq!(scratch.as_slice(), &[99, 88, 77]);

        scratch.zero();
        assert_eq!(scratch.as_slice(), &[0, 0, 0]);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_scratch_buffer_reuse() {
        let mut scratch = ScratchBuffer::new(2);

        // First use.
        scratch.as_mut_slice().copy_from_slice(&[1, 2]);
        assert_eq!(scratch.as_slice(), &[1, 2]);

        // Overwrite without zeroing.
        scratch.as_mut_slice().copy_from_slice(&[3, 4]);
        assert_eq!(scratch.as_slice(), &[3, 4]);
    }

    // --- ArenaBenchStats tests ---

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_arena_bench_stats_run() {
        let stats = super::ArenaBenchStats::run_arena_bench(100, 4, 25);
        assert_eq!(stats.allocations, 100);
        assert_eq!(stats.words_allocated, 400);
        assert_eq!(stats.resets, 3); // resets at i=25, 50, 75
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_heap_bench_stats_run() {
        let stats = super::ArenaBenchStats::run_heap_bench(50, 8);
        assert_eq!(stats.allocations, 50);
        assert_eq!(stats.words_allocated, 400);
        assert_eq!(stats.resets, 0);
    }

    // ========================================================================
    // try_alloc_state and fallback tests
    // Part of #3990: graceful fallback when arena is exhausted
    // ========================================================================

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_worker_arena_try_alloc_state_success() {
        let mut arena = WorkerArena::new(10);
        let slot = arena.try_alloc_state(3);
        assert!(slot.is_some());
        let slot = slot.unwrap();
        assert_eq!(slot.len(), 3);
        slot.copy_from_slice(&[10, 20, 30]);
        assert_eq!(slot, &[10, 20, 30]);
        assert_eq!(arena.used_words(), 3);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_worker_arena_try_alloc_state_exhaustion_returns_none() {
        let mut arena = WorkerArena::new(4);
        // Fill the arena completely.
        let slot = arena.try_alloc_state(4);
        assert!(slot.is_some());
        slot.unwrap().copy_from_slice(&[1, 2, 3, 4]);
        assert_eq!(arena.used_words(), 4);
        assert_eq!(arena.remaining_words(), 0);

        // Next allocation should return None, not panic.
        let result = arena.try_alloc_state(1);
        assert!(result.is_none());

        // Larger allocation also returns None.
        let result = arena.try_alloc_state(10);
        assert!(result.is_none());
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_worker_arena_try_alloc_state_empty_slice() {
        let mut arena = WorkerArena::new(4);
        let slot = arena.try_alloc_state(0);
        assert!(slot.is_some());
        assert!(slot.unwrap().is_empty());
        assert_eq!(arena.used_words(), 0);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_worker_arena_try_alloc_state_exact_fit() {
        let mut arena = WorkerArena::new(8);
        // Allocate exactly the capacity.
        let slot = arena.try_alloc_state(8);
        assert!(slot.is_some());
        assert_eq!(slot.unwrap().len(), 8);
        assert_eq!(arena.used_words(), 8);
        assert_eq!(arena.remaining_words(), 0);

        // Nothing left.
        assert!(arena.try_alloc_state(1).is_none());
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_worker_arena_try_alloc_then_reset_and_reuse() {
        let mut arena = WorkerArena::new(6);

        // Fill it.
        arena.try_alloc_state(6).unwrap().copy_from_slice(&[1, 2, 3, 4, 5, 6]);
        assert!(arena.try_alloc_state(1).is_none());

        // Reset.
        arena.reset();
        assert_eq!(arena.used_words(), 0);
        assert_eq!(arena.remaining_words(), 6);
        assert_eq!(arena.generation(), 1);

        // Allocate again.
        let slot = arena.try_alloc_state(4);
        assert!(slot.is_some());
        let slot = slot.unwrap();
        slot.copy_from_slice(&[10, 20, 30, 40]);
        assert_eq!(slot, &[10, 20, 30, 40]);
        assert_eq!(arena.used_words(), 4);
    }

    // ========================================================================
    // ArenaPool fallback tracking tests
    // ========================================================================

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_arena_pool_fallback_count() {
        let pool = super::ArenaPool::new(2, 10);
        assert_eq!(pool.fallback_count(), 0);

        pool.record_fallback();
        assert_eq!(pool.fallback_count(), 1);

        pool.record_fallback();
        pool.record_fallback();
        assert_eq!(pool.fallback_count(), 3);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_arena_pool_try_alloc_with_fallback() {
        let mut pool = super::ArenaPool::new(2, 5);

        // Worker 0 allocates 5 words (full capacity).
        let slot = pool.arena_mut(0).try_alloc_state(5);
        assert!(slot.is_some());
        slot.unwrap().copy_from_slice(&[1, 2, 3, 4, 5]);

        // Worker 0 exhausted — try_alloc returns None.
        let result = pool.arena_mut(0).try_alloc_state(1);
        assert!(result.is_none());
        // Record fallback.
        pool.record_fallback();

        // Worker 1 still has capacity.
        let slot = pool.arena_mut(1).try_alloc_state(3);
        assert!(slot.is_some());

        assert_eq!(pool.fallback_count(), 1);
    }

    // ========================================================================
    // BFS lifecycle simulation tests
    // Part of #3990: full arena lifecycle — alloc, dedup, promote, reset
    // ========================================================================

    /// Simulate a complete BFS level using ArenaPool:
    /// 1. Allocate successor states from arena
    /// 2. Compute fingerprints (simple hash)
    /// 3. Dedup against seen set
    /// 4. Promote new states to heap (simulating seen-set insertion)
    /// 5. Reset arena at level boundary
    /// 6. Verify promoted states survive reset
    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_arena_bfs_level_lifecycle() {
        let state_len = 5;
        let num_successors = 100;
        let mut pool = super::ArenaPool::new(1, state_len * num_successors);

        // Phase 1: Allocate successors in the arena.
        let mut arena_ptrs: Vec<*const i64> = Vec::new();
        for i in 0..num_successors {
            let slot = pool.arena_mut(0).alloc_state(state_len);
            for (j, val) in slot.iter_mut().enumerate() {
                *val = (i * 10 + j) as i64;
            }
            arena_ptrs.push(slot.as_ptr());
        }
        assert_eq!(pool.arena_mut(0).used_words(), state_len * num_successors);

        // Phase 2: Simulate dedup — 95% are duplicates, 5% are new.
        // "Promote" the 5 new states to heap storage.
        let new_indices = [3, 17, 42, 78, 95];
        let mut promoted: Vec<Vec<i64>> = Vec::new();
        for &idx in &new_indices {
            // SAFETY: arena_ptrs[idx] points to state_len i64 values in the
            // live arena (not yet reset). We read them to simulate promotion.
            let state_data: Vec<i64> = unsafe {
                slice::from_raw_parts(arena_ptrs[idx], state_len)
            }.to_vec();
            promoted.push(state_data);
        }

        // Phase 3: Verify promoted states have correct values.
        for (pi, &idx) in new_indices.iter().enumerate() {
            for j in 0..state_len {
                assert_eq!(
                    promoted[pi][j],
                    (idx * 10 + j) as i64,
                    "promoted state {pi} (original idx {idx}), var {j}"
                );
            }
        }

        // Phase 4: Reset arena (BFS level boundary).
        pool.reset_all();
        assert_eq!(pool.arena_mut(0).used_words(), 0);
        assert_eq!(pool.arena_mut(0).generation(), 1);

        // Phase 5: Promoted states must survive arena reset (they're on the heap).
        for (pi, &idx) in new_indices.iter().enumerate() {
            assert_eq!(promoted[pi][0], (idx * 10) as i64);
        }

        // Phase 6: Arena is reusable for next BFS level.
        let slot = pool.arena_mut(0).alloc_state(state_len);
        slot.copy_from_slice(&[999, 888, 777, 666, 555]);
        assert_eq!(slot, &[999, 888, 777, 666, 555]);
    }

    /// Simulate multiple BFS levels with arena reset between each.
    /// Verifies cumulative stats and arena reuse.
    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_arena_multi_level_bfs_simulation() {
        let state_len = 8;
        let allocs_per_level = 200;
        let levels = 5;
        // Each level needs state_len * allocs_per_level = 1600 words.
        let capacity = state_len * allocs_per_level;
        let mut pool = super::ArenaPool::new(2, capacity);

        for level in 0..levels {
            for worker_id in 0..2 {
                for i in 0..allocs_per_level / 2 {
                    let slot = pool.arena_mut(worker_id).alloc_state(state_len);
                    // Write unique data per level/worker/alloc.
                    slot[0] = level as i64;
                    slot[1] = worker_id as i64;
                    slot[2] = i as i64;
                    // Verify we can read it back.
                    assert_eq!(slot[0], level as i64);
                    assert_eq!(slot[1], worker_id as i64);
                    assert_eq!(slot[2], i as i64);
                }
            }
            // Level boundary: reset all arenas.
            pool.reset_all();
        }

        // After 5 levels, all arenas should be empty.
        assert_eq!(pool.total_used_words(), 0);
        // Generations should reflect resets.
        assert_eq!(pool.arena_mut(0).generation(), levels);
        assert_eq!(pool.arena_mut(1).generation(), levels);
    }

    /// Test that arena exhaustion with fallback to heap still produces
    /// correct results in a BFS-like scenario.
    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_arena_exhaustion_fallback_bfs_scenario() {
        let state_len = 4;
        // Tiny arena: only fits 5 states.
        let mut pool = super::ArenaPool::new(1, state_len * 5);
        let mut all_states: Vec<Vec<i64>> = Vec::new();

        // Try to allocate 10 states — first 5 from arena, next 5 from heap.
        for i in 0..10 {
            match pool.arena_mut(0).try_alloc_state(state_len) {
                Some(slot) => {
                    for (j, val) in slot.iter_mut().enumerate() {
                        *val = (i * 10 + j) as i64;
                    }
                    // Promote to heap (simulating dedup pass for new state).
                    all_states.push(slot.to_vec());
                }
                None => {
                    // Fallback: heap allocation.
                    pool.record_fallback();
                    let mut heap_state = vec![0i64; state_len];
                    for (j, val) in heap_state.iter_mut().enumerate() {
                        *val = (i * 10 + j) as i64;
                    }
                    all_states.push(heap_state);
                }
            }
        }

        // Verify all 10 states are correct regardless of allocation source.
        assert_eq!(all_states.len(), 10);
        for i in 0..10 {
            for j in 0..state_len {
                assert_eq!(
                    all_states[i][j],
                    (i * 10 + j) as i64,
                    "state {i}, var {j}"
                );
            }
        }

        // 5 fallbacks should have been recorded.
        assert_eq!(pool.fallback_count(), 5);
    }

    /// Test per-worker arena isolation in ArenaPool.
    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_arena_pool_per_worker_isolation() {
        let mut pool = super::ArenaPool::new(4, 100);

        // Each worker allocates different-sized states.
        let w0 = pool.arena_mut(0).alloc_state(5);
        w0.copy_from_slice(&[10, 20, 30, 40, 50]);

        let w1 = pool.arena_mut(1).alloc_state(3);
        w1.copy_from_slice(&[100, 200, 300]);

        let w2 = pool.arena_mut(2).alloc_state(7);
        w2.copy_from_slice(&[1, 2, 3, 4, 5, 6, 7]);

        // Worker 3 doesn't allocate anything.
        assert_eq!(pool.arena_mut(3).used_words(), 0);

        // Verify isolation: each worker's data is independent.
        assert_eq!(pool.arena_mut(0).used_words(), 5);
        assert_eq!(pool.arena_mut(1).used_words(), 3);
        assert_eq!(pool.arena_mut(2).used_words(), 7);
        assert_eq!(pool.total_used_words(), 15);

        // Reset only worker 1's arena.
        pool.arena_mut(1).reset();
        assert_eq!(pool.arena_mut(1).used_words(), 0);
        assert_eq!(pool.arena_mut(1).generation(), 1);

        // Workers 0 and 2 are unaffected.
        assert_eq!(pool.arena_mut(0).used_words(), 5);
        assert_eq!(pool.arena_mut(2).used_words(), 7);
    }

    /// Test ScratchBuffer + WorkerArena integration pattern:
    /// assemble state in scratch, then copy to arena.
    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_scratch_buffer_to_arena_pattern() {
        let mut scratch = ScratchBuffer::new(4);
        let mut arena = WorkerArena::new(100);

        // Simulate 10 successor generations: assemble in scratch, copy to arena.
        for i in 0..10 {
            let buf = scratch.as_mut_slice();
            buf[0] = i * 100;
            buf[1] = i * 100 + 1;
            buf[2] = i * 100 + 2;
            buf[3] = i * 100 + 3;

            let slot = arena.alloc_state(4);
            slot.copy_from_slice(scratch.as_slice());
        }

        assert_eq!(arena.used_words(), 40);

        // Reset and reuse.
        arena.reset();
        assert_eq!(arena.used_words(), 0);

        // Scratch buffer is independent of arena — still usable.
        scratch.as_mut_slice().copy_from_slice(&[77, 88, 99, 11]);
        assert_eq!(scratch.as_slice(), &[77, 88, 99, 11]);
    }
}
