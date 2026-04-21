// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lock-free 128-bit fingerprint set for parallel model checking.
//!
//! [`AtomicFpSet`] is an open-addressed hash table storing 128-bit fingerprints
//! using paired `AtomicU64` slots with compare-and-swap insertion. This provides
//! collision resistance far beyond 64-bit fingerprints: the Birthday Paradox
//! threshold for 128-bit is ~1.8 * 10^19, vs ~4.2 * 10^9 for 64-bit.
//!
//! At 100M states/sec, a 64-bit set hits 50% collision probability in under a
//! minute. 128-bit fingerprints make collisions astronomically unlikely for any
//! feasible state space.
//!
//! ## Slot Layout
//!
//! Each slot consists of three atomics: `state: AtomicU8`, `high: AtomicU64`,
//! `low: AtomicU64`. The state field tracks the slot lifecycle:
//!
//! - `SLOT_EMPTY (0)`: slot is available for claiming.
//! - `SLOT_WRITING (1)`: a writer has claimed this slot and is writing the
//!   128-bit value. Readers must spin until the state advances to COMMITTED.
//! - `SLOT_COMMITTED (2)`: the (high, low) pair is fully written and readable.
//!
//! The high and low fields store the fingerprint's upper and lower 64 bits
//! directly. No encoding is needed since the state field distinguishes empty
//! from occupied slots.
//!
//! ## Insertion Protocol
//!
//! 1. CAS `state[i]` from `EMPTY` to `WRITING`. This claims the slot.
//! 2. Store `high[i]` with Relaxed ordering.
//! 3. Store `low[i]` with Relaxed ordering.
//! 4. Store `state[i]` with Release ordering, setting it to `COMMITTED`.
//!
//! Readers who see `WRITING` spin briefly until the state becomes `COMMITTED`,
//! then read both halves.
//!
//! **Correctness argument:**
//! - `state` transitions monotonically: `EMPTY -> WRITING -> COMMITTED`.
//! - No slot is ever freed or reused (insert-only set), so no ABA problem.
//! - Steps 2-3 are invisible to readers (they check state first).
//! - Step 4's Release ordering ensures steps 2-3 are visible to any thread
//!   that observes COMMITTED via Acquire.
//!
//! ## Zero Fingerprint
//!
//! The 128-bit value `0` is tracked via a dedicated `has_zero` atomic flag
//! rather than in the table. This avoids the ambiguity of (hi=0, lo=0) in
//! the table (which could appear as a "not yet written" slot).
//!
//! Part of #3991.

use std::sync::atomic::{AtomicBool, AtomicU64, AtomicU8, AtomicUsize, Ordering};
use std::sync::RwLock;

/// Result of an `insert_if_absent` operation.
///
/// Tri-state to distinguish "already present" from "table overfull" — both are
/// reasons not to explore a successor, but "table overfull" is a correctness
/// hazard (silent state-space truncation) that callers must handle explicitly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InsertResult {
    /// Fingerprint was newly inserted into the table.
    Inserted,
    /// Fingerprint was already present — safe to skip.
    AlreadyPresent,
    /// Linear probe chain exceeded [`MAX_PROBE`] — table is overfull.
    ///
    /// Callers MUST treat this as an error (halt model checking with a clear
    /// diagnostic) rather than silently skipping the state.
    ProbeLimitHit,
}

/// Maximum linear probes before declaring the table overfull.
const MAX_PROBE: usize = 1024;

/// Maximum spin iterations waiting for a writer to commit.
const MAX_SPIN: usize = 4096;

/// Slot state: empty, available for claiming.
const SLOT_EMPTY: u8 = 0;
/// Slot state: a writer has claimed it and is writing high/low.
const SLOT_WRITING: u8 = 1;
/// Slot state: high/low are fully written and readable.
const SLOT_COMMITTED: u8 = 2;

/// A lock-free open-addressing hash set for 128-bit fingerprints.
///
/// Pre-allocates three parallel arrays: per-slot state flags, high halves,
/// and low halves. Capacity is always a power of two. Size to ~2x the
/// expected number of entries for good probe-length distribution.
///
/// # Thread Safety
///
/// Writers are lock-free. Readers encountering a concurrent write perform
/// bounded spinning (at most [`MAX_SPIN`] iterations with `spin_loop` hints).
/// Multiple threads may insert and query concurrently without external
/// synchronization.
pub(crate) struct AtomicFpSet {
    /// Per-slot state: EMPTY, WRITING, or COMMITTED.
    state: Box<[AtomicU8]>,
    /// High 64 bits of each slot. Valid only when state == COMMITTED.
    high: Box<[AtomicU64]>,
    /// Low 64 bits of each slot. Valid only when state == COMMITTED.
    low: Box<[AtomicU64]>,
    /// Number of distinct fingerprints inserted.
    count: AtomicUsize,
    /// Whether the zero fingerprint (0u128) has been inserted.
    has_zero: AtomicBool,
    /// Bitmask for index computation: capacity - 1.
    mask: usize,
    // --- Advisory probe-chain observability counters (Part of #3991) ---
    /// The longest probe chain observed across all insert attempts.
    max_probe_len: AtomicUsize,
    /// Total probe steps across all insert/contains attempts.
    total_probes: AtomicU64,
    /// Total number of insert attempts (including duplicates).
    total_inserts: AtomicU64,
}

impl AtomicFpSet {
    /// Create a new atomic fingerprint set with the given capacity.
    ///
    /// Capacity is rounded up to the next power of two. For good performance,
    /// pass ~2x the expected number of entries.
    ///
    /// # Panics
    ///
    /// Panics if `capacity` is 0.
    pub(crate) fn new(capacity: usize) -> Self {
        assert!(capacity > 0, "AtomicFpSet capacity must be > 0");
        let capacity = capacity.next_power_of_two();
        let state: Vec<AtomicU8> = (0..capacity).map(|_| AtomicU8::new(SLOT_EMPTY)).collect();
        let high: Vec<AtomicU64> = (0..capacity).map(|_| AtomicU64::new(0)).collect();
        let low: Vec<AtomicU64> = (0..capacity).map(|_| AtomicU64::new(0)).collect();
        Self {
            state: state.into_boxed_slice(),
            high: high.into_boxed_slice(),
            low: low.into_boxed_slice(),
            count: AtomicUsize::new(0),
            has_zero: AtomicBool::new(false),
            mask: capacity - 1,
            max_probe_len: AtomicUsize::new(0),
            total_probes: AtomicU64::new(0),
            total_inserts: AtomicU64::new(0),
        }
    }

    /// Split a 128-bit fingerprint into (high, low) halves.
    #[inline]
    fn split(fp: u128) -> (u64, u64) {
        ((fp >> 64) as u64, fp as u64)
    }

    /// Compute the starting probe index from a 128-bit fingerprint.
    ///
    /// Mixes both halves for good distribution across the table.
    #[inline]
    fn probe_start(&self, fp: u128) -> usize {
        let lo = fp as u64;
        let hi = (fp >> 64) as u64;
        // Fibonacci hashing mix for good distribution.
        let mixed = lo.wrapping_add(hi.wrapping_mul(0x9E3779B97F4A7C15));
        (mixed as usize) & self.mask
    }

    // --- Advisory probe-chain observability (Part of #3991) ---

    /// Record probe chain length for observability.
    #[inline]
    fn record_probe_stats(&self, probe_len: usize) {
        self.total_probes
            .fetch_add(probe_len as u64, Ordering::Relaxed);
        if probe_len > self.max_probe_len.load(Ordering::Relaxed) {
            let _ = self.max_probe_len.fetch_max(probe_len, Ordering::Relaxed);
        }
    }

    /// The longest probe chain observed across all insert attempts.
    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn max_probe_len(&self) -> usize {
        self.max_probe_len.load(Ordering::Relaxed)
    }

    /// Average probe chain length across all insert attempts.
    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn avg_probe_len(&self) -> f64 {
        let total_inserts = self.total_inserts.load(Ordering::Relaxed);
        if total_inserts == 0 {
            0.0
        } else {
            self.total_probes.load(Ordering::Relaxed) as f64 / total_inserts as f64
        }
    }

    /// Total number of insert attempts (including duplicates).
    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn total_inserts(&self) -> u64 {
        self.total_inserts.load(Ordering::Relaxed)
    }

    // --- Collection (Part of #3991) ---

    /// Collect all fingerprints stored in this table.
    ///
    /// Walks all committed slots and returns their 128-bit values.
    /// Not linearizable with concurrent insertions: callers should ensure
    /// no concurrent writers or accept a snapshot that may miss in-flight inserts.
    #[must_use]
    pub(crate) fn collect_all(&self) -> Vec<u128> {
        let mut result = Vec::with_capacity(self.count.load(Ordering::Acquire));
        if self.has_zero.load(Ordering::Acquire) {
            result.push(0u128);
        }
        for idx in 0..self.state.len() {
            if self.state[idx].load(Ordering::Acquire) == SLOT_COMMITTED {
                let hi = self.high[idx].load(Ordering::Relaxed);
                let lo = self.low[idx].load(Ordering::Relaxed);
                result.push(((hi as u128) << 64) | (lo as u128));
            }
        }
        result
    }

    /// Insert a batch of fingerprints, returning the number of newly inserted entries.
    ///
    /// More efficient than calling [`insert_if_absent`] in a loop when callers
    /// have a pre-collected batch (e.g., successors from a BFS level). Each
    /// fingerprint is inserted independently (no transactional semantics).
    ///
    /// Fingerprints that were already present or that hit the probe limit are
    /// NOT counted. Callers should check the returned count against `fps.len()`
    /// if they need to detect probe-limit failures.
    pub(crate) fn insert_batch(&self, fps: &[u128]) -> usize {
        let mut inserted = 0usize;
        for &fp in fps {
            if self.insert_if_absent(fp) == InsertResult::Inserted {
                inserted += 1;
            }
        }
        inserted
    }

    /// Insert a 128-bit fingerprint if absent.
    ///
    /// Returns [`InsertResult::Inserted`] if the fingerprint was newly stored,
    /// [`InsertResult::AlreadyPresent`] if it was already in the set, or
    /// [`InsertResult::ProbeLimitHit`] if the linear probe chain exceeded
    /// [`MAX_PROBE`] (table is overfull — callers must treat this as an error).
    ///
    /// # Lock-Free Guarantee
    ///
    /// Writers are fully lock-free. The CAS loop makes progress on every
    /// iteration (either claiming a slot or advancing to the next probe).
    #[must_use]
    pub(crate) fn insert_if_absent(&self, fp: u128) -> InsertResult {
        self.total_inserts.fetch_add(1, Ordering::Relaxed);

        // Handle the zero fingerprint via side channel.
        if fp == 0 {
            let was_absent = self
                .has_zero
                .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
                .is_ok();
            self.record_probe_stats(1);
            if was_absent {
                self.count.fetch_add(1, Ordering::Relaxed);
                return InsertResult::Inserted;
            }
            return InsertResult::AlreadyPresent;
        }

        let (fp_hi, fp_lo) = Self::split(fp);
        let start = self.probe_start(fp);

        for probe in 0..MAX_PROBE {
            let probe_len = probe + 1;
            let idx = (start + probe) & self.mask;

            let slot_state = self.state[idx].load(Ordering::Acquire);

            match slot_state {
                SLOT_EMPTY => {
                    // Attempt to claim this slot.
                    match self.state[idx].compare_exchange_weak(
                        SLOT_EMPTY,
                        SLOT_WRITING,
                        Ordering::AcqRel,
                        Ordering::Acquire,
                    ) {
                        Ok(_) => {
                            // Slot claimed. Write the fingerprint, then commit.
                            self.high[idx].store(fp_hi, Ordering::Relaxed);
                            self.low[idx].store(fp_lo, Ordering::Relaxed);
                            self.state[idx].store(SLOT_COMMITTED, Ordering::Release);
                            self.count.fetch_add(1, Ordering::Relaxed);
                            self.record_probe_stats(probe_len);
                            return InsertResult::Inserted;
                        }
                        Err(actual) => {
                            // Someone else claimed it. Check what they wrote.
                            if actual == SLOT_WRITING {
                                if self.spin_and_check(idx, fp_hi, fp_lo) {
                                    self.record_probe_stats(probe_len);
                                    return InsertResult::AlreadyPresent;
                                }
                            } else if actual == SLOT_COMMITTED {
                                if self.read_committed_matches(idx, fp_hi, fp_lo) {
                                    self.record_probe_stats(probe_len);
                                    return InsertResult::AlreadyPresent;
                                }
                            }
                            // Different fingerprint, continue probing.
                            continue;
                        }
                    }
                }
                SLOT_WRITING => {
                    // Slot is being written by another thread.
                    if self.spin_and_check(idx, fp_hi, fp_lo) {
                        self.record_probe_stats(probe_len);
                        return InsertResult::AlreadyPresent;
                    }
                    // Different fingerprint, continue probing.
                }
                SLOT_COMMITTED => {
                    // Slot is committed. Compare directly.
                    if self.read_committed_matches(idx, fp_hi, fp_lo) {
                        self.record_probe_stats(probe_len);
                        return InsertResult::AlreadyPresent;
                    }
                    // Different fingerprint, continue probing.
                }
                _ => {
                    // Unknown state — should never happen.
                    debug_assert!(
                        false,
                        "AtomicFpSet: unknown slot state {slot_state} at index {idx}"
                    );
                }
            }
        }

        // Probe limit exceeded. Table is overfull — callers MUST handle this
        // as an error rather than silently skipping the state.
        self.record_probe_stats(MAX_PROBE);
        InsertResult::ProbeLimitHit
    }

    /// Spin-wait for a WRITING slot to become COMMITTED, then check if it
    /// matches the target fingerprint.
    ///
    /// In pathological cases (stuck writer threads), `contains` could spin for
    /// up to `MAX_PROBE * MAX_SPIN` = 4M iterations (~20ms at ~5ns/iteration).
    /// This is bounded and self-healing: once the writer commits, subsequent
    /// probes proceed without spinning.
    #[inline]
    fn spin_and_check(&self, idx: usize, target_hi: u64, target_lo: u64) -> bool {
        for _ in 0..MAX_SPIN {
            std::hint::spin_loop();
            let s = self.state[idx].load(Ordering::Acquire);
            if s == SLOT_COMMITTED {
                return self.read_committed_matches(idx, target_hi, target_lo);
            }
            // SLOT_EMPTY should not happen (WRITING -> EMPTY is invalid), but
            // handle defensively.
            if s != SLOT_WRITING {
                return false;
            }
        }
        // Writer is very slow. Conservatively treat as non-matching.
        false
    }

    /// Read a COMMITTED slot and compare against the target fingerprint.
    ///
    /// **Precondition:** The caller must have observed `state[idx] == COMMITTED`
    /// with Acquire ordering before calling this method. The Acquire on the
    /// state load synchronizes-with the Release store by the writer, ensuring
    /// the Relaxed loads of high/low see the writer's values.
    #[inline]
    fn read_committed_matches(&self, idx: usize, target_hi: u64, target_lo: u64) -> bool {
        let hi = self.high[idx].load(Ordering::Relaxed);
        let lo = self.low[idx].load(Ordering::Relaxed);
        hi == target_hi && lo == target_lo
    }

    /// Number of distinct fingerprints in the set.
    pub(crate) fn len(&self) -> usize {
        self.count.load(Ordering::Acquire)
    }

    /// Check if the set is empty.
    #[allow(dead_code)]
    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Check if a 128-bit fingerprint is present.
    pub(crate) fn contains(&self, fp: u128) -> bool {
        if fp == 0 {
            return self.has_zero.load(Ordering::Acquire);
        }

        let (fp_hi, fp_lo) = Self::split(fp);
        let start = self.probe_start(fp);

        for probe in 0..MAX_PROBE {
            let idx = (start + probe) & self.mask;
            let slot_state = self.state[idx].load(Ordering::Acquire);

            match slot_state {
                SLOT_EMPTY => return false,
                SLOT_WRITING => {
                    if self.spin_and_check(idx, fp_hi, fp_lo) {
                        return true;
                    }
                }
                SLOT_COMMITTED => {
                    if self.read_committed_matches(idx, fp_hi, fp_lo) {
                        return true;
                    }
                }
                _ => {
                    debug_assert!(
                        false,
                        "AtomicFpSet: unknown slot state {slot_state} at index {idx}"
                    );
                }
            }
        }

        false
    }

    /// Memory bytes used by the table arrays.
    #[allow(dead_code)]
    pub(crate) fn memory_bytes(&self) -> usize {
        self.state.len() * std::mem::size_of::<AtomicU8>()
            + self.high.len() * std::mem::size_of::<AtomicU64>()
            + self.low.len() * std::mem::size_of::<AtomicU64>()
    }

    /// Table capacity (number of slots).
    #[allow(dead_code)]
    pub(crate) fn capacity(&self) -> usize {
        self.state.len()
    }
}

// ---------------------------------------------------------------------------
// ResizableAtomicFpSet — wrapper with automatic resize on high load
// ---------------------------------------------------------------------------

/// Default load factor threshold that triggers resize.
const RESIZE_LOAD_FACTOR: f64 = 0.75;

/// Cumulative probe-chain statistics across all resize generations.
///
/// Unlike the per-table stats on [`AtomicFpSet`], which are reset on each
/// resize, this struct accumulates statistics across the entire lifetime of
/// a [`ResizableAtomicFpSet`] so callers see full observability data.
#[derive(Debug, Clone, Copy)]
pub(crate) struct CumulativeProbeStats {
    /// The longest probe chain observed across ALL tables (all resize generations).
    pub(crate) max_probe_len: usize,
    /// Average probe length across ALL insert attempts (all resize generations).
    pub(crate) avg_probe_len: f64,
    /// Total number of insert attempts across ALL tables (includes rehash inserts).
    pub(crate) total_inserts: u64,
    /// Number of resize operations performed.
    pub(crate) resize_count: usize,
}

/// A resizable wrapper around [`AtomicFpSet`].
///
/// Normal operations (insert, contains) take the `RwLock` in shared/read mode —
/// uncontended on modern hardware. When the load factor exceeds
/// [`RESIZE_LOAD_FACTOR`] (75%) or a probe-limit is hit, the inserting thread
/// upgrades to an exclusive/write lock, allocates a 2x table, rehashes all
/// committed entries, and swaps the inner set.
///
/// # Thread Safety
///
/// Wrap in `Arc` for multi-threaded use. The `RwLock` ensures resize is
/// mutually exclusive with all other operations.
///
/// Fixes #4009.
pub(crate) struct ResizableAtomicFpSet {
    inner: RwLock<AtomicFpSet>,
    /// Cumulative probe statistics across all resize generations.
    cumulative_max_probe_len: AtomicUsize,
    cumulative_total_probes: AtomicU64,
    cumulative_total_inserts: AtomicU64,
    /// Number of resize operations performed.
    resize_count: AtomicUsize,
}

impl ResizableAtomicFpSet {
    /// Create a new resizable fingerprint set with the given initial capacity.
    ///
    /// Capacity is rounded up to the next power of two (delegated to
    /// [`AtomicFpSet::new`]).
    #[must_use]
    pub(crate) fn new(capacity: usize) -> Self {
        Self {
            inner: RwLock::new(AtomicFpSet::new(capacity)),
            cumulative_max_probe_len: AtomicUsize::new(0),
            cumulative_total_probes: AtomicU64::new(0),
            cumulative_total_inserts: AtomicU64::new(0),
            resize_count: AtomicUsize::new(0),
        }
    }

    /// Insert a 128-bit fingerprint if absent.
    ///
    /// This method **never** returns [`InsertResult::ProbeLimitHit`]. If the
    /// underlying table is overfull, it resizes automatically and retries.
    #[must_use]
    pub(crate) fn insert_if_absent(&self, fp: u128) -> InsertResult {
        // Fast path: read lock (uncontended).
        let (result, observed_capacity) = {
            let inner = self
                .inner
                .read()
                .expect("ResizableAtomicFpSet: read lock poisoned");
            let result = inner.insert_if_absent(fp);
            let should_resize = result == InsertResult::ProbeLimitHit
                || Self::load_factor_of(&inner) >= RESIZE_LOAD_FACTOR;

            if !should_resize {
                return result;
            }
            (result, inner.capacity())
        };
        // Read lock is dropped here before acquiring write lock.

        // Slow path: write lock for resize.
        let mut inner = self
            .inner
            .write()
            .expect("ResizableAtomicFpSet: write lock poisoned");

        match result {
            InsertResult::Inserted | InsertResult::AlreadyPresent => {
                // The insert succeeded but load factor was high. Resize now so
                // future inserts don't hit the probe limit.
                if Self::load_factor_of(&inner) >= RESIZE_LOAD_FACTOR {
                    self.resize_locked(&mut inner);
                }
                result
            }
            InsertResult::ProbeLimitHit => {
                // Double-check: another thread may have resized between our
                // read-lock drop and write-lock acquire.
                if inner.capacity() == observed_capacity
                    || Self::load_factor_of(&inner) >= RESIZE_LOAD_FACTOR
                {
                    self.resize_locked(&mut inner);
                }

                let retry = inner.insert_if_absent(fp);
                if retry == InsertResult::ProbeLimitHit {
                    panic!(
                        "ResizableAtomicFpSet: insert_if_absent({fp:#034x}) returned \
                         ProbeLimitHit after resize (capacity={})",
                        inner.capacity()
                    );
                }
                retry
            }
        }
    }

    /// Insert a batch of fingerprints, returning the number of newly inserted entries.
    ///
    /// Delegates to [`insert_if_absent`] per element, handling resizes
    /// automatically. Never returns [`InsertResult::ProbeLimitHit`].
    pub(crate) fn insert_batch(&self, fps: &[u128]) -> usize {
        let mut inserted = 0usize;
        for &fp in fps {
            if self.insert_if_absent(fp) == InsertResult::Inserted {
                inserted += 1;
            }
        }
        inserted
    }

    /// Check if a 128-bit fingerprint is present.
    #[must_use]
    pub(crate) fn contains(&self, fp: u128) -> bool {
        self.inner
            .read()
            .expect("ResizableAtomicFpSet: read lock poisoned")
            .contains(fp)
    }

    /// Number of distinct fingerprints in the set.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.inner
            .read()
            .expect("ResizableAtomicFpSet: read lock poisoned")
            .len()
    }

    /// Current load factor (len / capacity).
    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn load_factor(&self) -> f64 {
        let inner = self
            .inner
            .read()
            .expect("ResizableAtomicFpSet: read lock poisoned");
        Self::load_factor_of(&inner)
    }

    /// Table capacity (number of slots in the current inner table).
    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn capacity(&self) -> usize {
        self.inner
            .read()
            .expect("ResizableAtomicFpSet: read lock poisoned")
            .capacity()
    }

    /// Memory bytes used by the current inner table.
    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn memory_bytes(&self) -> usize {
        self.inner
            .read()
            .expect("ResizableAtomicFpSet: read lock poisoned")
            .memory_bytes()
    }

    // --- Advisory probe-chain observability (Part of #3991) ---

    /// The longest probe chain observed across all insert attempts.
    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn max_probe_len(&self) -> usize {
        self.inner
            .read()
            .expect("ResizableAtomicFpSet: read lock poisoned")
            .max_probe_len()
    }

    /// Average probe chain length across all insert attempts.
    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn avg_probe_len(&self) -> f64 {
        self.inner
            .read()
            .expect("ResizableAtomicFpSet: read lock poisoned")
            .avg_probe_len()
    }

    /// Cumulative probe-chain statistics across all resize generations.
    ///
    /// Includes stats from the current inner table plus all prior tables
    /// that were replaced during resize. This gives a lifetime view of
    /// probe chain behavior.
    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn cumulative_probe_stats(&self) -> CumulativeProbeStats {
        let inner = self
            .inner
            .read()
            .expect("ResizableAtomicFpSet: read lock poisoned");
        let cur_max = inner.max_probe_len();
        let cur_probes = inner.total_probes.load(Ordering::Relaxed);
        let cur_inserts = inner.total_inserts.load(Ordering::Relaxed);

        let cum_max = self.cumulative_max_probe_len.load(Ordering::Relaxed);
        let cum_probes = self.cumulative_total_probes.load(Ordering::Relaxed);
        let cum_inserts = self.cumulative_total_inserts.load(Ordering::Relaxed);

        let total_max = cur_max.max(cum_max);
        let total_probes = cur_probes + cum_probes;
        let total_inserts = cur_inserts + cum_inserts;
        let avg = if total_inserts == 0 {
            0.0
        } else {
            total_probes as f64 / total_inserts as f64
        };

        CumulativeProbeStats {
            max_probe_len: total_max,
            avg_probe_len: avg,
            total_inserts,
            resize_count: self.resize_count.load(Ordering::Relaxed),
        }
    }

    /// Number of resize operations performed.
    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn resize_count(&self) -> usize {
        self.resize_count.load(Ordering::Relaxed)
    }

    // --- Collection (Part of #3991) ---

    /// Collect all fingerprints stored in the current inner table.
    ///
    /// Takes the read lock briefly. Not linearizable with concurrent resize
    /// operations, but safe: a concurrent resize rehashes all entries into the
    /// new table, so the read lock sees a consistent snapshot.
    #[must_use]
    pub(crate) fn collect_all(&self) -> Vec<u128> {
        self.inner
            .read()
            .expect("ResizableAtomicFpSet: read lock poisoned")
            .collect_all()
    }

    /// Compute load factor from an already-locked inner set.
    #[inline]
    fn load_factor_of(inner: &AtomicFpSet) -> f64 {
        inner.len() as f64 / inner.capacity() as f64
    }

    /// Resize the inner table to 2x capacity, rehashing all committed entries.
    ///
    /// Accumulates probe stats from the old table into the cumulative counters
    /// before replacing it.
    ///
    /// **Precondition:** Caller holds the write lock on `inner`.
    fn resize_locked(&self, inner: &mut AtomicFpSet) {
        let old_capacity = inner.capacity();
        let new_capacity = old_capacity
            .checked_mul(2)
            .expect("ResizableAtomicFpSet: capacity overflow during resize");

        let old = std::mem::replace(inner, AtomicFpSet::new(new_capacity));

        // Accumulate probe stats from the old table before it is dropped.
        let old_max = old.max_probe_len.load(Ordering::Relaxed);
        let old_probes = old.total_probes.load(Ordering::Relaxed);
        let old_inserts = old.total_inserts.load(Ordering::Relaxed);
        let _ = self
            .cumulative_max_probe_len
            .fetch_max(old_max, Ordering::Relaxed);
        self.cumulative_total_probes
            .fetch_add(old_probes, Ordering::Relaxed);
        self.cumulative_total_inserts
            .fetch_add(old_inserts, Ordering::Relaxed);
        self.resize_count.fetch_add(1, Ordering::Relaxed);

        // Rehash the zero fingerprint if present.
        if old.has_zero.load(Ordering::Acquire) {
            match inner.insert_if_absent(0) {
                InsertResult::Inserted => {}
                InsertResult::AlreadyPresent => {
                    panic!("ResizableAtomicFpSet: duplicate zero fp during resize")
                }
                InsertResult::ProbeLimitHit => {
                    panic!(
                        "ResizableAtomicFpSet: ProbeLimitHit for zero during resize \
                         (capacity {old_capacity} -> {new_capacity})"
                    )
                }
            }
        }

        // Walk all committed slots in the old table and rehash into the new one.
        for idx in 0..old.state.len() {
            match old.state[idx].load(Ordering::Acquire) {
                SLOT_EMPTY => {}
                SLOT_COMMITTED => {
                    let hi = old.high[idx].load(Ordering::Relaxed);
                    let lo = old.low[idx].load(Ordering::Relaxed);
                    let fp = ((hi as u128) << 64) | (lo as u128);

                    match inner.insert_if_absent(fp) {
                        InsertResult::Inserted | InsertResult::AlreadyPresent => {}
                        InsertResult::ProbeLimitHit => {
                            panic!(
                                "ResizableAtomicFpSet: ProbeLimitHit during resize \
                                 rehash (capacity {old_capacity} -> {new_capacity})"
                            )
                        }
                    }
                }
                SLOT_WRITING => {
                    // Write lock is held, so no NEW writer should start. But a
                    // writer may have claimed the slot just before we acquired
                    // the write lock and not yet committed. Spin briefly.
                    for _ in 0..MAX_SPIN {
                        std::hint::spin_loop();
                        if old.state[idx].load(Ordering::Acquire) == SLOT_COMMITTED {
                            break;
                        }
                    }
                    let s = old.state[idx].load(Ordering::Acquire);
                    if s == SLOT_COMMITTED {
                        let hi = old.high[idx].load(Ordering::Relaxed);
                        let lo = old.low[idx].load(Ordering::Relaxed);
                        let fp = ((hi as u128) << 64) | (lo as u128);
                        match inner.insert_if_absent(fp) {
                            InsertResult::Inserted | InsertResult::AlreadyPresent => {}
                            InsertResult::ProbeLimitHit => {
                                panic!(
                                    "ResizableAtomicFpSet: ProbeLimitHit during \
                                     resize rehash of late-committed slot"
                                )
                            }
                        }
                    } else {
                        panic!(
                            "ResizableAtomicFpSet: slot {idx} stuck in WRITING \
                             state during resize (state={s})"
                        );
                    }
                }
                slot_state => {
                    debug_assert!(
                        false,
                        "ResizableAtomicFpSet: unknown slot state {slot_state} \
                         at index {idx}"
                    );
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;

    // ====================================================================
    // Basic single-threaded tests
    // ====================================================================

    #[test]
    fn test_atomic_fp_set_empty() {
        let set = AtomicFpSet::new(1024);
        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
        assert!(!set.contains(1));
        assert!(!set.contains(0));
    }

    #[test]
    fn test_atomic_fp_set_single_insert() {
        let set = AtomicFpSet::new(1024);
        let fp: u128 = 0xDEAD_BEEF_CAFE_BABE_1234_5678_9ABC_DEF0;

        assert_eq!(set.insert_if_absent(fp), InsertResult::Inserted);
        assert_eq!(set.len(), 1);
        assert!(set.contains(fp));
        assert!(!set.contains(fp.wrapping_add(1)));
    }

    #[test]
    fn test_atomic_fp_set_duplicate_insert() {
        let set = AtomicFpSet::new(1024);
        let fp: u128 = 0xAAAA_BBBB_CCCC_DDDD_1111_2222_3333_4444;

        assert_eq!(set.insert_if_absent(fp), InsertResult::Inserted);
        assert_eq!(set.insert_if_absent(fp), InsertResult::AlreadyPresent);
        assert_eq!(set.len(), 1);
        assert!(set.contains(fp));
    }

    #[test]
    fn test_atomic_fp_set_zero_fingerprint() {
        let set = AtomicFpSet::new(1024);

        assert!(!set.contains(0u128));
        assert_eq!(set.insert_if_absent(0u128), InsertResult::Inserted);
        assert!(set.contains(0u128));
        assert_eq!(set.insert_if_absent(0u128), InsertResult::AlreadyPresent);
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_atomic_fp_set_multiple_fingerprints() {
        let set = AtomicFpSet::new(4096);

        let fps: Vec<u128> = (1u128..=100)
            .map(|i| i.wrapping_mul(0x9E37_79B9_7F4A_7C15_1234_5678_9ABC_DEF0))
            .collect();

        for &fp in &fps {
            assert_eq!(
                set.insert_if_absent(fp),
                InsertResult::Inserted,
                "should insert fp={fp:#x}"
            );
        }
        assert_eq!(set.len(), 100);

        for &fp in &fps {
            assert!(set.contains(fp), "should contain fp={fp:#x}");
        }

        assert!(!set.contains(0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFFu128));
    }

    #[test]
    fn test_atomic_fp_set_low_half_zero() {
        let set = AtomicFpSet::new(1024);
        let fp1: u128 = 1u128 << 64; // hi=1, lo=0
        let fp2: u128 = 2u128 << 64; // hi=2, lo=0

        assert_eq!(set.insert_if_absent(fp1), InsertResult::Inserted);
        assert_eq!(set.insert_if_absent(fp2), InsertResult::Inserted);
        assert_eq!(set.len(), 2);
        assert!(set.contains(fp1));
        assert!(set.contains(fp2));
        assert_eq!(set.insert_if_absent(fp1), InsertResult::AlreadyPresent);
    }

    #[test]
    fn test_atomic_fp_set_high_half_zero() {
        let set = AtomicFpSet::new(1024);
        let fp1: u128 = 1; // hi=0, lo=1
        let fp2: u128 = 2; // hi=0, lo=2

        assert_eq!(set.insert_if_absent(fp1), InsertResult::Inserted);
        assert_eq!(set.insert_if_absent(fp2), InsertResult::Inserted);
        assert_eq!(set.len(), 2);
        assert!(set.contains(fp1));
        assert!(set.contains(fp2));
    }

    #[test]
    fn test_atomic_fp_set_same_high_different_low() {
        let set = AtomicFpSet::new(4096);
        let base_hi: u128 = 0x1234_5678_9ABC_DEF0u128 << 64;

        for lo in 0u64..50 {
            let fp = base_hi | (lo as u128);
            assert_eq!(
                set.insert_if_absent(fp),
                InsertResult::Inserted,
                "should insert lo={lo}"
            );
        }
        assert_eq!(set.len(), 50);

        for lo in 0u64..50 {
            let fp = base_hi | (lo as u128);
            assert!(set.contains(fp), "should contain lo={lo}");
        }
    }

    #[test]
    fn test_atomic_fp_set_max_u128() {
        let set = AtomicFpSet::new(1024);
        let fp = u128::MAX;

        assert_eq!(set.insert_if_absent(fp), InsertResult::Inserted);
        assert!(set.contains(fp));
        assert_eq!(set.insert_if_absent(fp), InsertResult::AlreadyPresent);
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_atomic_fp_set_all_bits_patterns() {
        let set = AtomicFpSet::new(4096);
        let patterns: Vec<u128> = vec![
            0,
            1,
            u128::MAX,
            u128::MAX - 1,
            1u128 << 64,
            (1u128 << 64) - 1,
            1u128 << 127,
            (1u128 << 63) << 64,
            0xFFFF_FFFF_FFFF_FFFF,
            0xFFFF_FFFF_FFFF_FFFF_0000_0000_0000_0000,
        ];

        for &fp in &patterns {
            let _ = set.insert_if_absent(fp);
        }

        for &fp in &patterns {
            assert!(set.contains(fp), "should contain pattern fp={fp:#034x}");
        }
    }

    #[test]
    fn test_atomic_fp_set_capacity_rounding() {
        let set = AtomicFpSet::new(100);
        assert_eq!(set.capacity(), 128);
    }

    #[test]
    fn test_atomic_fp_set_memory_bytes() {
        let set = AtomicFpSet::new(1024);
        let expected = 1024
            * (std::mem::size_of::<AtomicU8>()
                + std::mem::size_of::<AtomicU64>()
                + std::mem::size_of::<AtomicU64>());
        assert_eq!(set.memory_bytes(), expected);
    }

    // ====================================================================
    // Stress tests: high load factor
    // ====================================================================

    #[test]
    fn test_atomic_fp_set_high_load_factor() {
        let capacity = 8192;
        let set = AtomicFpSet::new(capacity);
        let n = capacity / 2;

        for i in 1u128..=(n as u128) {
            let fp = i.wrapping_mul(0x517C_C1B7_2722_0A95_6A09_E667_F3BC_C908);
            assert_eq!(
                set.insert_if_absent(fp),
                InsertResult::Inserted,
                "should insert i={i}"
            );
        }
        assert_eq!(set.len(), n);

        for i in 1u128..=(n as u128) {
            let fp = i.wrapping_mul(0x517C_C1B7_2722_0A95_6A09_E667_F3BC_C908);
            assert!(set.contains(fp), "should contain i={i}");
        }
    }

    // ====================================================================
    // Concurrent tests (16 threads)
    // ====================================================================

    #[test]
    fn test_atomic_fp_set_concurrent_disjoint_inserts() {
        let set = Arc::new(AtomicFpSet::new(1 << 18));
        let num_threads = 16;
        let fps_per_thread = 1000;

        let handles: Vec<_> = (0..num_threads)
            .map(|t| {
                let set = Arc::clone(&set);
                thread::spawn(move || {
                    let mut inserted = 0usize;
                    for i in 0..fps_per_thread {
                        let raw = (t as u128) * 1_000_000 + i as u128 + 1;
                        let fp = raw.wrapping_mul(0x9E37_79B9_7F4A_7C15_6A09_E667_F3BC_C908);
                        if set.insert_if_absent(fp) == InsertResult::Inserted {
                            inserted += 1;
                        }
                    }
                    inserted
                })
            })
            .collect();

        let total_inserted: usize = handles.into_iter().map(|h| h.join().unwrap()).sum();
        assert_eq!(total_inserted, num_threads * fps_per_thread);
        assert_eq!(set.len(), num_threads * fps_per_thread);
    }

    #[test]
    fn test_atomic_fp_set_concurrent_duplicate_inserts() {
        let set = Arc::new(AtomicFpSet::new(1024));
        let fp: u128 = 0xCAFE_BABE_DEAD_BEEF_1234_5678_9ABC_DEF0;
        let num_threads = 16;

        let handles: Vec<_> = (0..num_threads)
            .map(|_| {
                let set = Arc::clone(&set);
                thread::spawn(move || set.insert_if_absent(fp))
            })
            .collect();

        let results: Vec<InsertResult> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        let inserted_count = results
            .iter()
            .filter(|&&r| r == InsertResult::Inserted)
            .count();

        assert_eq!(inserted_count, 1, "exactly one thread should succeed");
        assert_eq!(set.len(), 1);
        assert!(set.contains(fp));
    }

    #[test]
    fn test_atomic_fp_set_concurrent_mixed_workload() {
        let set = Arc::new(AtomicFpSet::new(1 << 18));
        let num_writers = 8;
        let num_readers = 8;
        let fps_per_writer = 1000;

        let all_fps: Vec<u128> = (1u128..=(num_writers as u128 * fps_per_writer as u128))
            .map(|i| i.wrapping_mul(0x517C_C1B7_2722_0A95_6A09_E667_F3BC_C908))
            .collect();

        let all_fps = Arc::new(all_fps);
        let barrier = Arc::new(std::sync::Barrier::new(num_writers + num_readers));

        let mut handles: Vec<_> = (0..num_writers)
            .map(|t| {
                let set = Arc::clone(&set);
                let fps = Arc::clone(&all_fps);
                let barrier = Arc::clone(&barrier);
                thread::spawn(move || {
                    barrier.wait();
                    let start = t * fps_per_writer;
                    let end = start + fps_per_writer;
                    for fp in &fps[start..end] {
                        let _ = set.insert_if_absent(*fp);
                    }
                })
            })
            .collect();

        let reader_handles: Vec<_> = (0..num_readers)
            .map(|_| {
                let set = Arc::clone(&set);
                let fps = Arc::clone(&all_fps);
                let barrier = Arc::clone(&barrier);
                thread::spawn(move || {
                    barrier.wait();
                    let mut queries = 0usize;
                    for _ in 0..5 {
                        for fp in fps.iter() {
                            let _ = set.contains(*fp);
                            queries += 1;
                        }
                    }
                    queries
                })
            })
            .collect();

        for h in handles.drain(..) {
            h.join().unwrap();
        }
        for h in reader_handles {
            let _queries = h.join().unwrap();
        }

        assert_eq!(set.len(), all_fps.len());
        for fp in all_fps.iter() {
            assert!(set.contains(*fp), "missing fp after all writers complete");
        }
    }

    #[test]
    fn test_atomic_fp_set_concurrent_zero_fingerprint() {
        let set = Arc::new(AtomicFpSet::new(1024));
        let num_threads = 16;

        let handles: Vec<_> = (0..num_threads)
            .map(|_| {
                let set = Arc::clone(&set);
                thread::spawn(move || set.insert_if_absent(0u128))
            })
            .collect();

        let results: Vec<InsertResult> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        let inserted_count = results
            .iter()
            .filter(|&&r| r == InsertResult::Inserted)
            .count();

        assert_eq!(inserted_count, 1);
        assert_eq!(set.len(), 1);
        assert!(set.contains(0u128));
    }

    #[test]
    fn test_atomic_fp_set_concurrent_high_contention() {
        let set = Arc::new(AtomicFpSet::new(1 << 18));
        let num_threads = 16;
        let fps_per_thread = 5000usize;
        let overlap = 2000;

        let handles: Vec<_> = (0..num_threads)
            .map(|t| {
                let set = Arc::clone(&set);
                thread::spawn(move || {
                    let mut inserted = 0usize;
                    for i in 0..fps_per_thread {
                        let raw = if i < overlap {
                            (i as u128) + 1
                        } else {
                            (t as u128) * 1_000_000 + (i as u128) + 1
                        };
                        let fp = raw.wrapping_mul(0x9E37_79B9_7F4A_7C15_6A09_E667_F3BC_C908);
                        if set.insert_if_absent(fp) == InsertResult::Inserted {
                            inserted += 1;
                        }
                    }
                    inserted
                })
            })
            .collect();

        let total_inserted: usize = handles.into_iter().map(|h| h.join().unwrap()).sum();

        let expected = overlap + num_threads * (fps_per_thread - overlap);
        assert_eq!(total_inserted, expected);
        assert_eq!(set.len(), expected);
    }

    // ====================================================================
    // Probe limit tests (#4009)
    // ====================================================================

    #[test]
    fn test_atomic_fp_set_probe_limit_returns_probe_limit_hit() {
        // Use a tiny table (capacity 16) and fill every slot with distinct
        // fingerprints that hash to the same bucket. Since all 16 slots will
        // be occupied, the 17th insert must exhaust the probe chain and
        // return ProbeLimitHit.
        //
        // We use capacity 16 which is << MAX_PROBE (1024), so the probe
        // chain wraps around the entire table before exhausting.
        let capacity = 16usize;
        let set = AtomicFpSet::new(capacity);

        // Fill the table completely with distinct non-zero fingerprints.
        let mut inserted = 0usize;
        let mut candidate = 1u128;
        while inserted < capacity {
            match set.insert_if_absent(candidate) {
                InsertResult::Inserted => inserted += 1,
                InsertResult::AlreadyPresent => {}
                InsertResult::ProbeLimitHit => {
                    panic!("unexpected ProbeLimitHit while filling table");
                }
            }
            candidate += 1;
        }
        assert_eq!(set.len(), capacity);

        // Now every slot is occupied. The next unique fingerprint must fail
        // because the probe chain will wrap the entire table without finding
        // an empty slot (capacity 16 < MAX_PROBE 1024, so the probe hits
        // every slot and then continues until MAX_PROBE is reached).
        // With capacity 16 and MAX_PROBE 1024, the probe visits all 16
        // slots many times before hitting the limit. As long as none match
        // the new fingerprint, we get ProbeLimitHit.
        let new_fp = candidate + 1_000_000; // Guaranteed distinct from 1..capacity+1
        let result = set.insert_if_absent(new_fp);
        assert_eq!(
            result,
            InsertResult::ProbeLimitHit,
            "insert into full table should return ProbeLimitHit, got {result:?}"
        );

        // Count should not have changed — ProbeLimitHit does not increment.
        assert_eq!(set.len(), capacity);
    }

    #[test]
    fn test_atomic_fp_set_probe_limit_not_confused_with_already_present() {
        // Verify that ProbeLimitHit is distinguishable from AlreadyPresent.
        let capacity = 16usize;
        let set = AtomicFpSet::new(capacity);

        // Fill the table.
        for i in 1u128..=(capacity as u128) {
            assert_eq!(set.insert_if_absent(i), InsertResult::Inserted);
        }

        // Re-inserting an existing fingerprint should still return AlreadyPresent
        // even when the table is full, because the probe chain finds the match
        // before exhausting MAX_PROBE.
        for i in 1u128..=(capacity as u128) {
            assert_eq!(
                set.insert_if_absent(i),
                InsertResult::AlreadyPresent,
                "re-insert of existing fp={i} should be AlreadyPresent"
            );
        }
    }

    #[test]
    fn test_atomic_fp_set_zero_fp_never_probe_limit() {
        // Zero fingerprint uses the side-channel flag, not the table.
        // Even a totally full table should handle zero correctly.
        let set = AtomicFpSet::new(16);

        // Fill the table.
        for i in 1u128..=16 {
            let _ = set.insert_if_absent(i);
        }

        // Zero should still work via the has_zero flag.
        assert_eq!(set.insert_if_absent(0u128), InsertResult::Inserted);
        assert_eq!(set.insert_if_absent(0u128), InsertResult::AlreadyPresent);
    }

    // ====================================================================
    // ResizableAtomicFpSet tests (#4009)
    // ====================================================================

    #[test]
    fn test_resizable_basic_insert_and_contains() {
        let set = ResizableAtomicFpSet::new(1024);
        let fp: u128 = 0xDEAD_BEEF_CAFE_BABE_1234_5678_9ABC_DEF0;

        assert_eq!(set.insert_if_absent(fp), InsertResult::Inserted);
        assert_eq!(set.len(), 1);
        assert!(set.contains(fp));
        assert!(!set.contains(fp.wrapping_add(1)));

        assert_eq!(set.insert_if_absent(fp), InsertResult::AlreadyPresent);
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_resizable_zero_fingerprint() {
        let set = ResizableAtomicFpSet::new(64);

        assert!(!set.contains(0u128));
        assert_eq!(set.insert_if_absent(0u128), InsertResult::Inserted);
        assert!(set.contains(0u128));
        assert_eq!(set.insert_if_absent(0u128), InsertResult::AlreadyPresent);
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_resizable_auto_resize_on_high_load() {
        // Start with a small table (capacity 64 after rounding). Insert
        // enough entries to exceed the 75% load factor and trigger resize.
        let set = ResizableAtomicFpSet::new(64);
        let initial_capacity = set.capacity();
        assert_eq!(initial_capacity, 64);

        // 75% of 64 = 48 entries triggers resize. Insert 60.
        let n = 60usize;
        for i in 1u128..=(n as u128) {
            let fp = i.wrapping_mul(0x9E37_79B9_7F4A_7C15_6A09_E667_F3BC_C908);
            let result = set.insert_if_absent(fp);
            assert_ne!(
                result,
                InsertResult::ProbeLimitHit,
                "ResizableAtomicFpSet should never return ProbeLimitHit"
            );
        }
        assert_eq!(set.len(), n);

        // Capacity should have grown.
        assert!(
            set.capacity() > initial_capacity,
            "capacity should have grown from {initial_capacity}, got {}",
            set.capacity()
        );

        // All fingerprints should still be retrievable after resize.
        for i in 1u128..=(n as u128) {
            let fp = i.wrapping_mul(0x9E37_79B9_7F4A_7C15_6A09_E667_F3BC_C908);
            assert!(set.contains(fp), "missing fp after resize, i={i}");
        }
    }

    #[test]
    fn test_resizable_fills_tiny_table_without_panic() {
        // Capacity 16 — fill it entirely. The resizable wrapper should
        // resize rather than returning ProbeLimitHit.
        let set = ResizableAtomicFpSet::new(16);
        let initial_capacity = set.capacity();

        for i in 1u128..=32 {
            let result = set.insert_if_absent(i);
            assert_ne!(
                result,
                InsertResult::ProbeLimitHit,
                "should never get ProbeLimitHit from resizable set, i={i}"
            );
        }
        assert_eq!(set.len(), 32);
        assert!(set.capacity() > initial_capacity);

        // Verify all entries.
        for i in 1u128..=32 {
            assert!(set.contains(i), "missing i={i} after fill+resize");
        }
    }

    #[test]
    fn test_resizable_preserves_zero_across_resize() {
        let set = ResizableAtomicFpSet::new(16);

        // Insert zero first.
        assert_eq!(set.insert_if_absent(0u128), InsertResult::Inserted);

        // Fill the table to trigger resize.
        for i in 1u128..=20 {
            let _ = set.insert_if_absent(i);
        }

        // Zero should survive the resize.
        assert!(set.contains(0u128));
        assert_eq!(set.insert_if_absent(0u128), InsertResult::AlreadyPresent);
    }

    #[test]
    fn test_resizable_multiple_resizes() {
        // Start very small and force multiple resizes.
        let set = ResizableAtomicFpSet::new(8);
        let initial_capacity = set.capacity();
        assert_eq!(initial_capacity, 8);

        // Insert 500 entries — should trigger multiple resizes.
        for i in 1u128..=500 {
            let fp = i.wrapping_mul(0x517C_C1B7_2722_0A95_6A09_E667_F3BC_C908);
            let result = set.insert_if_absent(fp);
            assert_ne!(result, InsertResult::ProbeLimitHit, "i={i}");
        }
        assert_eq!(set.len(), 500);

        // Capacity should be at least 1024 (8 -> 16 -> 32 -> 64 -> 128 ->
        // 256 -> 512 -> 1024, each resize at 75%).
        assert!(
            set.capacity() >= 512,
            "capacity should have grown through multiple resizes, got {}",
            set.capacity()
        );

        // Verify all entries.
        for i in 1u128..=500 {
            let fp = i.wrapping_mul(0x517C_C1B7_2722_0A95_6A09_E667_F3BC_C908);
            assert!(set.contains(fp), "missing after multiple resizes, i={i}");
        }
    }

    #[test]
    fn test_resizable_concurrent_inserts_with_resize() {
        let set = Arc::new(ResizableAtomicFpSet::new(64));
        let num_threads = 8;
        let fps_per_thread = 500;

        let handles: Vec<_> = (0..num_threads)
            .map(|t| {
                let set = Arc::clone(&set);
                thread::spawn(move || {
                    let mut inserted = 0usize;
                    for i in 0..fps_per_thread {
                        let raw = (t as u128) * 1_000_000 + i as u128 + 1;
                        let fp = raw.wrapping_mul(0x9E37_79B9_7F4A_7C15_6A09_E667_F3BC_C908);
                        match set.insert_if_absent(fp) {
                            InsertResult::Inserted => inserted += 1,
                            InsertResult::AlreadyPresent => {}
                            InsertResult::ProbeLimitHit => {
                                panic!("ProbeLimitHit in concurrent resize test");
                            }
                        }
                    }
                    inserted
                })
            })
            .collect();

        let total_inserted: usize = handles.into_iter().map(|h| h.join().unwrap()).sum();
        let expected = num_threads * fps_per_thread;
        assert_eq!(total_inserted, expected);
        assert_eq!(set.len(), expected);

        // Capacity should have grown from 64.
        assert!(
            set.capacity() > 64,
            "capacity should have grown, got {}",
            set.capacity()
        );
    }

    #[test]
    fn test_resizable_load_factor_decreases_after_resize() {
        let set = ResizableAtomicFpSet::new(64);

        // Insert 47 entries (73% of 64 — just under threshold).
        for i in 1u128..=47 {
            let fp = i.wrapping_mul(0x9E37_79B9_7F4A_7C15_6A09_E667_F3BC_C908);
            let _ = set.insert_if_absent(fp);
        }
        assert!(
            set.load_factor() < RESIZE_LOAD_FACTOR,
            "load factor should be under threshold before triggering resize"
        );

        // Insert one more to cross the 75% threshold (48/64 = 0.75).
        let fp48 = 48u128.wrapping_mul(0x9E37_79B9_7F4A_7C15_6A09_E667_F3BC_C908);
        let _ = set.insert_if_absent(fp48);

        // After resize, load factor should be well below threshold.
        assert!(
            set.load_factor() < 0.5,
            "load factor should be < 0.5 after resize, got {}",
            set.load_factor()
        );
        assert_eq!(set.capacity(), 128);
    }

    // ====================================================================
    // Probe chain stats tests (Part of #3991)
    // ====================================================================

    #[test]
    fn test_atomic_fp_set_probe_stats_initially_zero() {
        let set = AtomicFpSet::new(1024);
        assert_eq!(set.max_probe_len(), 0);
        assert_eq!(set.avg_probe_len(), 0.0);
        assert_eq!(set.total_inserts(), 0);
    }

    #[test]
    fn test_atomic_fp_set_probe_stats_after_inserts() {
        let set = AtomicFpSet::new(4096);

        for i in 1u128..=200 {
            let fp = i.wrapping_mul(0x9E37_79B9_7F4A_7C15_6A09_E667_F3BC_C908);
            let _ = set.insert_if_absent(fp);
        }

        // Every insert probes at least 1 slot.
        assert!(
            set.max_probe_len() >= 1,
            "max_probe_len should be >= 1 after inserts, got {}",
            set.max_probe_len()
        );

        let avg = set.avg_probe_len();
        assert!(
            (1.0..=MAX_PROBE as f64).contains(&avg),
            "avg_probe_len should be in [1.0, {MAX_PROBE}], got {avg}"
        );

        // At low load factor, avg should be close to 1.
        assert!(
            avg < 3.0,
            "avg_probe_len at 5% load should be < 3.0, got {avg}"
        );

        // total_inserts includes all 200 insert calls.
        assert_eq!(set.total_inserts(), 200);
    }

    #[test]
    fn test_atomic_fp_set_probe_stats_duplicates_counted() {
        let set = AtomicFpSet::new(1024);
        let fp = 42u128;

        let _ = set.insert_if_absent(fp);
        let _ = set.insert_if_absent(fp); // duplicate
        let _ = set.insert_if_absent(fp); // duplicate

        // All 3 attempts are counted.
        assert_eq!(set.total_inserts(), 3);
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_resizable_probe_stats() {
        let set = ResizableAtomicFpSet::new(64);

        for i in 1u128..=50 {
            let fp = i.wrapping_mul(0x517C_C1B7_2722_0A95_6A09_E667_F3BC_C908);
            let _ = set.insert_if_absent(fp);
        }

        // Note: stats reflect the CURRENT inner table, not cumulative across
        // resizes. After resize, old table stats are discarded.
        assert!(
            set.max_probe_len() >= 1,
            "resizable max_probe_len should be >= 1"
        );
        let avg = set.avg_probe_len();
        assert!(
            avg >= 1.0,
            "resizable avg_probe_len should be >= 1.0, got {avg}"
        );
    }

    // ====================================================================
    // collect_all tests (Part of #3991)
    // ====================================================================

    #[test]
    fn test_atomic_fp_set_collect_all_empty() {
        let set = AtomicFpSet::new(1024);
        let collected = set.collect_all();
        assert!(collected.is_empty());
    }

    #[test]
    fn test_atomic_fp_set_collect_all_basic() {
        let set = AtomicFpSet::new(4096);
        let fps: Vec<u128> = (1u128..=100)
            .map(|i| i.wrapping_mul(0x9E37_79B9_7F4A_7C15_1234_5678_9ABC_DEF0))
            .collect();

        for &fp in &fps {
            let _ = set.insert_if_absent(fp);
        }

        let collected: std::collections::HashSet<u128> =
            set.collect_all().into_iter().collect();
        assert_eq!(collected.len(), 100);
        for &fp in &fps {
            assert!(collected.contains(&fp), "missing fp={fp:#034x}");
        }
    }

    #[test]
    fn test_atomic_fp_set_collect_all_includes_zero() {
        let set = AtomicFpSet::new(1024);
        let _ = set.insert_if_absent(0u128);
        let _ = set.insert_if_absent(42u128);

        let collected: std::collections::HashSet<u128> =
            set.collect_all().into_iter().collect();
        assert!(collected.contains(&0u128));
        assert!(collected.contains(&42u128));
        assert_eq!(collected.len(), 2);
    }

    #[test]
    fn test_resizable_collect_all_basic() {
        let set = ResizableAtomicFpSet::new(16);

        for i in 1u128..=50 {
            let _ = set.insert_if_absent(i);
        }

        let collected: std::collections::HashSet<u128> =
            set.collect_all().into_iter().collect();
        assert_eq!(collected.len(), 50);
        for i in 1u128..=50 {
            assert!(collected.contains(&i), "missing i={i}");
        }
    }

    #[test]
    fn test_resizable_collect_all_includes_zero() {
        let set = ResizableAtomicFpSet::new(16);
        let _ = set.insert_if_absent(0u128);

        // Force resize past the zero insert.
        for i in 1u128..=20 {
            let _ = set.insert_if_absent(i);
        }

        let collected: std::collections::HashSet<u128> =
            set.collect_all().into_iter().collect();
        assert!(
            collected.contains(&0u128),
            "zero fingerprint should survive resize"
        );
        assert_eq!(collected.len(), 21);
    }

    // ====================================================================
    // Batch insert tests (Part of #3991 Phase 8)
    // ====================================================================

    #[test]
    fn test_atomic_fp_set_batch_insert_basic() {
        let set = AtomicFpSet::new(4096);
        let fps: Vec<u128> = (1u128..=50)
            .map(|i| i.wrapping_mul(0x9E37_79B9_7F4A_7C15_1234_5678_9ABC_DEF0))
            .collect();

        let inserted = set.insert_batch(&fps);
        assert_eq!(inserted, 50);
        assert_eq!(set.len(), 50);

        for &fp in &fps {
            assert!(set.contains(fp), "missing fp={fp:#034x}");
        }

        // Re-insert same batch — all should be duplicates.
        let reinserted = set.insert_batch(&fps);
        assert_eq!(reinserted, 0);
        assert_eq!(set.len(), 50);
    }

    #[test]
    fn test_atomic_fp_set_batch_insert_with_duplicates() {
        let set = AtomicFpSet::new(4096);
        // Batch with internal duplicates.
        let fps: Vec<u128> = vec![1, 2, 3, 1, 2, 3, 4, 5];
        let inserted = set.insert_batch(&fps);
        assert_eq!(inserted, 5);
        assert_eq!(set.len(), 5);
    }

    #[test]
    fn test_atomic_fp_set_batch_insert_empty() {
        let set = AtomicFpSet::new(1024);
        let inserted = set.insert_batch(&[]);
        assert_eq!(inserted, 0);
        assert_eq!(set.len(), 0);
    }

    #[test]
    fn test_resizable_batch_insert_triggers_resize() {
        let set = ResizableAtomicFpSet::new(16);
        let initial_capacity = set.capacity();

        let fps: Vec<u128> = (1u128..=30)
            .map(|i| i.wrapping_mul(0x517C_C1B7_2722_0A95_6A09_E667_F3BC_C908))
            .collect();

        let inserted = set.insert_batch(&fps);
        assert_eq!(inserted, 30);
        assert_eq!(set.len(), 30);
        assert!(
            set.capacity() > initial_capacity,
            "capacity should have grown from {initial_capacity}, got {}",
            set.capacity()
        );

        for &fp in &fps {
            assert!(set.contains(fp), "missing fp after resize");
        }
    }

    #[test]
    fn test_atomic_fp_set_batch_insert_concurrent() {
        let set = Arc::new(AtomicFpSet::new(1 << 18));
        let num_threads = 8;
        let fps_per_thread = 500;

        let handles: Vec<_> = (0..num_threads)
            .map(|t| {
                let set = Arc::clone(&set);
                thread::spawn(move || {
                    let fps: Vec<u128> = (0..fps_per_thread)
                        .map(|i| {
                            let raw = (t as u128) * 1_000_000 + i as u128 + 1;
                            raw.wrapping_mul(0x9E37_79B9_7F4A_7C15_6A09_E667_F3BC_C908)
                        })
                        .collect();
                    set.insert_batch(&fps)
                })
            })
            .collect();

        let total_inserted: usize = handles.into_iter().map(|h| h.join().unwrap()).sum();
        assert_eq!(total_inserted, num_threads * fps_per_thread);
        assert_eq!(set.len(), num_threads * fps_per_thread);
    }

    // ====================================================================
    // Cumulative probe stats tests (Part of #3991 Phase 8)
    // ====================================================================

    #[test]
    fn test_resizable_cumulative_stats_across_resizes() {
        let set = ResizableAtomicFpSet::new(16);

        // Insert enough to trigger multiple resizes (16 -> 32 -> 64 -> 128...).
        for i in 1u128..=100 {
            let fp = i.wrapping_mul(0x517C_C1B7_2722_0A95_6A09_E667_F3BC_C908);
            let _ = set.insert_if_absent(fp);
        }

        assert!(
            set.resize_count() > 0,
            "should have resized at least once, got {}",
            set.resize_count()
        );

        // Cumulative stats should reflect all inserts including rehash inserts.
        let stats = set.cumulative_probe_stats();
        assert!(
            stats.total_inserts >= 100,
            "cumulative inserts should be >= 100, got {}",
            stats.total_inserts
        );
        assert!(
            stats.max_probe_len >= 1,
            "cumulative max_probe_len should be >= 1"
        );
        assert!(
            stats.resize_count > 0,
            "resize_count should be > 0"
        );
    }

    #[test]
    fn test_resizable_cumulative_stats_no_resize() {
        let set = ResizableAtomicFpSet::new(4096);

        // Insert few entries — no resize should occur.
        for i in 1u128..=10 {
            let _ = set.insert_if_absent(i);
        }

        assert_eq!(set.resize_count(), 0);
        let stats = set.cumulative_probe_stats();
        assert_eq!(stats.resize_count, 0);
        assert_eq!(stats.total_inserts, 10);
    }

    // ====================================================================
    // Property-based test (Part of #3991)
    // ====================================================================

    mod proptest_atomic_fp_set {
        use super::*;
        use proptest::prelude::*;
        use std::collections::HashSet;

        proptest! {
            /// For any set of u128 values, AtomicFpSet tracks them correctly:
            /// every inserted value is found by contains(), no false positives
            /// for values never inserted, len() is exact, and collect_all()
            /// returns exactly the inserted set.
            #[test]
            fn test_atomic_fp_set_insert_contains_agreement(
                values in proptest::collection::vec(any::<u128>(), 0..200)
            ) {
                let set = AtomicFpSet::new(1024);
                let mut expected: HashSet<u128> = HashSet::new();

                for &v in &values {
                    let result = set.insert_if_absent(v);
                    if expected.insert(v) {
                        prop_assert_eq!(
                            result, InsertResult::Inserted,
                            "expected Inserted for new value {:034x}", v
                        );
                    } else {
                        prop_assert_eq!(
                            result, InsertResult::AlreadyPresent,
                            "expected AlreadyPresent for duplicate {:034x}", v
                        );
                    }
                }

                prop_assert_eq!(set.len(), expected.len());

                // All inserted values are findable.
                for &v in &expected {
                    prop_assert!(
                        set.contains(v),
                        "missing value {:034x}", v
                    );
                }

                // collect_all returns exactly the expected set.
                let collected: HashSet<u128> = set.collect_all().into_iter().collect();
                prop_assert_eq!(
                    collected, expected,
                    "collect_all mismatch"
                );
            }
        }
    }
}
