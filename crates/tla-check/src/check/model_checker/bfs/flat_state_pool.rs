// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Arena-backed flat state pool for zero-allocation successor dedup.
//!
//! During BFS successor generation, most generated states (~95%) are duplicates
//! that get discarded after fingerprint dedup. Currently each successor allocates
//! heap memory (`Box<[i64]>` for `FlatState` or `Arc<[Value]>` for `ArrayState`)
//! before dedup, wasting allocations on states that are immediately dropped.
//!
//! `FlatStatePool` pre-allocates a reusable pool of `[i64]` buffers backed by a
//! single contiguous mmap region. Successor generation writes into a borrowed
//! buffer from the pool. After the fingerprint check, only states that pass dedup
//! are copied to the permanent frontier arena. Buffers that fail dedup are returned
//! to the pool with zero deallocation.
//!
//! # Design
//!
//! The pool is a simple free-list of fixed-size `[i64]` slots backed by a single
//! mmap allocation. Each slot holds one state vector of `state_len` i64 words.
//!
//! ```text
//! ┌──────────┬──────────┬──────────┬──────────┬──────────┐
//! │  slot 0  │  slot 1  │  slot 2  │  slot 3  │  slot 4  │  ... mmap region
//! └──────────┴──────────┴──────────┴──────────┴──────────┘
//!       ↑          ↑                     ↑
//!   [in use]   [in use]             [in use]
//!                            ↕
//!               free_stack: [3, 4, 5, ...]
//! ```
//!
//! - `checkout()` pops a slot index from the free stack and returns a mutable
//!   `&mut [i64]` reference. O(1).
//! - `checkin(handle)` pushes the slot index back onto the free stack. O(1).
//! - No malloc or free occurs per successor — the mmap region is allocated once
//!   at pool creation and reused for the entire BFS level.
//!
//! # Memory savings
//!
//! For a spec with 15-slot states and a BFS level generating 10,000 successors
//! where 95% are duplicates:
//! - **Before**: 10,000 `Box<[i64]>` heap allocations = 10,000 malloc + 10,000 free
//! - **After**: pool of ~500 buffers (peak in-flight), 0 malloc, 0 free per successor
//!
//! The pool capacity only needs to cover the maximum number of simultaneously
//! in-flight (checked-out) buffers, not the total successors generated.
//!
//! Part of #4172: Arena-backed flat state pool.

use std::fmt;
use std::io;
use std::mem::size_of;
use std::ptr::{self, NonNull};
use std::slice;

const I64_BYTES: usize = size_of::<i64>();

/// Handle to a checked-out buffer from the pool.
///
/// The handle tracks the slot index so it can be returned to the pool.
/// The handle does NOT implement `Drop` — callers must explicitly call
/// `FlatStatePool::checkin()` to return the buffer. This is deliberate:
/// auto-drop would require interior mutability (RefCell) on the pool,
/// adding overhead on the hot path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::check::model_checker) struct PoolHandle {
    slot_index: u32,
}

/// Arena-backed pool of reusable `[i64]` state buffers.
///
/// Each buffer holds `state_len` i64 words. Buffers are checked out for
/// successor generation and checked back in after dedup, with zero heap
/// allocation per successor.
///
/// Exclusively owned by one BFS worker thread (`&mut self` for mutations).
///
/// Part of #4172.
pub(in crate::check::model_checker) struct FlatStatePool {
    /// Mmap-backed contiguous buffer for all slots.
    base_ptr: NonNull<u8>,
    /// Total byte size of the mmap region.
    byte_len: usize,
    /// Number of i64 words per state slot.
    state_len: usize,
    /// Byte stride per slot (state_len * 8).
    stride_bytes: usize,
    /// Total number of slots in the pool.
    capacity: u32,
    /// Free-list stack: indices of available slots.
    /// Slots are popped from the back (O(1)) on checkout and pushed back on checkin.
    free_stack: Vec<u32>,
    /// Number of buffers currently checked out (for statistics).
    checked_out: u32,
    /// Peak number of simultaneously checked-out buffers.
    peak_checked_out: u32,
    /// Total checkout operations performed (for statistics).
    total_checkouts: u64,
    /// Total checkin operations performed (for statistics).
    total_checkins: u64,
}

// SAFETY: `FlatStatePool` owns a process-private mmap region. The `NonNull<u8>`
// does not alias any other allocation. Sending to another thread is safe because
// only one thread uses it at a time via `&mut self`.
unsafe impl Send for FlatStatePool {}

impl FlatStatePool {
    /// Create a new pool with `capacity` reusable buffers, each holding
    /// `state_len` i64 words.
    ///
    /// # Panics
    ///
    /// Panics if `capacity == 0` or `state_len == 0`.
    #[must_use]
    pub(in crate::check::model_checker) fn new(capacity: u32, state_len: usize) -> Self {
        assert!(capacity > 0, "FlatStatePool capacity must be > 0");
        assert!(state_len > 0, "FlatStatePool state_len must be > 0");

        let stride_bytes = state_len
            .checked_mul(I64_BYTES)
            .unwrap_or_else(|| panic!("FlatStatePool stride overflow: {state_len} * {I64_BYTES}"));
        let byte_len = (capacity as usize)
            .checked_mul(stride_bytes)
            .unwrap_or_else(|| panic!("FlatStatePool size overflow: {capacity} * {stride_bytes}"));

        assert!(byte_len > 0, "FlatStatePool requires non-zero mmap size");

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
                "FlatStatePool mmap failed for {byte_len} bytes: {}",
                io::Error::last_os_error()
            );
        }

        // SAFETY: `ptr != MAP_FAILED`, so `mmap` returned a valid, non-null base
        // address for a live mapping owned by this process.
        let base_ptr = unsafe { NonNull::new_unchecked(ptr.cast::<u8>()) };

        // Initialize free stack with all slot indices (0..capacity).
        // Stack grows from the front, so we push in reverse order so that
        // slot 0 is checked out first (LIFO).
        let free_stack: Vec<u32> = (0..capacity).rev().collect();

        Self {
            base_ptr,
            byte_len,
            state_len,
            stride_bytes,
            capacity,
            free_stack,
            checked_out: 0,
            peak_checked_out: 0,
            total_checkouts: 0,
            total_checkins: 0,
        }
    }

    /// Check out a reusable buffer from the pool.
    ///
    /// Returns a `(PoolHandle, &mut [i64])` pair. The handle must be passed to
    /// `checkin()` to return the buffer to the pool after use.
    ///
    /// Returns `None` if the pool is exhausted (all buffers checked out).
    ///
    /// The returned buffer contents are undefined (may contain data from a
    /// previous use). Callers must write all `state_len` words before reading.
    #[inline]
    pub(in crate::check::model_checker) fn checkout(&mut self) -> Option<(PoolHandle, &mut [i64])> {
        let slot_index = self.free_stack.pop()?;
        self.checked_out += 1;
        self.total_checkouts += 1;
        if self.checked_out > self.peak_checked_out {
            self.peak_checked_out = self.checked_out;
        }

        let handle = PoolHandle { slot_index };
        let buf = self.slot_mut(slot_index);
        Some((handle, buf))
    }

    /// Return a checked-out buffer to the pool.
    ///
    /// The buffer becomes available for future `checkout()` calls.
    /// No deallocation occurs — the buffer is simply marked as free.
    ///
    /// # Panics
    ///
    /// Debug-asserts that the handle's slot index is valid and that `checked_out > 0`.
    #[inline]
    pub(in crate::check::model_checker) fn checkin(&mut self, handle: PoolHandle) {
        // SAFETY-CRITICAL: These checks prevent aliasing &mut [i64] in release builds.
        // A double-checkin pushes the same slot index onto the free stack twice, so two
        // subsequent checkouts return mutable references to the same memory — UB.
        // Promoted from debug_assert! to assert! per #4177.
        assert!(
            (handle.slot_index as usize) < self.capacity as usize,
            "FlatStatePool::checkin: invalid slot index {} (capacity {})",
            handle.slot_index,
            self.capacity,
        );
        assert!(
            self.checked_out > 0,
            "FlatStatePool::checkin: checked_out underflow (possible double-checkin)"
        );

        self.free_stack.push(handle.slot_index);
        self.checked_out -= 1;
        self.total_checkins += 1;
    }

    /// Read-only view of a checked-out buffer.
    ///
    /// This is used to read the successor state after it has been written
    /// (e.g., for fingerprinting or copying to the permanent frontier).
    ///
    /// # Safety contract
    ///
    /// The handle must have been returned by a previous `checkout()` call
    /// and not yet passed to `checkin()`.
    #[inline]
    pub(in crate::check::model_checker) fn get(&self, handle: PoolHandle) -> &[i64] {
        self.slot_ref(handle.slot_index)
    }

    /// Mutable view of a checked-out buffer.
    ///
    /// # Safety contract
    ///
    /// The handle must have been returned by a previous `checkout()` call
    /// and not yet passed to `checkin()`.
    #[inline]
    pub(in crate::check::model_checker) fn get_mut(&mut self, handle: PoolHandle) -> &mut [i64] {
        self.slot_mut(handle.slot_index)
    }

    /// Reset the pool: return all checked-out buffers to the free list.
    ///
    /// Called at BFS level boundaries when all successor buffers have been
    /// processed. This is O(capacity) but happens once per BFS level, not
    /// per successor.
    pub(in crate::check::model_checker) fn reset(&mut self) {
        self.free_stack.clear();
        self.free_stack.extend((0..self.capacity).rev());
        self.checked_out = 0;
    }

    /// Number of i64 words per buffer.
    #[inline]
    #[must_use]
    pub(in crate::check::model_checker) fn state_len(&self) -> usize {
        self.state_len
    }

    /// Total number of buffer slots in the pool.
    #[inline]
    #[must_use]
    pub(in crate::check::model_checker) fn capacity(&self) -> u32 {
        self.capacity
    }

    /// Number of buffers currently available for checkout.
    #[inline]
    #[must_use]
    pub(in crate::check::model_checker) fn available(&self) -> u32 {
        self.free_stack.len() as u32
    }

    /// Number of buffers currently checked out.
    #[inline]
    #[must_use]
    pub(in crate::check::model_checker) fn checked_out(&self) -> u32 {
        self.checked_out
    }

    /// Peak number of simultaneously checked-out buffers.
    #[inline]
    #[must_use]
    pub(in crate::check::model_checker) fn peak_checked_out(&self) -> u32 {
        self.peak_checked_out
    }

    /// Total checkout operations performed.
    #[inline]
    #[must_use]
    pub(in crate::check::model_checker) fn total_checkouts(&self) -> u64 {
        self.total_checkouts
    }

    /// Total checkin operations performed.
    #[inline]
    #[must_use]
    pub(in crate::check::model_checker) fn total_checkins(&self) -> u64 {
        self.total_checkins
    }

    /// Report pool statistics to stderr.
    pub(in crate::check::model_checker) fn report_stats(&self) {
        let capacity_bytes = self.byte_len;
        eprintln!("=== FlatStatePool Stats ===");
        eprintln!("  Capacity:         {} slots ({:.1} MB)",
            self.capacity,
            capacity_bytes as f64 / (1024.0 * 1024.0));
        eprintln!("  State len:        {} words ({} bytes/slot)",
            self.state_len, self.stride_bytes);
        eprintln!("  Checked out:      {}", self.checked_out);
        eprintln!("  Peak checked out: {}", self.peak_checked_out);
        eprintln!("  Total checkouts:  {}", self.total_checkouts);
        eprintln!("  Total checkins:   {}", self.total_checkins);
        let savings = self.total_checkins;
        eprintln!("  Allocs saved:     {} (each checkin = 1 avoided Box<[i64]> alloc+free)",
            savings);
    }

    /// Get a mutable reference to the slot at the given index.
    #[inline]
    fn slot_mut(&mut self, slot_index: u32) -> &mut [i64] {
        // SAFETY-CRITICAL: Out-of-bounds index means raw pointer arithmetic past the
        // mmap region — UB and potential segfault. Promoted from debug_assert! per #4177.
        assert!(
            (slot_index as usize) < self.capacity as usize,
            "FlatStatePool::slot_mut: index {} >= capacity {}",
            slot_index,
            self.capacity,
        );
        let byte_offset = (slot_index as usize) * self.stride_bytes;
        // SAFETY: `slot_index < capacity`, so `byte_offset + stride_bytes <= byte_len`.
        // The base pointer comes from `mmap` (page-aligned), and each stride is a
        // multiple of `size_of::<i64>()`, so the cast preserves alignment. `&mut self`
        // guarantees exclusive access.
        unsafe {
            let ptr = self.base_ptr.as_ptr().add(byte_offset).cast::<i64>();
            slice::from_raw_parts_mut(ptr, self.state_len)
        }
    }

    /// Get a shared reference to the slot at the given index.
    #[inline]
    fn slot_ref(&self, slot_index: u32) -> &[i64] {
        // SAFETY-CRITICAL: Out-of-bounds index means raw pointer arithmetic past the
        // mmap region — UB and potential segfault. Promoted from debug_assert! per #4177.
        assert!(
            (slot_index as usize) < self.capacity as usize,
            "FlatStatePool::slot_ref: index {} >= capacity {}",
            slot_index,
            self.capacity,
        );
        let byte_offset = (slot_index as usize) * self.stride_bytes;
        // SAFETY: Same alignment and bounds reasoning as `slot_mut`. `&self`
        // guarantees no mutable alias exists.
        unsafe {
            let ptr = self.base_ptr.as_ptr().add(byte_offset).cast::<i64>();
            slice::from_raw_parts(ptr, self.state_len)
        }
    }
}

impl fmt::Debug for FlatStatePool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FlatStatePool")
            .field("capacity", &self.capacity)
            .field("state_len", &self.state_len)
            .field("byte_len", &self.byte_len)
            .field("checked_out", &self.checked_out)
            .field("available", &self.available())
            .field("peak_checked_out", &self.peak_checked_out)
            .field("total_checkouts", &self.total_checkouts)
            .finish()
    }
}

impl Drop for FlatStatePool {
    fn drop(&mut self) {
        // SAFETY: `base_ptr` and `byte_len` were returned by `mmap` in `new` and
        // still describe the owned mapping at drop time.
        let ret = unsafe { libc::munmap(self.base_ptr.as_ptr().cast(), self.byte_len) };
        debug_assert_eq!(
            ret,
            0,
            "FlatStatePool munmap failed: {}",
            io::Error::last_os_error()
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ========================================================================
    // Basic pool operations
    // ========================================================================

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_pool_new_valid() {
        let pool = FlatStatePool::new(16, 5);
        assert_eq!(pool.capacity(), 16);
        assert_eq!(pool.state_len(), 5);
        assert_eq!(pool.available(), 16);
        assert_eq!(pool.checked_out(), 0);
        assert_eq!(pool.peak_checked_out(), 0);
        assert_eq!(pool.total_checkouts(), 0);
        assert_eq!(pool.total_checkins(), 0);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    #[should_panic(expected = "FlatStatePool capacity must be > 0")]
    fn test_pool_zero_capacity_panics() {
        let _ = FlatStatePool::new(0, 5);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    #[should_panic(expected = "FlatStatePool state_len must be > 0")]
    fn test_pool_zero_state_len_panics() {
        let _ = FlatStatePool::new(16, 0);
    }

    // ========================================================================
    // Checkout and checkin
    // ========================================================================

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_checkout_and_checkin() {
        let mut pool = FlatStatePool::new(4, 3);

        // Checkout a buffer and write to it.
        let (handle, buf) = pool.checkout().unwrap();
        buf.copy_from_slice(&[10, 20, 30]);

        assert_eq!(pool.checked_out(), 1);
        assert_eq!(pool.available(), 3);
        assert_eq!(pool.total_checkouts(), 1);

        // Read back via get().
        assert_eq!(pool.get(handle), &[10, 20, 30]);

        // Checkin returns the buffer.
        pool.checkin(handle);
        assert_eq!(pool.checked_out(), 0);
        assert_eq!(pool.available(), 4);
        assert_eq!(pool.total_checkins(), 1);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_checkout_multiple_buffers() {
        let mut pool = FlatStatePool::new(8, 2);

        let (h1, b1) = pool.checkout().unwrap();
        b1.copy_from_slice(&[1, 2]);

        let (h2, b2) = pool.checkout().unwrap();
        b2.copy_from_slice(&[3, 4]);

        let (h3, b3) = pool.checkout().unwrap();
        b3.copy_from_slice(&[5, 6]);

        assert_eq!(pool.checked_out(), 3);
        assert_eq!(pool.peak_checked_out(), 3);

        // Each buffer is independent.
        assert_eq!(pool.get(h1), &[1, 2]);
        assert_eq!(pool.get(h2), &[3, 4]);
        assert_eq!(pool.get(h3), &[5, 6]);

        // Checkin in different order.
        pool.checkin(h2);
        assert_eq!(pool.checked_out(), 2);

        pool.checkin(h1);
        pool.checkin(h3);
        assert_eq!(pool.checked_out(), 0);
        assert_eq!(pool.peak_checked_out(), 3); // Peak preserved.
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_pool_exhaustion_returns_none() {
        let mut pool = FlatStatePool::new(2, 3);

        let (h1, _) = pool.checkout().unwrap();
        let (h2, _) = pool.checkout().unwrap();

        // Pool is exhausted.
        assert!(pool.checkout().is_none());
        assert_eq!(pool.checked_out(), 2);
        assert_eq!(pool.available(), 0);

        // After checkin, can checkout again.
        pool.checkin(h1);
        assert_eq!(pool.available(), 1);

        let (h3, buf) = pool.checkout().unwrap();
        buf.copy_from_slice(&[7, 8, 9]);
        assert_eq!(pool.get(h3), &[7, 8, 9]);

        pool.checkin(h2);
        pool.checkin(h3);
    }

    // ========================================================================
    // Buffer reuse and isolation
    // ========================================================================

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_buffer_reuse_after_checkin() {
        let mut pool = FlatStatePool::new(1, 4);

        // First use.
        let (h1, buf1) = pool.checkout().unwrap();
        buf1.copy_from_slice(&[10, 20, 30, 40]);
        assert_eq!(pool.get(h1), &[10, 20, 30, 40]);
        pool.checkin(h1);

        // Second use: same physical buffer, can overwrite.
        let (h2, buf2) = pool.checkout().unwrap();
        // Contents may be stale (previous use data), which is fine.
        buf2.copy_from_slice(&[50, 60, 70, 80]);
        assert_eq!(pool.get(h2), &[50, 60, 70, 80]);
        pool.checkin(h2);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_get_mut_modifies_buffer() {
        let mut pool = FlatStatePool::new(4, 3);

        let (handle, buf) = pool.checkout().unwrap();
        buf.copy_from_slice(&[1, 2, 3]);

        // Modify via get_mut.
        let buf_mut = pool.get_mut(handle);
        buf_mut[1] = 99;

        assert_eq!(pool.get(handle), &[1, 99, 3]);
        pool.checkin(handle);
    }

    // ========================================================================
    // Reset
    // ========================================================================

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_pool_reset() {
        let mut pool = FlatStatePool::new(4, 2);

        // Checkout all.
        let _ = pool.checkout().unwrap();
        let _ = pool.checkout().unwrap();
        let _ = pool.checkout().unwrap();
        let _ = pool.checkout().unwrap();
        assert_eq!(pool.checked_out(), 4);
        assert_eq!(pool.available(), 0);

        // Reset returns everything.
        pool.reset();
        assert_eq!(pool.checked_out(), 0);
        assert_eq!(pool.available(), 4);

        // Can checkout again after reset.
        let (h, buf) = pool.checkout().unwrap();
        buf.copy_from_slice(&[77, 88]);
        assert_eq!(pool.get(h), &[77, 88]);
        pool.checkin(h);
    }

    // ========================================================================
    // Statistics tracking
    // ========================================================================

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_pool_stats_tracking() {
        let mut pool = FlatStatePool::new(8, 3);

        // Multiple checkout/checkin cycles.
        for i in 0..100 {
            let (h, buf) = pool.checkout().unwrap();
            buf[0] = i;
            pool.checkin(h);
        }

        assert_eq!(pool.total_checkouts(), 100);
        assert_eq!(pool.total_checkins(), 100);
        assert_eq!(pool.peak_checked_out(), 1);
        assert_eq!(pool.checked_out(), 0);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_pool_peak_tracks_maximum() {
        let mut pool = FlatStatePool::new(8, 2);

        let (h1, _) = pool.checkout().unwrap();
        let (h2, _) = pool.checkout().unwrap();
        let (h3, _) = pool.checkout().unwrap();
        assert_eq!(pool.peak_checked_out(), 3);

        pool.checkin(h1);
        pool.checkin(h2);
        pool.checkin(h3);
        assert_eq!(pool.peak_checked_out(), 3); // Peak is sticky.

        let (h4, _) = pool.checkout().unwrap();
        assert_eq!(pool.peak_checked_out(), 3); // Still 3.

        let (h5, _) = pool.checkout().unwrap();
        let (h6, _) = pool.checkout().unwrap();
        let (h7, _) = pool.checkout().unwrap();
        assert_eq!(pool.peak_checked_out(), 4); // New peak.

        pool.checkin(h4);
        pool.checkin(h5);
        pool.checkin(h6);
        pool.checkin(h7);
    }

    // ========================================================================
    // BFS dedup simulation
    // ========================================================================

    /// Simulate the core BFS dedup pattern:
    /// 1. Checkout buffer from pool
    /// 2. Write successor state
    /// 3. Compute fingerprint (simulated as simple hash)
    /// 4. Check dedup (simulated with HashSet)
    /// 5. If new: copy to permanent storage; if duplicate: just checkin
    /// 6. Checkin handle regardless
    ///
    /// This verifies that the pool produces identical results to heap allocation.
    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_pool_bfs_dedup_simulation() {
        use std::collections::HashSet;

        let state_len = 5;
        let mut pool = FlatStatePool::new(64, state_len);
        let mut seen: HashSet<Vec<i64>> = HashSet::new();
        let mut frontier: Vec<Vec<i64>> = Vec::new();

        // Simulate 200 successors where many are duplicates.
        let successors: Vec<Vec<i64>> = (0..200)
            .map(|i| {
                let base = i % 30; // Only 30 unique states.
                vec![
                    base as i64,
                    base as i64 * 2,
                    base as i64 * 3,
                    base as i64 + 1,
                    base as i64 + 2,
                ]
            })
            .collect();

        for succ_data in &successors {
            // 1. Checkout
            let (handle, buf) = pool.checkout().unwrap();

            // 2. Write successor
            buf.copy_from_slice(succ_data);

            // 3+4. Fingerprint + dedup check
            let state_key = pool.get(handle).to_vec();
            let is_new = seen.insert(state_key.clone());

            // 5. If new, copy to permanent storage
            if is_new {
                frontier.push(pool.get(handle).to_vec());
            }

            // 6. Always checkin
            pool.checkin(handle);
        }

        // Verify results.
        assert_eq!(seen.len(), 30, "should have 30 unique states");
        assert_eq!(frontier.len(), 30, "frontier should have 30 states");
        assert_eq!(pool.checked_out(), 0, "all buffers returned");
        assert_eq!(pool.total_checkouts(), 200);
        assert_eq!(pool.total_checkins(), 200);

        // Verify frontier contents match expected unique states.
        for (i, state) in frontier.iter().enumerate() {
            assert_eq!(state.len(), state_len);
            assert_eq!(state[0], i as i64);
            assert_eq!(state[1], (i as i64) * 2);
        }
    }

    /// Simulate multiple BFS levels with pool reset between levels.
    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_pool_multi_level_bfs_simulation() {
        let state_len = 3;
        let mut pool = FlatStatePool::new(32, state_len);
        let mut total_new: usize = 0;

        for level in 0..5 {
            // Generate 50 successors per level, 10 unique.
            for i in 0..50 {
                let base = i % 10;
                let (handle, buf) = pool.checkout().unwrap();
                buf[0] = level as i64;
                buf[1] = base as i64;
                buf[2] = (level * 100 + base) as i64;

                // Simulate: every first occurrence (i < 10) is "new".
                if i < 10 {
                    total_new += 1;
                }

                pool.checkin(handle);
            }

            // Level boundary reset.
            pool.reset();
        }

        assert_eq!(total_new, 50); // 10 new per level * 5 levels
        assert_eq!(pool.checked_out(), 0);
    }

    // ========================================================================
    // Allocation savings benchmark
    // ========================================================================

    /// Compare pool checkout/checkin vs heap alloc/free for many successor
    /// states. This is a correctness test that also demonstrates the pattern.
    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_pool_vs_heap_identical_results() {
        let state_len = 8;
        let num_successors = 500;
        let dedup_ratio = 0.95; // 95% duplicates
        let num_unique = ((num_successors as f64) * (1.0 - dedup_ratio)) as usize;

        // --- Pool path ---
        let mut pool = FlatStatePool::new(64, state_len);
        let mut pool_frontier: Vec<Vec<i64>> = Vec::new();
        let mut pool_seen: HashSet<i64> = HashSet::new();

        use std::collections::HashSet;

        for i in 0..num_successors {
            let key = (i % (num_unique + 1)) as i64;
            let (handle, buf) = pool.checkout().unwrap();
            for j in 0..state_len {
                buf[j] = key * 10 + j as i64;
            }

            if pool_seen.insert(key) {
                pool_frontier.push(pool.get(handle).to_vec());
            }
            pool.checkin(handle);
        }

        // --- Heap path ---
        let mut heap_frontier: Vec<Vec<i64>> = Vec::new();
        let mut heap_seen: HashSet<i64> = HashSet::new();

        for i in 0..num_successors {
            let key = (i % (num_unique + 1)) as i64;
            let mut buf = vec![0i64; state_len];
            for j in 0..state_len {
                buf[j] = key * 10 + j as i64;
            }

            if heap_seen.insert(key) {
                heap_frontier.push(buf.clone());
            }
            // buf is dropped (freed) here.
        }

        // Both paths must produce identical results.
        assert_eq!(pool_frontier.len(), heap_frontier.len());
        for (p, h) in pool_frontier.iter().zip(heap_frontier.iter()) {
            assert_eq!(p, h, "pool and heap frontiers diverged");
        }

        // Pool stats show savings.
        assert_eq!(pool.total_checkouts(), num_successors as u64);
        assert_eq!(pool.total_checkins(), num_successors as u64);
        assert_eq!(pool.checked_out(), 0);
    }

    // ========================================================================
    // Edge cases
    // ========================================================================

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_pool_single_slot() {
        let mut pool = FlatStatePool::new(1, 2);

        let (h, buf) = pool.checkout().unwrap();
        buf.copy_from_slice(&[42, 43]);
        assert!(pool.checkout().is_none()); // Pool exhausted.

        pool.checkin(h);
        let (h2, buf2) = pool.checkout().unwrap();
        buf2.copy_from_slice(&[99, 100]);
        assert_eq!(pool.get(h2), &[99, 100]);
        pool.checkin(h2);
    }

    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_pool_large_state() {
        let state_len = 128;
        let mut pool = FlatStatePool::new(4, state_len);

        let (handle, buf) = pool.checkout().unwrap();
        for i in 0..state_len {
            buf[i] = (i * i) as i64;
        }
        for i in 0..state_len {
            assert_eq!(pool.get(handle)[i], (i * i) as i64);
        }
        pool.checkin(handle);
    }

    /// Test that pool handles produce correct data when checked out
    /// concurrently (multiple handles live at once).
    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    fn test_pool_concurrent_handles_isolation() {
        let mut pool = FlatStatePool::new(4, 3);

        let (h1, b1) = pool.checkout().unwrap();
        b1.copy_from_slice(&[1, 1, 1]);

        let (h2, b2) = pool.checkout().unwrap();
        b2.copy_from_slice(&[2, 2, 2]);

        // Modify h1 via get_mut — should not affect h2.
        let b1_mut = pool.get_mut(h1);
        b1_mut[0] = 100;

        assert_eq!(pool.get(h1), &[100, 1, 1]);
        assert_eq!(pool.get(h2), &[2, 2, 2]); // Unaffected.

        pool.checkin(h1);
        pool.checkin(h2);
    }

    // ========================================================================
    // Double-checkin detection (#4177)
    // ========================================================================

    /// Verify that double-checkin panics in all build modes (not just debug).
    ///
    /// A double-checkin pushes the same slot index onto the free stack twice,
    /// so two subsequent checkouts return `&mut [i64]` to the same memory —
    /// aliasing mutable references, which is UB. The assert! in checkin()
    /// catches this by detecting checked_out underflow.
    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    #[should_panic(expected = "checked_out underflow")]
    fn test_double_checkin_panics() {
        let mut pool = FlatStatePool::new(4, 3);

        let (handle, buf) = pool.checkout().unwrap();
        buf.copy_from_slice(&[1, 2, 3]);

        // First checkin is valid.
        pool.checkin(handle);
        assert_eq!(pool.checked_out(), 0);

        // Second checkin of the same handle must panic — checked_out would underflow.
        pool.checkin(handle);
    }

    /// Verify that checkin with an out-of-bounds slot index panics.
    #[test]
    #[cfg_attr(test, ntest::timeout(10000))]
    #[should_panic(expected = "invalid slot index")]
    fn test_checkin_invalid_slot_panics() {
        let mut pool = FlatStatePool::new(4, 3);

        // Forge a handle with an out-of-bounds slot index.
        let bad_handle = PoolHandle { slot_index: 100 };
        pool.checkin(bad_handle);
    }
}
