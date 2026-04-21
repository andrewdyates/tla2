// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Eviction coordination and disk merge path for [`DiskFingerprintSet`].

use std::io;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use super::disk::DiskFingerprintSet;
use super::disk_search::{FINGERPRINT_BYTES, FPS_PER_PAGE};

/// Terminal status: most recent completed eviction succeeded.
pub(crate) const EVICTION_STATUS_SUCCESS: u64 = 0;
/// Terminal status: most recent completed eviction failed.
pub(crate) const EVICTION_STATUS_FAILURE: u64 = 1;

/// Eviction coordination state protected by a mutex.
///
/// Replaces the separate `AtomicBool evicting` + `AtomicU64 eviction_outcome_state`
/// with a single mutex-protected struct, enabling Condvar-based blocking.
pub(crate) struct EvictionState {
    /// True while a leader thread is performing eviction.
    pub(crate) evicting: bool,
    /// Monotonic eviction generation, incremented after each completed eviction.
    pub(crate) epoch: u64,
    /// Status of the most recent eviction (`EVICTION_STATUS_SUCCESS` or `EVICTION_STATUS_FAILURE`).
    pub(crate) status: u64,
}

/// Barrier for coordinating eviction across worker threads.
///
/// TLC uses `java.util.concurrent.Phaser` for this (OffHeapDiskFPSet.java:58-75).
/// We use `parking_lot::Condvar` which provides OS-level parking (zero CPU)
/// instead of the previous `thread::yield_now()` busy-spin.
///
/// Part of #2494.
pub(crate) struct EvictionBarrier {
    pub(crate) state: parking_lot::Mutex<EvictionState>,
    pub(crate) condvar: parking_lot::Condvar,
}

impl EvictionBarrier {
    pub(super) fn new() -> Self {
        EvictionBarrier {
            state: parking_lot::Mutex::new(EvictionState {
                evicting: false,
                epoch: 0,
                status: EVICTION_STATUS_SUCCESS,
            }),
            condvar: parking_lot::Condvar::new(),
        }
    }
}

/// Read the next u64 fingerprint from a reader.
///
/// Returns `Ok(None)` only on a clean EOF at fingerprint boundary (0 bytes read).
/// Returns `Err(UnexpectedEof)` on truncated trailing bytes so eviction merge
/// does not silently treat corruption as end-of-stream (#1777).
pub(crate) fn read_next_fp(reader: &mut impl std::io::Read) -> io::Result<Option<u64>> {
    let mut buf = [0u8; FINGERPRINT_BYTES];
    let mut filled = 0usize;

    while filled < FINGERPRINT_BYTES {
        match reader.read(&mut buf[filled..]) {
            Ok(0) if filled == 0 => return Ok(None),
            Ok(0) => {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    format!(
                        "truncated fingerprint entry: read {} of {} bytes",
                        filled, FINGERPRINT_BYTES
                    ),
                ));
            }
            Ok(n) => {
                filled += n;
            }
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    }

    Ok(Some(u64::from_le_bytes(buf)))
}

/// RAII guard that clears the `evicting` flag and wakes waiting threads.
///
/// On normal completion, the leader publishes the outcome (epoch + status)
/// before this guard drops. On panic unwind, the epoch is unchanged and
/// waiters detect the coordination error via `evicting == false && epoch unchanged`.
///
/// Fix for #1778 (original). Part of #2494 (Condvar notification on drop).
pub(crate) struct EvictGuard<'a> {
    pub(crate) barrier: &'a EvictionBarrier,
}

impl Drop for EvictGuard<'_> {
    fn drop(&mut self) {
        {
            let mut state = self.barrier.state.lock();
            state.evicting = false;
        }
        self.barrier.condvar.notify_all();
    }
}

/// Roll back staged eviction metadata if file publish fails.
///
/// Fix for #2307: avoid exposing a mixed state where `disk_path` and in-memory
/// metadata (`page_index`, `disk_count`) describe different layouts.
struct EvictMetadataRollbackGuard<'a> {
    page_index: &'a parking_lot::RwLock<Vec<u64>>,
    disk_count: &'a AtomicUsize,
    old_page_index: Option<Vec<u64>>,
    old_disk_count: usize,
    publish_succeeded: bool,
}

impl<'a> EvictMetadataRollbackGuard<'a> {
    fn new(set: &'a DiskFingerprintSet) -> Self {
        let old_page_index = set.page_index.read().clone();
        let old_disk_count = set.disk_count.load(Ordering::Relaxed);
        Self {
            page_index: &set.page_index,
            disk_count: &set.disk_count,
            old_page_index: Some(old_page_index),
            old_disk_count,
            publish_succeeded: false,
        }
    }

    fn mark_publish_succeeded(&mut self) {
        self.publish_succeeded = true;
        self.old_page_index = None;
    }
}

impl Drop for EvictMetadataRollbackGuard<'_> {
    fn drop(&mut self) {
        if self.publish_succeeded {
            return;
        }

        if let Some(old_page_index) = self.old_page_index.take() {
            *self.page_index.write() = old_page_index;
        }
        self.disk_count
            .store(self.old_disk_count, Ordering::Relaxed);
    }
}

impl DiskFingerprintSet {
    fn waiter_outcome_from_status(&self, status: u64) -> io::Result<()> {
        match status {
            EVICTION_STATUS_SUCCESS => Ok(()),
            EVICTION_STATUS_FAILURE => Err(io::Error::other("peer eviction failed")),
            _ => Err(io::Error::other(
                "peer eviction completed with unknown terminal status",
            )),
        }
    }

    /// Wait for a concurrent eviction to complete, blocking on the condvar.
    ///
    /// Called when a thread discovers another thread is already evicting.
    /// Returns the outcome of the peer's eviction. Part of #2494.
    fn await_peer_eviction(
        &self,
        mut state: parking_lot::MutexGuard<'_, EvictionState>,
    ) -> io::Result<()> {
        const EVICT_WAIT_TIMEOUT: Duration = Duration::from_secs(60);

        let observed_epoch = state.epoch;
        let start = Instant::now();
        loop {
            if state.epoch != observed_epoch {
                return self.waiter_outcome_from_status(state.status);
            }
            if !state.evicting {
                // Leader dropped EvictGuard without publishing (panic path).
                if state.epoch != observed_epoch {
                    return self.waiter_outcome_from_status(state.status);
                }
                return Err(io::Error::other(
                    "eviction coordination error: peer ended without publishing outcome",
                ));
            }
            let remaining = EVICT_WAIT_TIMEOUT.saturating_sub(start.elapsed());
            if remaining.is_zero() {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "eviction wait timeout: evicting thread may have panicked",
                ));
            }
            if self
                .eviction_barrier
                .condvar
                .wait_for(&mut state, remaining)
                .timed_out()
            {
                if state.epoch != observed_epoch {
                    return self.waiter_outcome_from_status(state.status);
                }
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "eviction wait timeout: evicting thread may have panicked",
                ));
            }
        }
    }

    /// Evict fingerprints from primary to disk.
    ///
    /// This is called when primary storage is full. It:
    /// 1. Acquires write lock on primary_barrier (blocks worker insert/contains)
    /// 2. Collects all fingerprints from primary
    /// 3. Sorts them
    /// 4. Merges with existing disk file (if any)
    /// 5. Writes new sorted disk file
    /// 6. Rebuilds page index
    /// 7. Marks primary entries as flushed
    /// 8. Releases write lock
    ///
    /// Returns `Ok(())` on success, or if another thread completed a successful
    /// eviction while we were waiting.
    /// Returns `Err` if `do_evict()` fails (e.g., disk full, I/O error).
    ///
    /// Fix for #1760: propagate errors instead of silently swallowing them.
    /// Fix for #1778: EvictGuard ensures flag is reset even on panic unwind.
    pub(crate) fn evict(&self) -> io::Result<()> {
        let mut state = self.eviction_barrier.state.lock();

        if state.evicting {
            return self.await_peer_eviction(state);
        }

        // This thread becomes the eviction leader.
        state.evicting = true;
        drop(state);

        let _guard = EvictGuard {
            barrier: &self.eviction_barrier,
        };

        let result = self.do_evict();

        // Publish outcome atomically: epoch + status + evicting=false in one
        // critical section. Setting evicting=false here prevents the race where
        // a new thread sees {evicting: true, epoch: NEW} and gets a spurious
        // "peer ended without publishing outcome" error when EvictGuard drops.
        // EvictGuard.drop() is then a no-op (idempotent evicting=false).
        {
            let mut state = self.eviction_barrier.state.lock();
            state.epoch = state.epoch.wrapping_add(1);
            state.status = if result.is_ok() {
                EVICTION_STATUS_SUCCESS
            } else {
                EVICTION_STATUS_FAILURE
            };
            state.evicting = false;
        }
        self.eviction_barrier.condvar.notify_all();

        result
    }

    /// Internal eviction logic.
    ///
    /// Holds the primary_barrier write lock for the entire duration to ensure
    /// the primary is never mutated concurrently with worker `insert()`/`contains()`.
    /// Fix for #1423.
    pub(crate) fn do_evict(&self) -> io::Result<()> {
        use std::io::{BufWriter, Write};

        // Acquire write lock: blocks all worker insert/contains until eviction completes.
        // This guarantees exclusive access during collect + publish + flush marking.
        let _barrier = self.primary_barrier.write();

        self.eviction_count.fetch_add(1, Ordering::Relaxed);

        // Collect fingerprints from primary
        let mut fps = self.collect_primary_fps();
        if fps.is_empty() {
            return Ok(());
        }

        // Sort and dedup primary fps
        fps.sort_unstable();
        fps.dedup();

        let tmp_path = self.disk_path.with_extension("tmp");
        let existing_disk_count = self.disk_count.load(Ordering::Relaxed);

        let (new_index, total_count) = if existing_disk_count > 0 {
            // Streaming two-way merge: O(primary_size) memory instead of O(total_states).
            // Part of #1784, #1777.
            self.streaming_merge(&fps, &tmp_path)?
        } else {
            // No disk file yet — write sorted fps directly with on-the-fly page index.
            let file = std::fs::File::create(&tmp_path)?;
            let mut writer = BufWriter::new(file);
            let mut new_index = Vec::with_capacity(fps.len().div_ceil(FPS_PER_PAGE));
            for (i, &fp) in fps.iter().enumerate() {
                if i % FPS_PER_PAGE == 0 {
                    new_index.push(fp);
                }
                writer.write_all(&fp.to_le_bytes())?;
            }
            writer.flush()?;
            (new_index, fps.len())
        };

        let mut metadata_guard = EvictMetadataRollbackGuard::new(self);
        // Stage metadata before publish. If publish fails, rollback guard restores
        // the previous metadata to avoid mixed old/new state (#2307).
        *self.page_index.write() = new_index;
        self.disk_count.store(total_count, Ordering::Relaxed);

        // Commit point: once file publish succeeds, staged metadata must remain.
        self.publish_eviction_file(&tmp_path)?;
        metadata_guard.mark_publish_succeeded();

        // Mark primary entries as flushed (TLC parity: entries stay in-memory
        // as a lookup cache, avoiding unnecessary disk I/O for recently-evicted FPs).
        self.primary.mark_all_flushed();

        // Part of #2664: verify disk file invariants after each eviction in debug builds.
        debug_assert!(
            self.check_invariant_impl().unwrap_or(false),
            "DiskFingerprintSet invariant violated after eviction"
        );

        Ok(())
    }

    fn publish_eviction_file(&self, tmp_path: &std::path::Path) -> io::Result<()> {
        #[cfg(test)]
        if self.fail_next_publish.swap(false, Ordering::SeqCst) {
            return Err(io::Error::other(
                "injected eviction publish failure before disk replace",
            ));
        }

        // Cache new file length before rename so readers see it atomically
        // with the epoch advance. Part of #2371 (S1).
        let new_len = std::fs::metadata(tmp_path)?.len();

        std::fs::rename(tmp_path, &self.disk_path)?;

        // Update cached file length and invalidate stale reader sessions.
        // Ordering: store file_len before advancing epoch ensures readers
        // that see the new epoch also see the correct file_len.
        self.disk_file_len.store(new_len, Ordering::Release);
        self.disk_reader_pool.advance_epoch();

        Ok(())
    }

    /// Collect all fingerprints from primary storage.
    ///
    /// Note: This is O(capacity) scan - only used during eviction.
    fn collect_primary_fps(&self) -> Vec<u64> {
        self.primary.collect_all()
    }

    /// Streaming two-way merge of sorted primary fingerprints with sorted disk file.
    ///
    /// Writes merged output directly to `tmp_path` without loading the entire disk
    /// file into memory. Builds the page index on-the-fly during the write.
    ///
    /// Memory: O(primary_size) + small read/write buffers + page index.
    /// Time: O(primary_size + disk_count).
    ///
    /// Part of #1784, #1777: replaces read-all-then-sort merge that required
    /// O(total_states) memory, defeating the purpose of disk-backed storage.
    fn streaming_merge(
        &self,
        sorted_new: &[u64],
        tmp_path: &std::path::Path,
    ) -> io::Result<(Vec<u64>, usize)> {
        use std::io::{BufReader, BufWriter, Write};

        let disk_file = std::fs::File::open(&self.disk_path)?;
        let mut disk_reader = BufReader::new(disk_file);
        let out_file = std::fs::File::create(tmp_path)?;
        let mut writer = BufWriter::new(out_file);

        let mut new_idx: usize = 0;
        let mut total: usize = 0;
        let mut new_index = Vec::new();

        // Emit one fingerprint: build page index on-the-fly and write to disk.
        let mut emit = |fp: u64, writer: &mut BufWriter<std::fs::File>| -> io::Result<()> {
            if total % FPS_PER_PAGE == 0 {
                new_index.push(fp);
            }
            writer.write_all(&fp.to_le_bytes())?;
            total += 1;
            Ok(())
        };

        // Read first disk entry
        let mut disk_val = read_next_fp(&mut disk_reader)?;

        loop {
            match (new_idx < sorted_new.len(), disk_val) {
                (true, Some(dv)) => {
                    let nv = sorted_new[new_idx];
                    match nv.cmp(&dv) {
                        std::cmp::Ordering::Less => {
                            emit(nv, &mut writer)?;
                            new_idx += 1;
                        }
                        std::cmp::Ordering::Equal => {
                            // Duplicate: write once, advance both sources.
                            emit(nv, &mut writer)?;
                            new_idx += 1;
                            disk_val = read_next_fp(&mut disk_reader)?;
                        }
                        std::cmp::Ordering::Greater => {
                            emit(dv, &mut writer)?;
                            disk_val = read_next_fp(&mut disk_reader)?;
                        }
                    }
                }
                (true, None) => {
                    // Remaining new entries only
                    emit(sorted_new[new_idx], &mut writer)?;
                    new_idx += 1;
                }
                (false, Some(dv)) => {
                    // Remaining disk entries only
                    emit(dv, &mut writer)?;
                    disk_val = read_next_fp(&mut disk_reader)?;
                }
                (false, None) => break,
            }
        }

        writer.flush()?;
        Ok((new_index, total))
    }
}
