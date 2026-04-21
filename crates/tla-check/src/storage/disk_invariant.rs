// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Diagnostic and collection methods for [`DiskFingerprintSet`].
//!
//! These operations iterate every page sequentially and are intentionally
//! slow and thorough — they are never on the hot path.

use std::sync::atomic::Ordering;

use crate::state::Fingerprint;

use super::contracts::StorageFault;
use super::disk::DiskFingerprintSet;
use super::disk_search::{FINGERPRINT_BYTES, FPS_PER_PAGE, PAGE_SIZE};

impl DiskFingerprintSet {
    /// Verify internal consistency of disk-backed fingerprint storage.
    ///
    /// Checks:
    /// 1. Sorted order: `fp[i] < fp[i+1]` for all consecutive entries
    /// 2. Page index consistency: each `page_index[p]` equals the first FP on page `p`
    /// 3. Count consistency: actual entries on disk == `disk_count`
    ///
    /// TLC reference: `FPSetStatistic.checkInvariant()`, `FPSet.checkFPs()`.
    ///
    /// Part of #2664.
    pub(super) fn check_invariant_impl(&self) -> Result<bool, StorageFault> {
        let disk_count = self.disk_count.load(Ordering::Acquire);
        if disk_count == 0 {
            return Ok(true);
        }

        let file_len = self.disk_file_len.load(Ordering::Acquire);
        if file_len == 0 {
            eprintln!(
                "[check_invariant] FAIL: disk_count={} but file_len=0",
                disk_count,
            );
            return Ok(false);
        }

        let page_index = self.page_index.read();
        let total_pages = (file_len as usize).div_ceil(PAGE_SIZE);

        let mut session = self
            .disk_reader_pool
            .checkout()
            .map_err(|e: std::io::Error| {
                StorageFault::new("disk", "check_invariant", e.to_string())
            })?;

        let mut actual_count: usize = 0;
        let mut prev_fp: Option<u64> = None;
        let mut ok = true;

        for page in 0..total_pages {
            let bytes = session
                .read_page_exact(page, file_len)
                .map_err(|e: std::io::Error| {
                    StorageFault::new("disk", "check_invariant", e.to_string())
                })?;

            for (i, chunk) in bytes.chunks_exact(FINGERPRINT_BYTES).enumerate() {
                let fp = u64::from_le_bytes(
                    chunk
                        .try_into()
                        .expect("invariant: chunks_exact guarantees 8-byte chunks"),
                );

                // Check page index consistency: first FP on each page must match.
                if i == 0 {
                    if let Some(&expected) = page_index.get(page) {
                        if fp != expected {
                            eprintln!(
                                "[check_invariant] FAIL: page {} first FP {} != page_index {}",
                                page, fp, expected,
                            );
                            ok = false;
                        }
                    } else {
                        eprintln!(
                            "[check_invariant] FAIL: page {} exists on disk but missing from page_index (len={})",
                            page, page_index.len(),
                        );
                        ok = false;
                    }
                }

                // Check sorted order: each FP must be strictly greater than the previous.
                if let Some(prev) = prev_fp {
                    if fp <= prev {
                        eprintln!(
                            "[check_invariant] FAIL: sort violation at entry {}: {} <= {}",
                            actual_count, fp, prev,
                        );
                        ok = false;
                    }
                }

                prev_fp = Some(fp);
                actual_count += 1;
            }

            // Verify page had the expected number of FPs
            if bytes.len() % FINGERPRINT_BYTES != 0 {
                eprintln!(
                    "[check_invariant] FAIL: page {} has {} bytes, not aligned to {} byte FPs",
                    page,
                    bytes.len(),
                    FINGERPRINT_BYTES,
                );
                ok = false;
            }
        }

        // Check count consistency.
        if actual_count != disk_count {
            eprintln!(
                "[check_invariant] FAIL: actual disk entries {} != disk_count {}",
                actual_count, disk_count,
            );
            ok = false;
        }

        // Check page_index length consistency.
        let expected_pages = disk_count.div_ceil(FPS_PER_PAGE);
        if page_index.len() != expected_pages {
            eprintln!(
                "[check_invariant] FAIL: page_index len {} != expected {} (disk_count={}, fps_per_page={})",
                page_index.len(), expected_pages, disk_count, FPS_PER_PAGE,
            );
            ok = false;
        }

        Ok(ok)
    }

    /// Collect all fingerprints from disk pages.
    ///
    /// Returns the combined set of primary (unflushed) and disk (evicted) fingerprints.
    /// Used for checkpointing, not hot path.
    pub(super) fn collect_all_fingerprints(&self) -> Result<Vec<Fingerprint>, StorageFault> {
        // Collect unflushed entries from primary (flushed entries are on disk).
        let primary_fps: Vec<Fingerprint> = self
            .primary
            .collect_all()
            .into_iter()
            .map(Fingerprint)
            .collect();

        let disk_count = self.disk_count.load(Ordering::Acquire);
        if disk_count == 0 {
            return Ok(primary_fps);
        }

        // Read all fingerprints from the sorted disk file.
        let file_len = self.disk_file_len.load(Ordering::Acquire);
        let mut disk_fps = Vec::with_capacity(disk_count);
        let mut session = self
            .disk_reader_pool
            .checkout()
            .map_err(|e: std::io::Error| {
                StorageFault::new("disk", "collect_fingerprints", e.to_string())
            })?;

        let total_pages = (file_len as usize).div_ceil(PAGE_SIZE);
        for page in 0..total_pages {
            let bytes = session
                .read_page_exact(page, file_len)
                .map_err(|e: std::io::Error| {
                    StorageFault::new("disk", "collect_fingerprints", e.to_string())
                })?;
            for chunk in bytes.chunks_exact(FINGERPRINT_BYTES) {
                let raw = u64::from_le_bytes(
                    chunk
                        .try_into()
                        .expect("invariant: chunks_exact guarantees 8-byte chunks"),
                );
                disk_fps.push(Fingerprint(raw));
            }
        }

        // Concatenate primary (unflushed) + disk (evicted). No overlap.
        disk_fps.extend(primary_fps);
        Ok(disk_fps)
    }
}
