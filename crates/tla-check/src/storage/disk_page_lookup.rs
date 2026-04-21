// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Page-level disk lookup and interpolated search for [`DiskFingerprintSet`].
//!
//! Extracted from `disk.rs` to keep the main struct file under the 500-line
//! threshold. Contains the disk lookup hot path: page-index interpolated
//! search and within-page interpolated search.

use std::io;
use std::sync::atomic::Ordering;

use super::contracts::{LookupOutcome, StorageFault};
use super::disk::DiskFingerprintSet;
use super::disk_search::{interpolate_mid, IntervalKind, FINGERPRINT_BYTES};
use crate::state::Fingerprint;

impl DiskFingerprintSet {
    /// Record a disk I/O error encountered during lookup.
    pub(super) fn record_disk_error(&self, context: &'static str, err: &io::Error) {
        let previous_errors = self.disk_error_count.fetch_add(1, Ordering::Relaxed);
        // Log the first failure to avoid flooding stderr under repeated lookups.
        if previous_errors == 0 {
            eprintln!(
                "Warning: DiskFingerprintSet {} failed with I/O error: {}. \
                 Subsequent results may be incomplete.",
                context, err
            );
        }
    }

    /// Lookup a fingerprint on disk using interpolated search with typed faults.
    ///
    /// Uses interpolated binary search over the page index (TLC parity:
    /// `DiskFPSet.java:383-432`), then delegates to [`search_disk_page`] for
    /// within-page interpolated search.
    ///
    /// Part of #2430: replaces standard `binary_search` with interpolated search.
    pub(super) fn disk_lookup_checked(&self, fp: Fingerprint) -> LookupOutcome {
        let index = self.page_index.read();
        if index.is_empty() {
            return LookupOutcome::Absent;
        }

        self.disk_lookups.fetch_add(1, Ordering::Relaxed);

        let target = fp.0;
        let n = index.len();

        // Boundary: target below first page.
        if target < index[0] {
            return LookupOutcome::Absent;
        }

        // Determine candidate page via interpolated search over page index.
        let page = if n == 1 {
            // Single page: target >= index[0], search page 0.
            0
        } else {
            let last = n - 1;
            if target >= index[last] {
                if target == index[last] {
                    // Exact match on last page boundary.
                    self.disk_hits.fetch_add(1, Ordering::Relaxed);
                    return LookupOutcome::Present;
                }
                // Beyond last page boundary: target may be on the last page.
                last
            } else {
                // Interpolated search: invariant index[lo] <= target < index[hi].
                let mut lo = 0usize;
                let mut hi = last;
                while lo + 1 < hi {
                    let mid =
                        interpolate_mid(lo, hi, index[lo], index[hi], target, IntervalKind::Open)
                            .unwrap_or_else(|| lo + (hi - lo) / 2);
                    match target.cmp(&index[mid]) {
                        std::cmp::Ordering::Less => hi = mid,
                        std::cmp::Ordering::Greater => lo = mid,
                        std::cmp::Ordering::Equal => {
                            // Exact match on page boundary.
                            self.disk_hits.fetch_add(1, Ordering::Relaxed);
                            return LookupOutcome::Present;
                        }
                    }
                }
                lo
            }
        };

        // Search within the candidate page.
        match self.search_disk_page(page, fp) {
            Ok(found) => {
                if found {
                    self.disk_hits.fetch_add(1, Ordering::Relaxed);
                    LookupOutcome::Present
                } else {
                    LookupOutcome::Absent
                }
            }
            Err(err) => {
                self.record_disk_error("search_disk_page", &err);
                LookupOutcome::StorageFault(StorageFault::new("disk", "contains", err.to_string()))
            }
        }
    }

    /// Search within a specific disk page for a fingerprint.
    ///
    /// Uses interpolated binary search over the decoded page buffer entries
    /// (TLC parity: `DiskFPSet.java:457-488`, `calculateMidEntry:538-553`).
    /// Boundary values are cached and updated on each probe to avoid redundant
    /// reads, matching TLC's approach.
    ///
    /// Part of #2371 (S1): pooled reader.
    /// Part of #2430: interpolated search replaces standard binary search.
    pub(crate) fn search_disk_page(&self, page: usize, fp: Fingerprint) -> io::Result<bool> {
        let file_len = self.disk_file_len.load(Ordering::Acquire);
        let mut session = self.disk_reader_pool.checkout()?;
        let bytes = session.read_page_exact(page, file_len)?;
        let fps_in_page = bytes.len() / FINGERPRINT_BYTES;

        if fps_in_page == 0 {
            self.disk_reader_pool.return_session(session);
            return Ok(false);
        }

        // Decode a fingerprint entry at the given index within the page buffer.
        let read_entry = |idx: usize| -> u64 {
            let start = idx * FINGERPRINT_BYTES;
            let mut raw = [0u8; FINGERPRINT_BYTES];
            raw.copy_from_slice(&bytes[start..start + FINGERPRINT_BYTES]);
            u64::from_le_bytes(raw)
        };

        let target = fp.0;
        let mut lo = 0usize;
        let mut hi = fps_in_page;
        // Cache boundary values for interpolation (TLC pattern: avoids
        // re-reading boundary entries each iteration). After narrowing,
        // lo_val/hi_val are approximate lower/upper bounds — this is sound
        // because the entries are sorted, so the actual boundary value is
        // always >= lo_val and <= hi_val respectively.
        let mut lo_val = read_entry(0);
        let mut hi_val = read_entry(fps_in_page - 1);

        while lo < hi {
            let mid = interpolate_mid(lo, hi, lo_val, hi_val, target, IntervalKind::HalfOpen)
                .unwrap_or_else(|| lo + (hi - lo) / 2);

            let mid_fp = read_entry(mid);
            match mid_fp.cmp(&target) {
                std::cmp::Ordering::Less => {
                    lo = mid + 1;
                    lo_val = mid_fp;
                }
                std::cmp::Ordering::Greater => {
                    hi = mid;
                    hi_val = mid_fp;
                }
                std::cmp::Ordering::Equal => {
                    self.disk_reader_pool.return_session(session);
                    return Ok(true);
                }
            }
        }

        self.disk_reader_pool.return_session(session);
        Ok(false)
    }

    /// Invalidate all cached disk reader sessions, forcing reopen on next
    /// lookup. Test-only: production code relies on epoch-based invalidation
    /// via `publish_eviction_file`.
    #[cfg(test)]
    pub(crate) fn invalidate_disk_readers_for_test(&self) {
        self.disk_reader_pool.advance_epoch();
    }
}
