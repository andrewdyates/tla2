// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Memory-mapped fingerprint set for scalable state space exploration.
//!
//! Uses open addressing with linear probing:
//! - Each slot stores a 64-bit fingerprint
//! - Empty slots contain the value `0` (fingerprint 0 is special-cased)
//! - On collision, probe linearly up to `MAX_PROBE` slots
//!
//! # Thread Safety
//!
//! The implementation uses atomic operations for concurrent access:
//! - `insert()` uses compare-and-swap to safely insert
//! - `contains()` uses atomic load with acquire ordering
//! - Multiple threads can safely insert/query simultaneously

use memmap2::MmapMut;
use std::io;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicUsize};
use tempfile::NamedTempFile;

pub(crate) mod huge_pages;
mod maintenance;
mod ops;
mod trait_impl;

/// Memory-mapped fingerprint set for scalable state space exploration.
///
/// Stores fingerprints in a memory-mapped array, letting the OS page
/// to disk when the state space exceeds available RAM.
pub struct MmapFingerprintSet {
    /// The memory-mapped array of fingerprints
    pub(super) mmap: MmapMut,
    /// Capacity (number of slots)
    pub(in crate::storage::mmap) capacity: usize,
    /// Number of entries (approximate, may lag slightly in concurrent use)
    pub(in crate::storage::mmap) count: AtomicUsize,
    /// Backing file (kept open to prevent deletion; never read, underscore suppresses warning)
    _backing_file: Option<NamedTempFile>,
    /// Load factor threshold (when count/capacity exceeds this, table is "full")
    pub(in crate::storage::mmap) max_load_factor: f64,
    /// Error flag - set when an insert fails due to table overflow
    pub(in crate::storage::mmap) has_error: AtomicBool,
    /// Number of fingerprints that were dropped due to table overflow
    pub(in crate::storage::mmap) dropped_count: AtomicUsize,
    /// Fix #1535: Separate flag for Fingerprint(0), which cannot be stored in the
    /// mmap array since 0 is the EMPTY sentinel. This replaces the previous
    /// FP_ZERO_ENCODING scheme that conflated FP(0) and FP(u64::MAX).
    pub(in crate::storage::mmap) has_zero: AtomicBool,
    /// Whether this mapping was created through the huge-pages constructor.
    ///
    /// The OS advisory itself is best-effort, but the requested storage mode
    /// must survive backend-preserving resets so recreated tables reissue the
    /// same hint instead of silently degrading to plain mmap.
    huge_pages_requested: bool,
}

impl MmapFingerprintSet {
    /// Create a new memory-mapped fingerprint set.
    ///
    /// # Arguments
    ///
    /// * `capacity` - Maximum number of fingerprints to store. This determines
    ///   the size of the memory-mapped region (capacity * 8 bytes).
    /// * `backing_dir` - If `Some(path)`, create a file-backed mapping in this
    ///   directory. If `None`, use anonymous mapping (in-memory only).
    ///
    /// # Returns
    ///
    /// Returns the new set, or an I/O error if mapping fails.
    ///
    /// # Panics
    ///
    /// Panics if capacity is 0.
    pub fn new(capacity: usize, backing_dir: Option<PathBuf>) -> io::Result<Self> {
        assert!(capacity > 0, "capacity must be non-zero");

        let byte_size = capacity
            .checked_mul(8) // 8 bytes per u64
            .ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("fingerprint set capacity overflow: {capacity} * 8 exceeds usize"),
                )
            })?;

        let (mmap, backing_file) = if let Some(dir) = backing_dir {
            // File-backed mapping
            let file = NamedTempFile::new_in(dir)?;
            file.as_file().set_len(byte_size as u64)?;
            // SAFETY: the file is resized to `byte_size` above and the temp file
            // handle is retained in `_backing_file` for the mapping lifetime.
            let mmap = unsafe { MmapMut::map_mut(file.as_file())? };
            (mmap, Some(file))
        } else {
            // Anonymous mapping (in-memory)
            let mmap = MmapMut::map_anon(byte_size)?;
            (mmap, None)
        };

        Ok(MmapFingerprintSet {
            mmap,
            capacity,
            count: AtomicUsize::new(0),
            _backing_file: backing_file,
            max_load_factor: 0.75,
            has_error: AtomicBool::new(false),
            dropped_count: AtomicUsize::new(0),
            has_zero: AtomicBool::new(false),
            huge_pages_requested: false,
        })
    }

    /// Create a new memory-mapped fingerprint set with huge page hints.
    ///
    /// Identical to [`Self::new`] but additionally requests the OS to back
    /// the mapping with huge pages (2MB) for reduced TLB pressure. Falls back
    /// gracefully to regular pages if huge pages are unavailable.
    ///
    /// Part of #3856: Memory-Mapped State Table with Huge Pages.
    pub fn new_with_huge_pages(capacity: usize, backing_dir: Option<PathBuf>) -> io::Result<Self> {
        let mut set = Self::new(capacity, backing_dir)?;
        set.huge_pages_requested = true;

        // Best-effort: request huge pages via madvise. Failure is non-fatal.
        let ptr = set.mmap.as_mut_ptr();
        let len = set.mmap.len();
        match huge_pages::advise_huge_pages(ptr, len) {
            Ok(true) => {
                // Hint accepted by the OS
            }
            Ok(false) => {
                // Huge pages not available on this platform/config -- using regular pages
            }
            Err(e) => {
                // Log but don't fail: huge pages are a performance hint, not required.
                eprintln!("Warning: huge page advisory failed (non-fatal): {e}");
            }
        }

        Ok(set)
    }

    /// Create a new set with custom load factor.
    ///
    /// The load factor determines when the table is considered "full".
    /// Default is 0.75 (75% full).
    pub fn with_load_factor(
        capacity: usize,
        backing_dir: Option<PathBuf>,
        load_factor: f64,
    ) -> io::Result<Self> {
        let mut set = Self::new(capacity, backing_dir)?;
        set.max_load_factor = load_factor;
        Ok(set)
    }

    pub(crate) fn recreate_empty(&self) -> io::Result<Self> {
        let backing_dir = self
            ._backing_file
            .as_ref()
            .and_then(|file| file.path().parent())
            .map(std::path::Path::to_path_buf);
        let mut fresh = if self.huge_pages_requested {
            Self::new_with_huge_pages(self.capacity, backing_dir)?
        } else {
            Self::new(self.capacity, backing_dir)?
        };
        fresh.max_load_factor = self.max_load_factor;
        Ok(fresh)
    }

    #[cfg(test)]
    pub(crate) fn huge_pages_requested(&self) -> bool {
        self.huge_pages_requested
    }
}
