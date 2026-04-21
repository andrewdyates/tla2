// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Trace location storage for state space trace reconstruction.
//!
//! Maps state fingerprints to their trace file offsets, enabling
//! counterexample reconstruction after a property violation is found.

use crate::state::Fingerprint;
use memmap2::MmapMut;
use std::io;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};

use tempfile::NamedTempFile;

use super::open_addressing::{encode_fingerprint, MmapError, EMPTY, FP_MASK, MAX_PROBE};

/// Entry size for trace locations: 16 bytes (8 bytes fingerprint + 8 bytes offset).
pub(crate) const TRACE_ENTRY_SIZE: usize = 16;

/// Memory-mapped trace location storage for scalable trace file mode.
///
/// Stores (fingerprint, offset) pairs for trace reconstruction using
/// open addressing with linear probing. Each slot is 16 bytes:
/// 8 bytes fingerprint + 8 bytes offset. Uses atomic operations for
/// the fingerprint field to allow concurrent reads.
pub struct MmapTraceLocations {
    /// The memory-mapped array of (fingerprint, offset) pairs
    pub(super) mmap: MmapMut,
    /// Capacity (number of slots)
    capacity: usize,
    /// Number of entries
    count: AtomicUsize,
    /// Backing file (kept open to prevent deletion; never read, underscore suppresses warning)
    _backing_file: Option<NamedTempFile>,
    /// Load factor threshold
    max_load_factor: f64,
    /// Fix #1535: Separate storage for Fingerprint(0) (see MmapFingerprintSet).
    has_zero: AtomicBool,
    /// Trace offset for Fingerprint(0) when present.
    zero_offset: AtomicU64,
}

impl MmapTraceLocations {
    /// Create a new memory-mapped trace location storage.
    ///
    /// # Arguments
    ///
    /// * `capacity` - Maximum number of entries. The storage will use
    ///   `capacity * 16` bytes.
    /// * `backing_dir` - If `Some(path)`, create a file-backed mapping.
    ///   If `None`, use anonymous mapping.
    ///
    /// # Returns
    ///
    /// Returns the new storage, or an I/O error if mapping fails.
    pub fn new(capacity: usize, backing_dir: Option<PathBuf>) -> io::Result<Self> {
        assert!(capacity > 0, "capacity must be non-zero");

        let byte_size = capacity
            .checked_mul(TRACE_ENTRY_SIZE)
            .ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("trace locations capacity overflow: {capacity} * {TRACE_ENTRY_SIZE} exceeds usize"),
                )
            })?;

        let (mmap, backing_file) = if let Some(dir) = backing_dir {
            // File-backed mapping
            let file = NamedTempFile::new_in(dir)?;
            file.as_file().set_len(byte_size as u64)?;
            // SAFETY: the file is resized to `byte_size` above and `_backing_file`
            // keeps the backing file alive for the mapping lifetime.
            let mmap = unsafe { MmapMut::map_mut(file.as_file())? };
            (mmap, Some(file))
        } else {
            // Anonymous mapping
            let mmap = MmapMut::map_anon(byte_size)?;
            (mmap, None)
        };

        Ok(MmapTraceLocations {
            mmap,
            capacity,
            count: AtomicUsize::new(0),
            _backing_file: backing_file,
            max_load_factor: 0.75,
            has_zero: AtomicBool::new(false),
            zero_offset: AtomicU64::new(0),
        })
    }

    /// Create with custom load factor.
    pub fn with_load_factor(
        capacity: usize,
        backing_dir: Option<PathBuf>,
        load_factor: f64,
    ) -> io::Result<Self> {
        let mut locs = Self::new(capacity, backing_dir)?;
        locs.max_load_factor = load_factor;
        Ok(locs)
    }

    /// Get a reference to the fingerprint slot at the given index as AtomicU64.
    #[inline]
    fn fp_slot(&self, index: usize) -> &AtomicU64 {
        assert!(
            index < self.capacity,
            "fp_slot index {index} out of bounds (capacity {})",
            self.capacity
        );
        let ptr = self.mmap.as_ptr().cast::<AtomicU64>();
        // Each entry is 16 bytes = 2 u64s. Fingerprint is first.
        // SAFETY: `index < capacity` is enforced by the assert above and each
        // slot consumes exactly two contiguous `u64` words in the mmap region.
        #[allow(clippy::cast_ptr_alignment)]
        unsafe {
            &*ptr.add(index * 2)
        }
    }

    /// Get a mutable reference to the offset at the given index.
    ///
    /// # Safety
    ///
    /// Caller must ensure no concurrent writes to the same slot.
    #[inline]
    fn offset_slot(&self, index: usize) -> &AtomicU64 {
        assert!(
            index < self.capacity,
            "offset_slot index {index} out of bounds (capacity {})",
            self.capacity
        );
        let ptr = self.mmap.as_ptr().cast::<AtomicU64>();
        // Each entry is 16 bytes = 2 u64s. Offset is second.
        // SAFETY: `index < capacity` is enforced by the assert above, so
        // `index * 2 + 1` addresses the second word of an in-bounds 2-word entry.
        #[allow(clippy::cast_ptr_alignment)]
        unsafe {
            &*ptr.add(index * 2 + 1)
        }
    }

    /// Compute the primary hash index for a fingerprint.
    #[inline]
    fn hash_index(&self, fp: Fingerprint) -> usize {
        // Mask off MSB (FLUSHED_BIT) so FPs differing only in bit 63 hash
        // to the same probe chain — matches encode_fingerprint (#2674).
        let h = (fp.0 & FP_MASK).wrapping_mul(0x9E3779B97F4A7C15);
        (h as usize) % self.capacity
    }

    /// Insert a fingerprint-to-offset mapping.
    ///
    /// # Arguments
    ///
    /// * `fp` - The fingerprint to map
    /// * `offset` - The trace file offset for this fingerprint
    ///
    /// # Returns
    ///
    /// * `Ok(true)` if newly inserted
    /// * `Ok(false)` if fingerprint already present (offset is updated)
    /// * `Err(...)` if table is too full
    pub fn insert(&self, fp: Fingerprint, offset: u64) -> Result<bool, MmapError> {
        // Fix #1535: Handle FP(0) via separate flag.
        if fp.0 & FP_MASK == 0 {
            let was_new = !self.has_zero.swap(true, Ordering::AcqRel);
            self.zero_offset.store(offset, Ordering::Release);
            if was_new {
                self.count.fetch_add(1, Ordering::Relaxed);
            }
            return Ok(was_new);
        }

        // Check load factor
        let current_count = self.count.load(Ordering::Relaxed);
        if current_count as f64 / self.capacity as f64 >= self.max_load_factor {
            return Err(MmapError::TableFull {
                count: current_count,
                capacity: self.capacity,
            });
        }

        let encoded = encode_fingerprint(fp);
        let start_index = self.hash_index(fp);

        for probe in 0..MAX_PROBE {
            let index = (start_index + probe) % self.capacity;
            let fp_slot = self.fp_slot(index);

            let current = fp_slot.load(Ordering::Acquire);

            if current == encoded {
                // Already present - update offset
                self.offset_slot(index).store(offset, Ordering::Release);
                return Ok(false);
            }

            if current == EMPTY {
                // Try to insert via CAS
                match fp_slot.compare_exchange(EMPTY, encoded, Ordering::AcqRel, Ordering::Acquire)
                {
                    Ok(_) => {
                        // Successfully claimed slot - write offset
                        self.offset_slot(index).store(offset, Ordering::Release);
                        self.count.fetch_add(1, Ordering::Relaxed);
                        return Ok(true);
                    }
                    Err(actual) => {
                        if actual == encoded {
                            // Someone else wrote same fingerprint - update offset
                            self.offset_slot(index).store(offset, Ordering::Release);
                            return Ok(false);
                        }
                        // Different fingerprint - continue probing
                    }
                }
            }
        }

        Err(MmapError::ProbeExceeded {
            fp,
            probes: MAX_PROBE,
        })
    }

    /// Get the offset for a fingerprint.
    ///
    /// # Returns
    ///
    /// `Some(offset)` if the fingerprint is present, `None` otherwise.
    pub fn get(&self, fp: &Fingerprint) -> Option<u64> {
        // Fix #1535: FP(0) is tracked via separate flag.
        if fp.0 & FP_MASK == 0 {
            return if self.has_zero.load(Ordering::Acquire) {
                Some(self.zero_offset.load(Ordering::Acquire))
            } else {
                None
            };
        }

        let encoded = encode_fingerprint(*fp);
        let start_index = self.hash_index(*fp);

        for probe in 0..MAX_PROBE {
            let index = (start_index + probe) % self.capacity;
            let fp_slot = self.fp_slot(index);
            let current = fp_slot.load(Ordering::Acquire);

            if current == encoded {
                return Some(self.offset_slot(index).load(Ordering::Acquire));
            }

            if current == EMPTY {
                return None;
            }
        }

        None
    }

    /// Check if a fingerprint is present.
    pub fn contains(&self, fp: &Fingerprint) -> bool {
        self.get(fp).is_some()
    }

    /// Return the number of entries.
    pub fn len(&self) -> usize {
        self.count.load(Ordering::Relaxed)
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Return the capacity.
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Return the current load factor.
    pub fn load_factor(&self) -> f64 {
        self.len() as f64 / self.capacity as f64
    }

    /// Flush pending writes to disk.
    pub fn flush(&self) -> io::Result<()> {
        self.mmap.flush()
    }
}

/// Trait for trace location storage, allowing different implementations.
pub trait TraceLocationStorage: Send + Sync {
    /// Insert a fingerprint-to-offset mapping.
    /// Returns `true` on success, `false` if the insert failed (e.g., mmap table full).
    fn insert(&self, fp: Fingerprint, offset: u64) -> bool;

    /// Get the offset for a fingerprint.
    fn get(&self, fp: &Fingerprint) -> Option<u64>;

    /// Check if a fingerprint is present.
    fn contains(&self, fp: &Fingerprint) -> bool {
        self.get(fp).is_some()
    }

    /// Return the number of entries.
    fn len(&self) -> usize;

    /// Check if empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl TraceLocationStorage for MmapTraceLocations {
    fn insert(&self, fp: Fingerprint, offset: u64) -> bool {
        match MmapTraceLocations::insert(self, fp, offset) {
            Ok(_) => true,
            Err(e) => {
                use std::sync::atomic::AtomicBool;
                static WARNED: AtomicBool = AtomicBool::new(false);
                if !WARNED.swap(true, Ordering::Relaxed) {
                    eprintln!("WARNING: mmap trace location insert failed (counterexample traces may be incomplete): {e}");
                }
                false
            }
        }
    }

    fn get(&self, fp: &Fingerprint) -> Option<u64> {
        MmapTraceLocations::get(self, fp)
    }

    fn len(&self) -> usize {
        MmapTraceLocations::len(self)
    }
}

/// In-memory trace location storage using identity-hashed FpHashMap.
///
/// Part of #4128: Fingerprints are pre-hashed 64-bit values, so identity
/// hashing avoids the redundant FxHash Fibonacci multiplication.
pub struct InMemoryTraceLocations {
    locations: parking_lot::RwLock<crate::state::FpHashMap<u64>>,
}

impl InMemoryTraceLocations {
    /// Create a new in-memory trace location storage.
    pub fn new() -> Self {
        InMemoryTraceLocations {
            locations: parking_lot::RwLock::new(crate::state::fp_hashmap()),
        }
    }
}

impl Default for InMemoryTraceLocations {
    fn default() -> Self {
        Self::new()
    }
}

impl TraceLocationStorage for InMemoryTraceLocations {
    fn insert(&self, fp: Fingerprint, offset: u64) -> bool {
        self.locations.write().insert(fp, offset);
        true
    }

    fn get(&self, fp: &Fingerprint) -> Option<u64> {
        self.locations.read().get(fp).copied()
    }

    fn len(&self) -> usize {
        self.locations.read().len()
    }
}

/// Trace location storage abstraction that supports both in-memory and scalable backends.
///
/// For small state spaces: Use `TraceLocationsStorage::InMemory`.
/// For large state spaces: Use `TraceLocationsStorage::Mmap`.
#[non_exhaustive]
pub enum TraceLocationsStorage {
    /// In-memory hash map (fast, but limited to RAM).
    InMemory(InMemoryTraceLocations),
    /// Memory-mapped file (scales beyond RAM).
    Mmap(MmapTraceLocations),
}

impl TraceLocationsStorage {
    /// Create in-memory storage.
    pub fn in_memory() -> Self {
        TraceLocationsStorage::InMemory(InMemoryTraceLocations::new())
    }

    /// Create memory-mapped storage.
    ///
    /// # Arguments
    ///
    /// * `capacity` - Maximum number of entries.
    /// * `backing_dir` - Optional directory for the backing file.
    pub fn mmap(capacity: usize, backing_dir: Option<PathBuf>) -> io::Result<Self> {
        Ok(TraceLocationsStorage::Mmap(MmapTraceLocations::new(
            capacity,
            backing_dir,
        )?))
    }
}

impl TraceLocationStorage for TraceLocationsStorage {
    fn insert(&self, fp: Fingerprint, offset: u64) -> bool {
        match self {
            TraceLocationsStorage::InMemory(locs) => locs.insert(fp, offset),
            TraceLocationsStorage::Mmap(locs) => {
                <MmapTraceLocations as TraceLocationStorage>::insert(locs, fp, offset)
            }
        }
    }

    fn get(&self, fp: &Fingerprint) -> Option<u64> {
        match self {
            TraceLocationsStorage::InMemory(locs) => locs.get(fp),
            TraceLocationsStorage::Mmap(locs) => locs.get(fp),
        }
    }

    fn len(&self) -> usize {
        match self {
            TraceLocationsStorage::InMemory(locs) => locs.len(),
            TraceLocationsStorage::Mmap(locs) => locs.len(),
        }
    }
}
