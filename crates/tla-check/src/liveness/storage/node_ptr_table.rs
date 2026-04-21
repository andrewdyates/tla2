// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Mmap-backed node pointer table for disk-backed liveness graphs.
//!
//! Maps `(Fingerprint, tableau_idx)` composite keys to `u64` node record
//! offsets. This is the TLA2 equivalent of TLC's `TableauNodePtrTable`.
//!
//! # Layout
//!
//! Each entry is 24 bytes (3 × u64):
//! - Word 0: encoded fingerprint (EMPTY=0 sentinel, MSB reserved)
//! - Word 1: tableau index as u64 (meaningful only when fp ≠ EMPTY)
//! - Word 2: node record offset
//!
//! Open-addressing with linear probing. The composite key hash combines
//! state fingerprint and tableau index for probe start position.
//!
//! # Design notes
//!
//! - Not concurrent: liveness graph construction is sequential (single-threaded
//!   BFS + SCC post-pass). If parallelism is added later, atomics are needed.
//! - FP(0) is handled via a separate small Vec, matching the existing pattern
//!   in `storage/trace.rs` and the `storage/mmap/` directory module.
//! - Reuses `encode_fingerprint` / `EMPTY` / `FP_MASK` from `storage/open_addressing.rs`.
//!
//! Part of #2732 Slice C.

use crate::state::Fingerprint;
use crate::storage::open_addressing::{encode_fingerprint, EMPTY, FP_MASK, MAX_PROBE};
use memmap2::MmapMut;
use std::io;
use std::path::PathBuf;
use tempfile::NamedTempFile;

/// Entry size: 24 bytes (3 × u64).
const ENTRY_SIZE: usize = 24;

/// Number of u64 words per entry.
const WORDS_PER_ENTRY: usize = 3;

/// Mmap-backed open-addressed table mapping `(Fingerprint, tableau_idx)` → `u64`
/// node offset.
///
/// Designed for the liveness checker's graph node pointer index. Each unique
/// `(state_fp, tableau_idx)` pair gets one slot storing the node record's byte
/// offset in the append-only node record file (Slice D).
pub(crate) struct NodePtrTable {
    /// Memory-mapped array of `(encoded_fp, tidx, offset)` triples.
    mmap: MmapMut,
    /// Number of slots (not bytes).
    capacity: usize,
    /// Number of occupied mmap slots.
    slot_count: usize,
    /// Backing file (kept alive for the mapping lifetime).
    _backing_file: Option<NamedTempFile>,
    /// Maximum load factor before insert fails.
    max_load_factor: f64,
    /// Side-channel for Fingerprint(0) entries. Vec of `(tableau_idx, offset)`.
    /// Typically tiny (≤ tableau node count, usually < 20).
    zero_entries: Vec<(usize, u64)>,
}

impl NodePtrTable {
    /// Create a new node pointer table.
    ///
    /// # Arguments
    ///
    /// * `capacity` - Maximum number of entries (slots).
    /// * `backing_dir` - If `Some(path)`, create a file-backed mapping.
    ///   If `None`, use anonymous mapping (RAM-only).
    pub(crate) fn new(capacity: usize, backing_dir: Option<PathBuf>) -> io::Result<Self> {
        assert!(capacity > 0, "capacity must be non-zero");

        let byte_size = capacity.checked_mul(ENTRY_SIZE).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "node pointer table capacity overflow: {capacity} * {ENTRY_SIZE} exceeds usize"
                ),
            )
        })?;

        let (mmap, backing_file) = if let Some(dir) = backing_dir {
            let file = NamedTempFile::new_in(dir)?;
            file.as_file().set_len(byte_size as u64)?;
            // SAFETY: the file is resized to `byte_size` and `_backing_file`
            // keeps it alive for the mapping lifetime.
            let mmap = unsafe { MmapMut::map_mut(file.as_file())? };
            (mmap, Some(file))
        } else {
            let mmap = MmapMut::map_anon(byte_size)?;
            (mmap, None)
        };

        Ok(Self {
            mmap,
            capacity,
            slot_count: 0,
            _backing_file: backing_file,
            max_load_factor: 0.75,
            zero_entries: Vec::new(),
        })
    }

    /// Read the fingerprint word at `slot_index`.
    #[inline]
    fn fp_word(&self, slot_index: usize) -> u64 {
        debug_assert!(slot_index < self.capacity);
        let offset = slot_index * WORDS_PER_ENTRY;
        let ptr = self.mmap.as_ptr().cast::<u64>();
        // SAFETY: `slot_index < capacity` and the mmap is sized to hold
        // `capacity * WORDS_PER_ENTRY` u64 words. Reading `offset` which is
        // `slot_index * 3` is within bounds.
        unsafe { ptr.add(offset).read() }
    }

    /// Read the tableau-index word at `slot_index`.
    #[inline]
    fn tidx_word(&self, slot_index: usize) -> u64 {
        debug_assert!(slot_index < self.capacity);
        let offset = slot_index * WORDS_PER_ENTRY + 1;
        let ptr = self.mmap.as_ptr().cast::<u64>();
        // SAFETY: same bounds argument as `fp_word`, offset+1 is the second
        // word of the same entry.
        unsafe { ptr.add(offset).read() }
    }

    /// Read the node-offset word at `slot_index`.
    #[inline]
    fn offset_word(&self, slot_index: usize) -> u64 {
        debug_assert!(slot_index < self.capacity);
        let offset = slot_index * WORDS_PER_ENTRY + 2;
        let ptr = self.mmap.as_ptr().cast::<u64>();
        // SAFETY: same bounds argument, offset+2 is the third word.
        unsafe { ptr.add(offset).read() }
    }

    /// Write all three words for a slot.
    #[inline]
    fn write_slot(&mut self, slot_index: usize, encoded_fp: u64, tidx: u64, node_offset: u64) {
        debug_assert!(slot_index < self.capacity);
        let base = slot_index * WORDS_PER_ENTRY;
        let ptr = self.mmap.as_mut_ptr().cast::<u64>();
        // SAFETY: slot is within bounds (same argument as read methods).
        // Single-threaded access guaranteed by &mut self.
        unsafe {
            ptr.add(base).write(encoded_fp);
            ptr.add(base + 1).write(tidx);
            ptr.add(base + 2).write(node_offset);
        }
    }

    /// Compute the primary hash index for a `(fp, tidx)` composite key.
    #[inline]
    fn hash_index(&self, fp: Fingerprint, tidx: usize) -> usize {
        // Multiplicative hash combining both key components.
        let h = (fp.0 & FP_MASK)
            .wrapping_mul(0x9E3779B97F4A7C15)
            .wrapping_add((tidx as u64).wrapping_mul(0x517CC1B727220A95));
        (h as usize) % self.capacity
    }

    /// Insert or update a `(fp, tidx) → node_offset` mapping.
    ///
    /// Returns `Ok(true)` if newly inserted, `Ok(false)` if updated, or
    /// `Err` if the table is too full / probe limit exceeded.
    pub(crate) fn insert(
        &mut self,
        fp: Fingerprint,
        tidx: usize,
        node_offset: u64,
    ) -> Result<bool, NodePtrError> {
        // Handle FP(0) via side-channel.
        if fp.0 & FP_MASK == 0 {
            for entry in &mut self.zero_entries {
                if entry.0 == tidx {
                    entry.1 = node_offset;
                    return Ok(false);
                }
            }
            self.zero_entries.push((tidx, node_offset));
            return Ok(true);
        }

        let encoded = encode_fingerprint(fp);
        let tidx_u64 = tidx as u64;
        let start = self.hash_index(fp, tidx);

        for probe in 0..MAX_PROBE {
            let idx = (start + probe) % self.capacity;
            let slot_fp = self.fp_word(idx);

            if slot_fp == encoded && self.tidx_word(idx) == tidx_u64 {
                // Exact key match — updates must continue to work even when
                // the table has reached its insertion load-factor cap.
                self.write_slot(idx, encoded, tidx_u64, node_offset);
                return Ok(false);
            }

            if slot_fp == EMPTY {
                if self.slot_count as f64 / self.capacity as f64 >= self.max_load_factor {
                    return Err(NodePtrError::TableFull {
                        count: self.slot_count,
                        capacity: self.capacity,
                    });
                }
                // Claim empty slot.
                self.write_slot(idx, encoded, tidx_u64, node_offset);
                self.slot_count += 1;
                return Ok(true);
            }

            // Different key — continue probing.
        }

        Err(NodePtrError::ProbeExceeded {
            fp,
            tidx,
            probes: MAX_PROBE,
        })
    }

    /// Look up the node offset for a `(fp, tidx)` key.
    pub(crate) fn get(&self, fp: Fingerprint, tidx: usize) -> Option<u64> {
        // FP(0) side-channel.
        if fp.0 & FP_MASK == 0 {
            return self.zero_entries.iter().find(|e| e.0 == tidx).map(|e| e.1);
        }

        let encoded = encode_fingerprint(fp);
        let tidx_u64 = tidx as u64;
        let start = self.hash_index(fp, tidx);

        for probe in 0..MAX_PROBE {
            let idx = (start + probe) % self.capacity;
            let slot_fp = self.fp_word(idx);

            if slot_fp == EMPTY {
                return None;
            }

            if slot_fp == encoded && self.tidx_word(idx) == tidx_u64 {
                return Some(self.offset_word(idx));
            }
        }

        None
    }

    /// Check if a `(fp, tidx)` key is present.
    pub(crate) fn contains(&self, fp: Fingerprint, tidx: usize) -> bool {
        self.get(fp, tidx).is_some()
    }

    /// Number of entries in the table.
    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.slot_count + self.zero_entries.len()
    }

    /// Check if the table is empty.
    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        self.slot_count == 0 && self.zero_entries.is_empty()
    }

    /// Current load factor.
    #[cfg(test)]
    pub(crate) fn load_factor(&self) -> f64 {
        self.slot_count as f64 / self.capacity as f64
    }

    /// Flush mmap writes to disk.
    #[cfg(test)]
    pub(crate) fn flush(&self) -> io::Result<()> {
        self.mmap.flush()
    }
}

/// Errors from node pointer table operations.
#[derive(Debug, Clone)]
pub(crate) enum NodePtrError {
    /// Table load factor exceeded.
    TableFull { count: usize, capacity: usize },
    /// Maximum probe distance exceeded for a key.
    ProbeExceeded {
        fp: Fingerprint,
        tidx: usize,
        probes: usize,
    },
}

impl std::fmt::Display for NodePtrError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NodePtrError::TableFull { count, capacity } => {
                write!(
                    f,
                    "node pointer table full: {count} entries, {capacity} capacity"
                )
            }
            NodePtrError::ProbeExceeded { fp, tidx, probes } => {
                write!(f, "exceeded {probes} probes inserting ({fp}, tidx={tidx})")
            }
        }
    }
}

impl std::error::Error for NodePtrError {}

#[cfg(test)]
#[path = "node_ptr_table_tests.rs"]
mod tests;
