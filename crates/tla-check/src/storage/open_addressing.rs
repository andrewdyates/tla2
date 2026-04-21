// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared open-addressing primitives for mmap-backed storage tables.

use crate::state::Fingerprint;

/// Maximum number of probes before giving up on insert.
/// If exceeded, the table is too full and should be resized.
pub(crate) const MAX_PROBE: usize = 1024;

/// Sentinel value for empty slots.
/// Fingerprint 0 is handled separately via a dedicated `has_zero` flag.
pub(crate) const EMPTY: u64 = 0;

/// MSB reserved as flushed flag (TLC parity: MSBDiskFPSet.MARK_FLUSHED).
/// After eviction, occupied mmap slots are marked with this bit instead of
/// being cleared. This keeps flushed entries as an in-memory lookup cache,
/// avoiding unnecessary disk I/O for recently-evicted fingerprints.
pub(crate) const FLUSHED_BIT: u64 = 1u64 << 63;

/// Mask for the lower 63 bits — the actual fingerprint value.
/// The MSB is reserved for the flushed flag.
pub(crate) const FP_MASK: u64 = !FLUSHED_BIT;

/// Check if an encoded slot value has the flushed flag set.
#[inline]
pub(crate) fn is_flushed(encoded: u64) -> bool {
    encoded & FLUSHED_BIT != 0
}

/// Set the flushed flag on an encoded slot value.
#[inline]
pub(crate) fn mark_flushed(encoded: u64) -> u64 {
    encoded | FLUSHED_BIT
}

/// Encode a fingerprint for storage in open-addressed tables.
///
/// The MSB is masked off (reserved for the flushed flag), reducing the
/// effective fingerprint space from 64 to 63 bits (same as TLC).
///
/// Fingerprints that encode to 0 after masking cannot be stored in table
/// slots because 0 is the EMPTY sentinel. Callers must handle these via
/// a side-channel flag (`has_zero`).
#[inline]
pub(crate) fn encode_fingerprint(fp: Fingerprint) -> u64 {
    let encoded = fp.0 & FP_MASK;
    debug_assert!(
        encoded != 0,
        "FP that encodes to 0 must be handled via has_zero flag, not encoded"
    );
    encoded
}

/// Decode a stored value back to its fingerprint value.
/// Strips the flushed flag if present.
#[inline]
pub(crate) fn decode_fingerprint(encoded: u64) -> u64 {
    let fp = encoded & FP_MASK;
    debug_assert!(fp != 0, "EMPTY sentinel should not be decoded");
    fp
}

/// Errors that can occur during mmap-backed open-addressed table operations.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum MmapError {
    /// The table is too full (load factor exceeded).
    TableFull { count: usize, capacity: usize },
    /// Maximum probe distance exceeded.
    ProbeExceeded { fp: Fingerprint, probes: usize },
}

impl std::fmt::Display for MmapError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MmapError::TableFull { count, capacity } => {
                write!(
                    f,
                    "fingerprint table full: {} entries, {} capacity",
                    count, capacity
                )
            }
            MmapError::ProbeExceeded { fp, probes } => {
                write!(f, "exceeded {} probes inserting fingerprint {}", probes, fp)
            }
        }
    }
}

impl std::error::Error for MmapError {}
