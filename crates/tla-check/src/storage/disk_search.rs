// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interpolated search helper and disk-page constants for fingerprint storage.
//!
//! This is a leaf module with no dependency on [`super::disk::DiskFingerprintSet`].
//! Both `disk.rs` and `disk_lookup.rs` consume these constants and the search
//! helper, so extracting them here cleans up the dependency graph.

// ============================================================================
// Constants
// ============================================================================

/// Serialized fingerprint width (u64) in bytes.
/// pub(crate): re-exported via storage.rs for storage_tests/ access.
pub(crate) const FINGERPRINT_BYTES: usize = std::mem::size_of::<u64>();

/// Number of fingerprints per disk page (8KB pages, 8 bytes per FP).
/// pub(crate): re-exported via storage.rs for storage_tests/ access.
pub(crate) const FPS_PER_PAGE: usize = 1024;

/// Page size in bytes.
pub(super) const PAGE_SIZE: usize = FPS_PER_PAGE * FINGERPRINT_BYTES;

// ============================================================================
// Interpolated search helper
// ============================================================================

/// Interval semantics for interpolated midpoint computation.
///
/// Page-level search operates on a strict open interval (the boundaries are
/// known page-index entries), while entry-level search within a page uses a
/// half-open interval (lo is a candidate, hi is exclusive).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum IntervalKind {
    /// Strict open interval: result in `(lo, hi)`, clamped to `[lo+1, hi-1]`.
    /// Used by page-index interpolated search.
    Open,
    /// Half-open interval: result in `[lo, hi)`, clamped to `[lo, hi-1]`.
    /// Used by within-page entry-level search.
    HalfOpen,
}

/// Compute interpolated midpoint for binary search over sorted `u64` values.
///
/// Uses `u128` arithmetic to avoid precision loss on `u64` fingerprint values.
/// Returns `Some(mid)` in the interval determined by `kind`, or `None` when
/// the interval is too narrow, values are non-distinct, or the target is at or
/// beyond the boundary values.
///
/// Provides the TLC-style progress guarantee: result is always clamped within
/// the valid range for the given interval kind.
///
/// TLC reference: `DiskFPSet.java:413-416` (page index), `DiskFPSet.java:538-550`
/// (entry-level). This helper generalizes both with integer arithmetic.
pub(super) fn interpolate_mid(
    lo_idx: usize,
    hi_idx: usize,
    lo_val: u64,
    hi_val: u64,
    target: u64,
    kind: IntervalKind,
) -> Option<usize> {
    // Common preconditions: distinct boundary values, target strictly interior.
    if hi_val <= lo_val || target <= lo_val || target >= hi_val {
        return None;
    }

    let (base, range_idx, clamp_lo, clamp_hi) = match kind {
        IntervalKind::Open => {
            // Need at least 2 positions apart for a strict interior midpoint.
            if hi_idx <= lo_idx + 1 {
                return None;
            }
            (
                lo_idx + 1,
                (hi_idx - lo_idx - 1) as u128,
                lo_idx + 1,
                hi_idx - 1,
            )
        }
        IntervalKind::HalfOpen => {
            // Need hi - lo > 2 for interpolation to improve over simple midpoint.
            if hi_idx <= lo_idx + 2 {
                return None;
            }
            (lo_idx, (hi_idx - 1 - lo_idx) as u128, lo_idx, hi_idx - 1)
        }
    };

    // u128 arithmetic: mid = base + range_idx * (target - lo_val) / (hi_val - lo_val)
    let range_val = (hi_val - lo_val) as u128;
    let offset = (target - lo_val) as u128;
    let mid = base + (range_idx * offset / range_val) as usize;
    // Clamp into valid range — TLC-style "mid != hi" guard generalized.
    Some(mid.max(clamp_lo).min(clamp_hi))
}
