// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `FuncBuilder` and `FuncValue` — general function type implementations.
//!
//! `IntIntervalFunc` has been extracted to `int_interval_func.rs` as part of #3309.
//! Struct declarations co-located with impls as part of #3332.

mod accessors;
mod builder;
mod compare;
mod core;
mod overlay;

use super::Value;
use std::sync::atomic::AtomicU64;
use std::sync::{Arc, OnceLock};

/// Sentinel value for "fingerprint not yet computed" in AtomicU64 caches.
/// Matches SortedSet's SORTED_SET_FP_UNSET. A real fingerprint of u64::MAX
/// is astronomically unlikely (1 in 2^64) and an accepted trade-off.
/// Part of #3294.
pub(crate) const FP_UNSET: u64 = u64::MAX;

/// Source of a value taken by [`FuncValue::take_at`].
/// Tells [`FuncValue::restore_at`] whether to put the replacement back into
/// the overlay (preserving lazy representation) or into the base values array.
/// Part of #3386.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FuncTakeSource {
    /// Value came from the base values array.
    Base,
    /// Value came from the lazy EXCEPT overlay.
    Overlay,
}

/// Convert an optional fingerprint to the AtomicU64 representation.
/// `None` maps to `FP_UNSET`, `Some(fp)` maps to `fp`.
#[inline]
fn additive_cache_val(fp: Option<u64>) -> u64 {
    fp.unwrap_or(FP_UNSET)
}

// === Interval length utility ===

/// Compute the length of an inclusive integer interval `[min, max]` with overflow checking.
///
/// Returns `Some(0)` for inverted intervals (`max < min`).
/// Returns `None` if the length overflows `usize` (e.g., `[i64::MIN, i64::MAX]`).
pub fn checked_interval_len(min: i64, max: i64) -> Option<usize> {
    if max < min {
        return Some(0);
    }
    // max >= min, but max - min can still overflow i64 (e.g., i64::MAX - i64::MIN)
    let diff = max.checked_sub(min)?;
    let len = diff.checked_add(1)?;
    usize::try_from(len).ok()
}

/// A TLA+ function value
///
/// Functions in TLA+ are total mappings from a domain set to values.
/// [x \in S |-> e] creates a function with domain S.
///
/// Internally stores domain keys and mapped values in separate arrays.
/// The domain stays immutable and shared across EXCEPT operations, while the
/// values array uses copy-on-write (COW) updates.
///
/// This matches TLC's split `domain` / `values` layout closely enough to avoid
/// cloning unchanged keys on EXCEPT-heavy workloads. Part of #3337.
///
/// Part of #3371: Lazy EXCEPT overlay. Instead of cloning the entire values
/// array on each EXCEPT, modifications are accumulated in a small overlay.
/// The overlay is materialized on demand (comparison, normalization, direct
/// slice access). In BFS, most successor states are fingerprinted and stored
/// without ever materializing — eliminating the O(n) values clone entirely.
pub struct FuncValue {
    /// Domain keys sorted by `Value::cmp`.
    /// Invariant: keys are unique and sorted.
    domain: Arc<[Value]>,
    /// Values positionally aligned with `domain`.
    /// Uses `Arc<Vec<...>>` to enable `Arc::make_mut` COW in `except()`.
    values: Arc<Vec<Value>>,
    /// Lazy EXCEPT overlay: (position_index, replacement_value) pairs.
    /// When non-empty, the logical value at position `i` is:
    ///   overrides.last(|(idx, _)| idx == i).value  OR  values[i]
    /// Last wins for duplicate indices (matches TLA+ EXCEPT semantics).
    /// Part of #3371.
    // Box keeps Option at 8 bytes (pointer-sized) vs 24 bytes for Option<Vec>,
    // saving 16 bytes per FuncValue — a hot allocation target.
    #[allow(clippy::box_collection)]
    overrides: Option<Box<Vec<(usize, Value)>>>,
    /// Cached commutative (additive) fingerprint for state-level dedup.
    ///
    /// Part of #3168: Unlike FP64 (sequential rolling hash), this uses wrapping
    /// addition of mixed per-entry hashes. This is COMMUTATIVE, so:
    /// 1. Unchanged nested values can use their cached additive_fp (O(1) lookup)
    /// 2. EXCEPT operations can update incrementally in O(1)
    ///
    /// This reduces function fingerprinting from O(total_entries_all_levels) to
    /// O(entries_at_modified_levels) — critical for nested EXCEPT patterns like
    /// `[snapshotStore EXCEPT ![t][k] = v]`.
    ///
    /// Part of #3285: `cached_fp` (FP64) removed — recomputed on demand.
    additive_fp: AtomicU64,
    /// Lazily-computed TLC-normalized domain index order.
    /// For homogeneous-safe domains (Bool/Int), the stored order already
    /// matches TLC order and this field is never populated.
    /// For non-safe domains (String, ModelValue, Tuple, Set), computed on first
    /// TLC comparison/fingerprint and cached as indices into `domain`/`values`.
    /// Part of #1434: TLC's `isNorm` flag equivalent for immutable FuncValue.
    tlc_normalized: OnceLock<Arc<[usize]>>,
}

/// Builder for constructing FuncValue incrementally.
///
/// Collects key-value pairs and sorts them when building the final FuncValue.
pub struct FuncBuilder {
    entries: Vec<(Value, Value)>,
}
