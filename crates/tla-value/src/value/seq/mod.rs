// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TLA+ sequence values with cached fingerprints.
//!
//! Decomposed from the monolithic `seq.rs` as part of #3435.
//! Submodules host focused `impl SeqValue` blocks:
//!
//! - `core`: construction, accessors, iteration, persistent O(log n) ops
//! - `cache`: flat-view materialization, fingerprint caching, mutation helpers
//! - `traits`: Clone, Eq/Ord/Hash, Debug, From, IntoIterator, etc.

mod cache;
mod core;
mod traits;

use std::sync::atomic::AtomicU64;
use std::sync::{Arc, OnceLock};
use tla_core::kani_types::Vector;

use super::Value;

/// Sentinel value indicating no cached fingerprint.
pub(super) const SEQ_VALUE_FP_UNSET: u64 = u64::MAX;

/// A TLA+ sequence value with cached fingerprint.
///
/// Similar to Tuple but with fingerprint caching for performance.
/// Sequences are 1-indexed in TLA+, but stored as 0-indexed internally.
pub struct SeqValue {
    pub(super) elements: Vector<Value>,
    /// Cached commutative (additive) fingerprint for state-level dedup.
    ///
    /// Part of #3196: Separates additive and FP64 caching to avoid first-writer-wins
    /// aliasing between the two algorithms.
    /// Part of #3285: `cached_fp` (FP64) removed — recomputed on demand.
    pub(super) additive_fp: AtomicU64,
    /// Lazily materialized contiguous snapshot for compare/hash/equality hot paths.
    pub(super) flat_view: OnceLock<Arc<[Value]>>,
}
