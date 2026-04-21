// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `SortedSet` — lazy-normalized set storage for TLA+ values.
//!
//! Extracted from `interning_sets.rs` per #3306 to separate the value type
//! (SortedSet, SetBuilder, value pooling) from the interning table infrastructure
//! (`intern_tables/`).
//!
//! Builder helpers and tests extracted into child modules per #3326.
//! Interval/domain helpers and set algebra extracted to `algebra.rs` per #3408.

mod algebra;
mod builder;
#[cfg(test)]
mod tests;

pub use builder::{val_false, val_int, val_true, SetBuilder};

#[cfg(feature = "memory-stats")]
use super::memory_stats;
use super::Value;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering as AtomicOrdering};
use std::sync::{Arc, OnceLock};

use super::intern_tables::intern_set_array;

// ============================================================================
// SortedSet - Lazy-normalized set storage for performance
// ============================================================================

/// A set of values with a lazily computed sorted, deduplicated view.
///
/// `SortedSet::from_iter()` preserves raw insertion order and defers sorting +
/// deduplication until callers observe the normalized contract via iteration,
/// ordering, hashing, fingerprinting, or cardinality. This keeps hot-path
/// membership checks from paying the normalization cost eagerly. Constructors
/// that already know they are producing sorted, deduplicated output use the
/// normalized representation directly.
///
/// Public accessors continue to expose normalized behavior:
/// - iteration order is ascending by `Value::cmp`
/// - `len()` is the deduplicated cardinality
/// - equality / ordering / hashing are extensional
pub struct SortedSet {
    storage: SetStorage,
    /// Cached additive (commutative) fingerprint for state-level dedup.
    ///
    /// Part of #3246: Uses wrapping addition of splitmix64-mixed element fingerprints.
    /// Unlike FP64, this is COMMUTATIVE and supports O(1) incremental updates when
    /// elements are inserted via `insert()`. Critical for specs with growing message
    /// sets (e.g., PaxosCommit's `msgs \cup {m}` pattern) where FP64 forced O(|set|)
    /// recomputation per successor state.
    ///
    /// Part of #3285: `cached_value_fp` (FP64) removed — FP64 now recomputed on
    /// demand, matching TLC which does not cache per-value fingerprints.
    cached_additive_fp: AtomicU64,
    /// Cached deduplicated element count.
    ///
    /// For `Normalized` storage, this equals the slice length (set eagerly in
    /// constructors). For `Unnormalized` storage, lazily computed via FxHashSet
    /// dedup counting — O(n) with cheap hash — instead of forcing full O(n log n)
    /// normalization (sort + dedup + intern) just to answer `len()` queries.
    /// Sentinel `DEDUP_LEN_UNSET` means not yet computed.
    cached_dedup_len: AtomicUsize,
}

enum SetStorage {
    Normalized(Arc<[Value]>),
    Unnormalized {
        elements: Arc<[Value]>,
        normalized: OnceLock<Arc<[Value]>>,
    },
}

const SORTED_SET_FP_UNSET: u64 = u64::MAX;
const DEDUP_LEN_UNSET: usize = usize::MAX;

/// Empty set singleton for reuse
static EMPTY_SET: std::sync::OnceLock<SortedSet> = std::sync::OnceLock::new();

impl SortedSet {
    #[inline]
    fn from_sorted_vec_canonical(mut vec: Vec<Value>) -> Self {
        if vec.is_empty() {
            return Self::new();
        }
        vec.dedup();
        let dedup_len = vec.len();
        #[cfg(feature = "memory-stats")]
        memory_stats::inc_set();
        let mut set = Self::from_normalized_arc(intern_set_array(vec));
        // We know the exact dedup len at construction time.
        set.cached_dedup_len = AtomicUsize::new(dedup_len);
        set
    }

    #[inline]
    fn from_normalized_arc(elements: Arc<[Value]>) -> Self {
        let dedup_len = elements.len();
        SortedSet {
            storage: SetStorage::Normalized(elements),
            cached_additive_fp: AtomicU64::new(SORTED_SET_FP_UNSET),
            cached_dedup_len: AtomicUsize::new(dedup_len),
        }
    }

    #[inline]
    fn from_unnormalized_vec(elements: Vec<Value>) -> Self {
        SortedSet {
            storage: SetStorage::Unnormalized {
                elements: Arc::from(elements),
                normalized: OnceLock::new(),
            },
            cached_additive_fp: AtomicU64::new(SORTED_SET_FP_UNSET),
            cached_dedup_len: AtomicUsize::new(DEDUP_LEN_UNSET),
        }
    }

    fn normalized_elements_from_raw(elements: &[Value]) -> Arc<[Value]> {
        let mut vec = elements.to_vec();
        vec.sort();
        vec.dedup();
        intern_set_array(vec)
    }

    /// Compute the deduplicated count without sorting.
    ///
    /// Uses FxHashSet for O(n) counting with cheap hash, avoiding the O(n log n)
    /// sort required by full normalization. For small sets (<= 8 elements), uses
    /// a brute-force quadratic scan to avoid HashSet allocation overhead.
    fn compute_dedup_len(elements: &[Value]) -> usize {
        let raw_len = elements.len();
        if raw_len <= 1 {
            return raw_len;
        }
        // Small set fast path: quadratic scan avoids HashSet allocation.
        // For sets of 2-8 elements this is cheaper than hash+alloc overhead.
        if raw_len <= 8 {
            let mut count = 0usize;
            'outer: for (i, elem) in elements.iter().enumerate() {
                for prev in &elements[..i] {
                    if prev == elem {
                        continue 'outer;
                    }
                }
                count += 1;
            }
            return count;
        }
        // Large set: use FxHashSet for O(n) dedup counting.
        // ValueByHash wraps &Value which has interior mutability (AtomicU64 caches),
        // but Hash/Eq impls only read value content, never mutate through the ref.
        #[allow(clippy::mutable_key_type)]
        let mut seen = rustc_hash::FxHashSet::with_capacity_and_hasher(raw_len, Default::default());
        for elem in elements {
            seen.insert(ValueByHash(elem));
        }
        seen.len()
    }

    #[inline]
    pub(crate) fn raw_slice(&self) -> &[Value] {
        match &self.storage {
            SetStorage::Normalized(elements) => elements,
            SetStorage::Unnormalized { elements, .. } => elements,
        }
    }

    /// Iterate over elements in storage order without forcing normalization.
    ///
    /// Internal callers may use this when the result is another extensional
    /// set value that will normalize later.
    #[inline]
    pub(crate) fn raw_iter(&self) -> std::slice::Iter<'_, Value> {
        self.raw_slice().iter()
    }

    /// Check whether this set's storage is already in normalized (sorted+deduped) form.
    ///
    /// Used to choose between O(n+m) sorted merge (when both operands are normalized)
    /// and O(n+m) raw concatenation (when at least one operand is unnormalized).
    #[inline]
    pub(crate) fn is_normalized(&self) -> bool {
        match &self.storage {
            SetStorage::Normalized(_) => true,
            SetStorage::Unnormalized { normalized, .. } => normalized.get().is_some(),
        }
    }

    #[inline]
    fn raw_arc(&self) -> &Arc<[Value]> {
        match &self.storage {
            SetStorage::Normalized(elements) => elements,
            SetStorage::Unnormalized { elements, .. } => elements,
        }
    }

    #[inline]
    fn normalized_slice(&self) -> &[Value] {
        match &self.storage {
            SetStorage::Normalized(elements) => elements,
            SetStorage::Unnormalized {
                elements,
                normalized,
            } => {
                let norm = normalized
                    .get_or_init(|| Self::normalized_elements_from_raw(elements.as_ref()));
                // Backfill cached_dedup_len from the now-known normalized length.
                let _ = self.cached_dedup_len.compare_exchange(
                    DEDUP_LEN_UNSET,
                    norm.len(),
                    AtomicOrdering::Relaxed,
                    AtomicOrdering::Relaxed,
                );
                norm.as_ref()
            }
        }
    }

    #[inline]
    fn normalized_arc(&self) -> Arc<[Value]> {
        match &self.storage {
            SetStorage::Normalized(elements) => Arc::clone(elements),
            SetStorage::Unnormalized {
                elements,
                normalized,
            } => {
                let norm = Arc::clone(
                    normalized.get_or_init(|| Self::normalized_elements_from_raw(elements.as_ref())),
                );
                // Backfill cached_dedup_len from the now-known normalized length.
                let _ = self.cached_dedup_len.compare_exchange(
                    DEDUP_LEN_UNSET,
                    norm.len(),
                    AtomicOrdering::Relaxed,
                    AtomicOrdering::Relaxed,
                );
                norm
            }
        }
    }

    /// Create an empty set
    #[inline]
    pub fn new() -> Self {
        EMPTY_SET
            .get_or_init(|| Self::from_normalized_arc(Arc::from([])))
            .clone()
    }

    /// Create a set from an iterator, deferring normalization until needed.
    #[allow(clippy::should_implement_trait)]
    pub fn from_iter<I: IntoIterator<Item = Value>>(iter: I) -> Self {
        let vec: Vec<Value> = iter.into_iter().collect();
        Self::from_vec(vec)
    }

    /// Create a set from an owned Vec, deferring normalization until needed.
    ///
    /// Part of #3805: Avoids the intermediate collect in `from_iter()` when the
    /// caller already has a Vec (e.g., from `SmallVec::into_vec()`).
    pub fn from_vec(vec: Vec<Value>) -> Self {
        if vec.is_empty() {
            return Self::new();
        }
        #[cfg(feature = "memory-stats")]
        memory_stats::inc_set();
        Self::from_unnormalized_vec(vec)
    }

    /// Create a set from a sorted Vec, without additional sorting
    /// Deduplicates but assumes input is already sorted.
    #[inline]
    pub fn from_sorted_vec(vec: Vec<Value>) -> Self {
        Self::from_sorted_vec_canonical(vec)
    }

    /// Get the deduplicated number of elements.
    ///
    /// Avoids forcing full normalization (O(n log n) sort + dedup + intern) when
    /// only the count is needed. For unnormalized sets, computes the dedup count
    /// via FxHashSet (O(n) with cheap hash) and caches the result. If normalization
    /// has already occurred, returns the normalized slice length directly.
    #[inline]
    pub fn len(&self) -> usize {
        // Fast path: already computed.
        let cached = self.cached_dedup_len.load(AtomicOrdering::Relaxed);
        if cached != DEDUP_LEN_UNSET {
            return cached;
        }
        // If normalization has already occurred, use that length.
        if let SetStorage::Unnormalized { normalized, elements, .. } = &self.storage {
            if let Some(norm) = normalized.get() {
                let len = norm.len();
                let _ = self.cached_dedup_len.compare_exchange(
                    DEDUP_LEN_UNSET,
                    len,
                    AtomicOrdering::Relaxed,
                    AtomicOrdering::Relaxed,
                );
                return len;
            }
            // Compute dedup count without full normalization.
            let len = Self::compute_dedup_len(elements);
            let _ = self.cached_dedup_len.compare_exchange(
                DEDUP_LEN_UNSET,
                len,
                AtomicOrdering::Relaxed,
                AtomicOrdering::Relaxed,
            );
            return len;
        }
        // Normalized storage: should have been set eagerly, but handle defensively.
        let len = match &self.storage {
            SetStorage::Normalized(elements) => elements.len(),
            _ => unreachable!(),
        };
        self.cached_dedup_len.store(len, AtomicOrdering::Relaxed);
        len
    }

    /// Check if empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.raw_slice().is_empty()
    }

    /// Return a single element if this set was constructed from exactly one value.
    ///
    /// Uses raw storage length to detect singletons without forcing normalization.
    /// A raw slice of length 1 is guaranteed to be a singleton (no duplicates
    /// possible with only one element). Returns `None` for empty or multi-element sets.
    #[inline]
    pub fn as_singleton(&self) -> Option<&Value> {
        match self.raw_slice() {
            [elem] => Some(elem),
            _ => None,
        }
    }

    /// Check if the set contains a value.
    ///
    /// Unnormalized sets use a linear scan over raw storage to avoid paying the
    /// sorting cost when the caller only needs membership.
    #[inline]
    pub fn contains(&self, v: &Value) -> bool {
        match &self.storage {
            SetStorage::Normalized(elements) => elements.binary_search(v).is_ok(),
            SetStorage::Unnormalized {
                elements,
                normalized,
            } => normalized.get().map_or_else(
                || elements.iter().any(|elem| elem == v),
                |set| set.binary_search(v).is_ok(),
            ),
        }
    }

    /// Iterate over elements in sorted order.
    #[inline]
    pub fn iter(&self) -> std::slice::Iter<'_, Value> {
        self.normalized_slice().iter()
    }

    /// Get the normalized, sorted slice view.
    #[inline]
    pub fn as_slice(&self) -> &[Value] {
        self.normalized_slice()
    }

    /// Clone and return the normalized Arc<[Value]>.
    /// Part of #129: Used for caching constant domains in CompiledGuard
    #[inline]
    pub fn to_arc_slice(&self) -> Arc<[Value]> {
        self.normalized_arc()
    }

    /// Check raw-storage pointer equality (optimization only).
    #[inline]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(self.raw_arc(), other.raw_arc())
    }

    /// Get first element
    #[inline]
    pub(crate) fn first(&self) -> Option<&Value> {
        self.normalized_slice().first()
    }

    /// Get last element
    #[inline]
    pub(crate) fn last(&self) -> Option<&Value> {
        self.normalized_slice().last()
    }

    /// Get cached additive fingerprint for state dedup if available.
    #[inline]
    pub fn get_additive_fp(&self) -> Option<u64> {
        let cached = self.cached_additive_fp.load(AtomicOrdering::Relaxed);
        (cached != SORTED_SET_FP_UNSET).then_some(cached)
    }

    /// Cache an additive fingerprint for state dedup.
    #[inline]
    pub fn cache_additive_fp(&self, fp: u64) -> u64 {
        let _ = self.cached_additive_fp.compare_exchange(
            SORTED_SET_FP_UNSET,
            fp,
            AtomicOrdering::Relaxed,
            AtomicOrdering::Relaxed,
        );
        fp
    }

    /// Return a stable identity key for the underlying storage Arc.
    ///
    /// Part of #3337: Used by `WorkerFpMemo` to cache fingerprints by
    /// pointer identity without needing `AtomicU64` embedded caches.
    #[inline]
    pub fn storage_ptr_identity(&self) -> usize {
        match &self.storage {
            SetStorage::Normalized(arc) => Arc::as_ptr(arc).cast::<()>() as usize,
            SetStorage::Unnormalized { elements, .. } => {
                Arc::as_ptr(elements).cast::<()>() as usize
            }
        }
    }
}

// ============================================================================
// ValueByHash — wrapper for FxHashSet-based dedup counting without sorting
// ============================================================================

/// Wrapper that implements Hash+Eq for &Value using the standard Hash/PartialEq
/// impls on Value, allowing FxHashSet-based dedup counting without allocating
/// cloned Values.
struct ValueByHash<'a>(&'a Value);

impl<'a> Hash for ValueByHash<'a> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<'a> PartialEq for ValueByHash<'a> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<'a> Eq for ValueByHash<'a> {}

impl Clone for SortedSet {
    fn clone(&self) -> Self {
        let storage = match &self.storage {
            SetStorage::Normalized(elements) => SetStorage::Normalized(Arc::clone(elements)),
            SetStorage::Unnormalized {
                elements,
                normalized,
            } => {
                let cloned_cache = OnceLock::new();
                if let Some(cached) = normalized.get() {
                    let _ = cloned_cache.set(Arc::clone(cached));
                }
                SetStorage::Unnormalized {
                    elements: Arc::clone(elements),
                    normalized: cloned_cache,
                }
            }
        };
        SortedSet {
            storage,
            cached_additive_fp: AtomicU64::new(
                self.cached_additive_fp.load(AtomicOrdering::Relaxed),
            ),
            cached_dedup_len: AtomicUsize::new(
                self.cached_dedup_len.load(AtomicOrdering::Relaxed),
            ),
        }
    }
}

impl Default for SortedSet {
    fn default() -> Self {
        Self::new()
    }
}

impl PartialEq for SortedSet {
    fn eq(&self, other: &Self) -> bool {
        if self.ptr_eq(other) {
            return true;
        }
        // Fast cardinality check: if deduplicated lengths differ, sets differ.
        // This avoids full normalization for the common case where sets have
        // different sizes.
        if self.len() != other.len() {
            return false;
        }
        self.normalized_slice() == other.normalized_slice()
    }
}

impl Eq for SortedSet {}

impl PartialOrd for SortedSet {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SortedSet {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.ptr_eq(other) {
            return Ordering::Equal;
        }
        self.normalized_slice().cmp(other.normalized_slice())
    }
}

impl Hash for SortedSet {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.normalized_slice().hash(state);
    }
}

impl fmt::Debug for SortedSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<'a> IntoIterator for &'a SortedSet {
    type Item = &'a Value;
    type IntoIter = std::slice::Iter<'a, Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl FromIterator<Value> for SortedSet {
    fn from_iter<I: IntoIterator<Item = Value>>(iter: I) -> Self {
        SortedSet::from_iter(iter)
    }
}
