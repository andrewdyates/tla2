// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[cfg(feature = "memory-stats")]
use super::super::memory_stats;
use super::super::{parallel_intern, Value};
use super::shared::{record_counted_insert, reset_counted_table, MAX_INTERN_TABLE_ENTRIES};
use dashmap::DashMap;
use std::cell::Cell;
use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};
use std::sync::{Arc, OnceLock};

/// Global set intern table for deduplicating small sets.
///
/// Many TLA+ specs repeatedly create the same small sets (e.g., subsets of
/// {1, 2, 3} when processes are 1..3). Interning ensures we store each unique
/// set only once.
///
/// Key: FNV-1a hash of set elements (sorted)
/// Value: Arc<[Value]> - the interned set array
///
/// Only interning small sets (≤8 elements) to limit cache size and avoid
/// fingerprint collisions on large sets.
static SET_INTERN_TABLE: OnceLock<DashMap<u64, Arc<[Value]>>> = OnceLock::new();
static SET_INTERN_TABLE_ENTRY_COUNT: AtomicUsize = AtomicUsize::new(0);

/// Maximum set size for interning (larger sets are not cached)
const MAX_INTERN_SET_SIZE: usize = 8;

// Part of #3441: Thread-local flag to skip set interning.
//
// Set interning (fingerprint + DashMap lookup) adds O(n) overhead per
// set construction. For specs with many ephemeral intermediate sets
// (e.g., GameOfLife's score() creates ~2M sets/run), the fingerprint
// computation dominates. Skipping interning trades memory dedup for speed.
thread_local! {
    static SKIP_SET_INTERNING: Cell<bool> = const { Cell::new(false) };
}

/// Set whether set interning should be skipped on this thread.
pub fn set_skip_set_interning(skip: bool) {
    SKIP_SET_INTERNING.with(|cell| cell.set(skip));
}

/// Check if set interning should be skipped on this thread.
#[inline]
fn skip_set_interning() -> bool {
    SKIP_SET_INTERNING.with(|cell| cell.get())
}

#[cfg(feature = "memory-stats")]
pub(crate) fn set_intern_table_len() -> Option<usize> {
    SET_INTERN_TABLE.get().map(DashMap::len)
}

#[inline]
fn get_set_intern_table() -> &'static DashMap<u64, Arc<[Value]>> {
    SET_INTERN_TABLE.get_or_init(DashMap::new)
}

/// Snapshot the set intern table into an FxHashMap for frozen parallel interning.
/// Part of #3285 Phase 2.
pub(crate) fn snapshot_set_intern_table() -> rustc_hash::FxHashMap<u64, Arc<[Value]>> {
    match SET_INTERN_TABLE.get() {
        Some(table) => table
            .iter()
            .map(|record| (*record.key(), Arc::clone(record.value())))
            .collect(),
        None => rustc_hash::FxHashMap::default(),
    }
}

/// Compute a fingerprint for a sorted set array.
#[inline]
pub(crate) fn set_fingerprint(elements: &[Value]) -> u64 {
    use std::hash::{Hash, Hasher};

    let mut hasher = rustc_hash::FxHasher::default();
    elements.hash(&mut hasher);
    hasher.finish()
}

/// Create an Arc<[Value]> for a set, using interning for small sets.
///
/// For sets with ≤8 elements, checks the global cache first.
/// Returns cached version if found, otherwise stores and returns new arc.
///
/// Part of #3285: When parallel interning is active, uses the frozen snapshot
/// and worker-local overlay instead of the global DashMap, completely avoiding
/// cross-thread lock contention during BFS.
#[inline]
pub(crate) fn intern_set_array(elements: Vec<Value>) -> Arc<[Value]> {
    if elements.len() > MAX_INTERN_SET_SIZE || elements.is_empty() || skip_set_interning() {
        return Arc::from(elements);
    }

    let fp = set_fingerprint(&elements);

    if parallel_intern::is_parallel_intern_active() {
        if let Some(arc) = parallel_intern::parallel_intern_set(fp, &elements) {
            return arc;
        }
    }

    let table = get_set_intern_table();

    if let Some(arc) = table.get(&fp) {
        if arc.len() == elements.len() && arc.iter().zip(elements.iter()).all(|(a, b)| a == b) {
            #[cfg(feature = "memory-stats")]
            memory_stats::inc_set_cache_hit();
            return Arc::clone(arc.value());
        }
    }

    let arc: Arc<[Value]> = Arc::from(elements);
    match table.entry(fp) {
        dashmap::mapref::entry::Entry::Occupied(mut entry) => {
            let interned = entry.get();
            if interned.len() == arc.len() && interned.iter().zip(arc.iter()).all(|(a, b)| a == b) {
                #[cfg(feature = "memory-stats")]
                memory_stats::inc_set_cache_hit();
                return Arc::clone(interned);
            }
            entry.insert(Arc::clone(&arc));
        }
        dashmap::mapref::entry::Entry::Vacant(entry) => {
            entry.insert(Arc::clone(&arc));
            record_counted_insert(
                table,
                &SET_INTERN_TABLE_ENTRY_COUNT,
                fp,
                Arc::clone(&arc),
                MAX_INTERN_TABLE_ENTRIES,
            );
        }
    }
    arc
}

#[cfg(test)]
pub(crate) fn set_intern_table_entry_count() -> usize {
    SET_INTERN_TABLE.get().map_or(0, DashMap::len)
}

/// Clear the set intern table.
/// Call between model checking runs to free memory.
pub fn clear_set_intern_table() {
    if let Some(table) = SET_INTERN_TABLE.get() {
        reset_counted_table(table, &SET_INTERN_TABLE_ENTRY_COUNT);
    } else {
        SET_INTERN_TABLE_ENTRY_COUNT.store(0, AtomicOrdering::Relaxed);
    }
}
