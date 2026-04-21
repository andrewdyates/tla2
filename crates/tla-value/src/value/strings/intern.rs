// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use dashmap::DashMap;
use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};
use std::sync::{Arc, OnceLock};

/// Global string intern table for O(1) pointer-based string equality.
///
/// When the same string literal is used multiple times (e.g., "ECHO", "V0"),
/// interning ensures they share the same Arc<str>, making comparisons
/// a simple pointer equality check instead of content comparison.
///
/// Uses DashMap for lock-free concurrent access.
static STRING_INTERN_TABLE: OnceLock<DashMap<String, Arc<str>>> = OnceLock::new();
static STRING_INTERN_TABLE_ENTRY_COUNT: AtomicUsize = AtomicUsize::new(0);

/// Maximum entries before the string intern table is cleared to reclaim memory.
///
/// Typical TLA+ specs use a bounded set of string literals (variable names,
/// operator names, model values). Unbounded growth comes from dynamically
/// generated strings (e.g., `ToString(i)` over large integer ranges).
/// Clearing is safe: `Value::String` equality falls back to content comparison
/// when `Arc` pointers differ (ordering.rs:932).
///
/// Part of #1331: memory safety audit -- unbounded intern tables.
pub(super) const MAX_STRING_INTERN_ENTRIES: usize = 10_000;

/// Get the string intern table, initializing if needed.
#[inline]
fn get_intern_table() -> &'static DashMap<String, Arc<str>> {
    STRING_INTERN_TABLE.get_or_init(DashMap::new)
}

/// Intern a string, returning a shared `Arc<str>`.
///
/// If the string was previously interned, returns the existing Arc.
/// Otherwise, creates a new Arc and stores it for future reuse.
///
/// This function should be used for all TLA+ string values and model value names
/// to enable O(1) pointer-based equality comparisons.
#[inline]
pub fn intern_string(s: &str) -> Arc<str> {
    // Part of #3285: Route through frozen snapshot + worker-local overlay
    // during parallel BFS to avoid DashMap shard-lock contention.
    if super::super::parallel_intern::is_parallel_intern_active() {
        if let Some(arc) = super::super::parallel_intern::parallel_intern_string(s) {
            return arc;
        }
    }

    let table = get_intern_table();

    // Fast path: check if already interned
    if let Some(arc) = table.get(s) {
        return Arc::clone(arc.value());
    }

    // Slow path: insert new string
    // Use entry API to avoid race conditions.
    let key = s.to_string();
    let arc: Arc<str> = Arc::from(s);
    match table.entry(key.clone()) {
        dashmap::mapref::entry::Entry::Occupied(entry) => Arc::clone(entry.get()),
        dashmap::mapref::entry::Entry::Vacant(entry) => {
            entry.insert(Arc::clone(&arc));

            // Part of #3287: Eagerly assign TLC string token at intern time,
            // matching TLC's UniqueString.uniqueStringOf() which assigns tok
            // at construction, not at first comparison. This makes parse-time
            // token order deterministic regardless of worker scheduling.
            super::tokens::tlc_string_token(&arc);

            // Cap table size to prevent unbounded growth (Part of #1331).
            // The entry count is approximate and only guards memory usage, so a
            // relaxed atomic avoids the cross-shard DashMap::len() scan here.
            if STRING_INTERN_TABLE_ENTRY_COUNT.fetch_add(1, AtomicOrdering::Relaxed) + 1
                > MAX_STRING_INTERN_ENTRIES
            {
                table.clear();
                STRING_INTERN_TABLE_ENTRY_COUNT.store(0, AtomicOrdering::Relaxed);
                table.insert(key, Arc::clone(&arc));
                STRING_INTERN_TABLE_ENTRY_COUNT.store(1, AtomicOrdering::Relaxed);
            }

            arc
        }
    }
}

/// Get the number of entries in the string intern table.
#[cfg(test)]
pub(super) fn string_intern_table_entry_count() -> usize {
    STRING_INTERN_TABLE.get().map_or(0, DashMap::len)
}

/// Snapshot the string intern table into an immutable FxHashMap.
///
/// Part of #3285: Used by `parallel_intern::freeze_value_interners()` to create
/// the frozen snapshot before spawning BFS workers.
pub(in crate::value) fn snapshot_string_intern_table() -> rustc_hash::FxHashMap<String, Arc<str>> {
    let table = get_intern_table();
    table
        .iter()
        .map(|entry| (entry.key().clone(), Arc::clone(entry.value())))
        .collect()
}

/// Clear the string intern table.
///
/// Call between model checking runs to free memory. Clearing is safe because
/// `Value::String` equality falls back to content comparison when `Arc`
/// pointers differ.
pub fn clear_string_intern_table() {
    if let Some(table) = STRING_INTERN_TABLE.get() {
        table.clear();
    }
    STRING_INTERN_TABLE_ENTRY_COUNT.store(0, AtomicOrdering::Relaxed);
}
