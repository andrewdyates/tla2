// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use dashmap::DashMap;
use std::hash::Hash;
use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};

/// Maximum number of entries in each intern table before clearing.
/// Prevents unbounded memory growth in long model checking runs with high
/// unique value cardinality. When exceeded, the table is cleared and the
/// new entry is inserted into the fresh table. The 8-element size limit
/// bounds typical growth, but pathological specs can still produce many
/// unique small sets/functions.
pub(super) const MAX_INTERN_TABLE_ENTRIES: usize = 10_000;

#[inline]
pub(super) fn reset_counted_table<K, V>(table: &DashMap<K, V>, entry_count: &AtomicUsize)
where
    K: Eq + Hash,
{
    table.clear();
    entry_count.store(0, AtomicOrdering::Relaxed);
}

#[inline]
pub(super) fn record_counted_insert<K, V>(
    table: &DashMap<K, V>,
    entry_count: &AtomicUsize,
    key: K,
    value: V,
    cap: usize,
) where
    K: Eq + Hash,
{
    if entry_count.fetch_add(1, AtomicOrdering::Relaxed) + 1 > cap {
        reset_counted_table(table, entry_count);
        table.insert(key, value);
        entry_count.store(1, AtomicOrdering::Relaxed);
    }
}
