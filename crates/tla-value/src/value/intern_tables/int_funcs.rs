// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::{parallel_intern, Value};
use super::shared::{record_counted_insert, reset_counted_table, MAX_INTERN_TABLE_ENTRIES};
use dashmap::DashMap;
use std::cell::Cell;
use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};
use std::sync::{Arc, OnceLock};

/// Global intern table for IntIntervalFunc values.
/// Key: FNV-1a hash of (min, max, elements)
/// Value: Arc<Vec<Value>> - the interned values array
static INT_FUNC_INTERN_TABLE: OnceLock<DashMap<u64, Arc<Vec<Value>>>> = OnceLock::new();
static INT_FUNC_INTERN_TABLE_ENTRY_COUNT: AtomicUsize = AtomicUsize::new(0);

/// Maximum IntIntervalFunc size for interning
pub(crate) const MAX_INTERN_INT_FUNC_SIZE: usize = 8;

// Part of #3316: Thread-local flag to skip IntIntervalFunc interning.
//
// Simulation mode generates unique states on random traces - interning
// provides little memory benefit but adds per-EXCEPT overhead:
// hash ALL values + DashMap lookup + potential re-intern.
// For 7-node EWD998ChanID, this is ~200+ hash ops per step.
thread_local! {
    static SKIP_INT_FUNC_INTERNING: Cell<bool> = const { Cell::new(false) };
}

/// Set whether IntIntervalFunc interning should be skipped on this thread.
pub fn set_skip_int_func_interning(skip: bool) {
    SKIP_INT_FUNC_INTERNING.with(|cell| cell.set(skip));
}

/// Check if IntIntervalFunc interning should be skipped on this thread.
#[inline]
pub(crate) fn skip_int_func_interning() -> bool {
    SKIP_INT_FUNC_INTERNING.with(|cell| cell.get())
}

#[cfg(feature = "memory-stats")]
pub(crate) fn int_func_intern_table_len() -> Option<usize> {
    INT_FUNC_INTERN_TABLE.get().map(DashMap::len)
}

#[inline]
fn get_int_func_intern_table() -> &'static DashMap<u64, Arc<Vec<Value>>> {
    INT_FUNC_INTERN_TABLE.get_or_init(DashMap::new)
}

/// Snapshot the int-function intern table into an FxHashMap for frozen parallel interning.
/// Part of #3285 Phase 2.
pub(crate) fn snapshot_int_func_intern_table() -> rustc_hash::FxHashMap<u64, Arc<Vec<Value>>> {
    match INT_FUNC_INTERN_TABLE.get() {
        Some(table) => table
            .iter()
            .map(|record| (*record.key(), Arc::clone(record.value())))
            .collect(),
        None => rustc_hash::FxHashMap::default(),
    }
}

/// Compute a fingerprint for an IntIntervalFunc modification.
/// Computes what the fingerprint would be after setting values[arr_idx] = new_value.
#[inline]
fn int_func_modified_fingerprint(
    min: i64,
    max: i64,
    values: &[Value],
    arr_idx: usize,
    new_value: &Value,
) -> u64 {
    use std::hash::{Hash, Hasher};

    let mut hasher = rustc_hash::FxHasher::default();
    min.hash(&mut hasher);
    max.hash(&mut hasher);
    for (i, value) in values.iter().enumerate() {
        if i == arr_idx {
            new_value.hash(&mut hasher);
        } else {
            value.hash(&mut hasher);
        }
    }
    hasher.finish()
}

/// Compute a fingerprint for an IntIntervalFunc.
#[inline]
pub(crate) fn int_func_fingerprint(min: i64, max: i64, values: &[Value]) -> u64 {
    use std::hash::{Hash, Hasher};

    let mut hasher = rustc_hash::FxHasher::default();
    min.hash(&mut hasher);
    max.hash(&mut hasher);
    values.hash(&mut hasher);
    hasher.finish()
}

/// Try to find an interned IntIntervalFunc with a modification applied.
/// Returns the interned Arc if found, None if we need to create a new one.
///
/// Part of #3285: When parallel interning is active, checks the frozen snapshot
/// and worker-local overlay instead of the global DashMap.
#[inline]
pub(crate) fn try_get_interned_modified(
    min: i64,
    max: i64,
    values: &[Value],
    arr_idx: usize,
    new_value: &Value,
) -> Option<Arc<Vec<Value>>> {
    let fp = int_func_modified_fingerprint(min, max, values, arr_idx, new_value);

    if parallel_intern::is_parallel_intern_active() {
        if let Some(result) =
            parallel_intern::parallel_try_get_interned_modified(fp, values, arr_idx, new_value)
        {
            return result;
        }
    }

    let table = get_int_func_intern_table();
    if let Some(arc) = table.get(&fp) {
        if arc.len() == values.len() {
            let matches = arc.iter().enumerate().all(|(i, value)| {
                if i == arr_idx {
                    value == new_value
                } else {
                    value == &values[i]
                }
            });
            if matches {
                return Some(Arc::clone(arc.value()));
            }
        }
    }
    None
}

/// Intern an IntIntervalFunc's values array.
///
/// Part of #3285: When parallel interning is active, uses the frozen snapshot
/// + worker-local overlay instead of the global DashMap.
#[inline]
pub(crate) fn intern_int_func_array(min: i64, max: i64, values: Vec<Value>) -> Arc<Vec<Value>> {
    if values.len() > MAX_INTERN_INT_FUNC_SIZE {
        return Arc::new(values);
    }

    let fp = int_func_fingerprint(min, max, &values);

    if parallel_intern::is_parallel_intern_active() {
        if let Some(arc) = parallel_intern::parallel_intern_int_func(fp, &values) {
            return arc;
        }
    }

    let table = get_int_func_intern_table();

    if let Some(arc) = table.get(&fp) {
        if arc.len() == values.len() && arc.iter().zip(values.iter()).all(|(a, b)| a == b) {
            return Arc::clone(arc.value());
        }
    }

    let arc = Arc::new(values);
    match table.entry(fp) {
        dashmap::mapref::entry::Entry::Occupied(mut entry) => {
            let interned = entry.get();
            if interned.len() == arc.len() && interned.iter().zip(arc.iter()).all(|(a, b)| a == b) {
                return Arc::clone(interned);
            }
            entry.insert(Arc::clone(&arc));
        }
        dashmap::mapref::entry::Entry::Vacant(entry) => {
            entry.insert(Arc::clone(&arc));
            record_counted_insert(
                table,
                &INT_FUNC_INTERN_TABLE_ENTRY_COUNT,
                fp,
                Arc::clone(&arc),
                MAX_INTERN_TABLE_ENTRIES,
            );
        }
    }
    arc
}

#[cfg(test)]
pub(crate) fn int_func_intern_table_entry_count() -> usize {
    INT_FUNC_INTERN_TABLE.get().map_or(0, DashMap::len)
}

/// Clear the IntIntervalFunc intern table.
pub fn clear_int_func_intern_table() {
    if let Some(table) = INT_FUNC_INTERN_TABLE.get() {
        reset_counted_table(table, &INT_FUNC_INTERN_TABLE_ENTRY_COUNT);
    } else {
        INT_FUNC_INTERN_TABLE_ENTRY_COUNT.store(0, AtomicOrdering::Relaxed);
    }
}
