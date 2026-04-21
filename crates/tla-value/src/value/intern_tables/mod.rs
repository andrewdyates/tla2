// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interning tables for set and int-function deduplication.
//!
//! Extracted from `interning_sets.rs` per #3306. Contains only the global
//! DashMap-based intern table facade and child modules for get/snapshot/
//! intern/clear operations. The `SortedSet` value type and `SetBuilder` are in
//! `sorted_set/`.

// Part of #3459: child modules need pub(in crate::value) so their items
// (also pub(in crate::value)) can be re-exported through this mod.rs.
pub(in crate::value) mod int_funcs;
pub(in crate::value) mod sets;
mod shared;
#[cfg(test)]
mod tests;

#[cfg(test)]
pub(super) use int_funcs::int_func_fingerprint;
pub use int_funcs::{clear_int_func_intern_table, set_skip_int_func_interning};
pub(super) use int_funcs::{
    intern_int_func_array, skip_int_func_interning, snapshot_int_func_intern_table,
    try_get_interned_modified, MAX_INTERN_INT_FUNC_SIZE,
};
#[cfg(test)]
pub(super) use sets::set_fingerprint;
pub use sets::{clear_set_intern_table, set_skip_set_interning};
pub(super) use sets::{intern_set_array, snapshot_set_intern_table};

#[cfg(feature = "memory-stats")]
pub(super) use int_funcs::int_func_intern_table_len;
#[cfg(feature = "memory-stats")]
pub(super) use sets::set_intern_table_len;
