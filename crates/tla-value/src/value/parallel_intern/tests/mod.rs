// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the parallel value interning system.
//!
//! Extracted from `parallel_intern.rs` as part of #3325 structural decomposition.
//! Split into two families:
//! - `core`: lifecycle, set, int-function, and all-table preload coverage
//! - `string_preload`: string-only preload tests (design: 2026-03-17-3285)

mod core;
mod string_preload;

use super::*;
use crate::value::intern_tables::{clear_int_func_intern_table, clear_set_intern_table};
use rustc_hash::FxHashMap;
use std::cell::Cell;
use std::sync::Arc;

/// Build a `WorkerInternState` with zeroed attribution counters.
pub(super) fn make_worker_state(
    frozen: Arc<FrozenValueInterners>,
    set_overlay: FxHashMap<u64, Arc<[Value]>>,
    int_func_overlay: FxHashMap<u64, Arc<Vec<Value>>>,
    string_overlay: FxHashMap<String, Arc<str>>,
    string_token_overlay: FxHashMap<Arc<str>, u32>,
) -> WorkerInternState {
    WorkerInternState {
        frozen,
        set_overlay,
        int_func_overlay,
        string_overlay,
        string_token_overlay,
        frozen_string_hits: Cell::new(0),
        frozen_token_hits: Cell::new(0),
        frozen_set_hits: Cell::new(0),
        frozen_int_func_hits: Cell::new(0),
        overlay_string_hits: Cell::new(0),
        overlay_token_hits: Cell::new(0),
        overlay_set_hits: Cell::new(0),
        overlay_int_func_hits: Cell::new(0),
        new_string_inserts: Cell::new(0),
        new_set_inserts: Cell::new(0),
        new_int_func_inserts: Cell::new(0),
    }
}
