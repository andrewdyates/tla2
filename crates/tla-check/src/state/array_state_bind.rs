// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bind/unbind methods for TLC-style mutable state exploration with backtracking.
//!
//! These methods implement TLC's mutable state exploration pattern:
//! - `bind()` saves old value, sets new value
//! - `unbind()` restores previous value from undo stack
//! - `unbind_to()` batch restores to a save point (for disjunction branches)
//! - `snapshot()` creates an immutable `State` copy for storing successors
//!
//! This avoids cloning the entire state per branch, matching TLC's O(1)
//! bind/unbind performance. See designs/2026-01-13-bind-unbind-architecture.md

use tla_value::CompactValue;

use crate::var_index::{VarIndex, VarRegistry};
use crate::Value;

use super::array_state::{ArrayState, UndoEntry};
use super::State;

impl ArrayState {
    /// Bind a variable to a new value, recording the old value for later unbind.
    ///
    /// This is an O(1) operation that:
    /// 1. Pushes the old CompactValue onto the undo stack
    /// 2. Converts and sets the new value in the values array
    /// 3. Invalidates the fingerprint cache
    ///
    /// Use with `unbind()` or `unbind_to()` to restore the previous value.
    ///
    /// # Pattern
    /// ```rust
    /// use tla_check::{ArrayState, VarRegistry, Value};
    /// use tla_check::state::UndoEntry;
    ///
    /// let registry = VarRegistry::from_names(["x"]);
    /// let idx = registry.get("x").expect("x in registry");
    ///
    /// let mut state = ArrayState::new(registry.len());
    /// let mut undo: Vec<UndoEntry> = Vec::new();
    ///
    /// let save_point = undo.len();
    /// state.bind(idx, Value::int(1), &mut undo);
    /// // ... explore with new binding ...
    /// state.unbind_to(&mut undo, save_point); // restore
    /// ```
    #[inline]
    pub fn bind(&mut self, idx: VarIndex, value: Value, undo: &mut Vec<UndoEntry>) {
        let compact = CompactValue::from(value);
        let old = std::mem::replace(&mut self.values[idx.as_usize()], compact);
        undo.push(UndoEntry {
            idx,
            old_value: old,
        });
        self.fp_cache = None; // Invalidate fingerprint
    }

    /// Bind a value without invalidating fp_cache.
    ///
    /// Use this on working states created with `clone_for_working()` where
    /// fp_cache is already None and will never be read. This avoids the
    /// overhead of repeated `fp_cache = None` assignments.
    ///
    /// # Safety Contract
    /// The caller must ensure this ArrayState was created with `clone_for_working()`
    /// or otherwise has fp_cache = None and the fingerprint will never be read
    /// from this state directly.
    ///
    /// Part of #188: Batch fingerprint optimization
    #[inline]
    pub fn bind_no_invalidate(&mut self, idx: VarIndex, value: Value, undo: &mut Vec<UndoEntry>) {
        let compact = CompactValue::from(value);
        let old = std::mem::replace(&mut self.values[idx.as_usize()], compact);
        undo.push(UndoEntry {
            idx,
            old_value: old,
        });
        // Don't invalidate fp_cache - caller guarantees it's not used
    }

    /// Unbind the most recent binding (restore previous value).
    ///
    /// This is an O(1) operation that pops the last entry from the undo stack
    /// and restores the old CompactValue.
    ///
    /// # Panics
    /// Panics if the undo stack is empty.
    ///
    /// # Note
    /// For unbinding multiple bindings, prefer `unbind_to()` which only
    /// invalidates the fingerprint cache once.
    #[inline]
    pub fn unbind(&mut self, undo: &mut Vec<UndoEntry>) {
        let entry = undo.pop().expect("unbind called with empty undo stack");
        self.values[entry.idx.as_usize()] = entry.old_value;
        self.fp_cache = None; // Invalidate fingerprint
    }

    /// Unbind multiple bindings at once, restoring to a save point.
    ///
    /// This is optimized for disjunction branches where we need to restore
    /// multiple bindings after exploring one branch. It only invalidates the
    /// fingerprint cache once at the end (z4 solver pattern).
    ///
    /// # Arguments
    /// * `undo` - The undo stack
    /// * `target_len` - The save point to restore to (typically `undo.len()` before binding)
    ///
    /// # Pattern
    /// ```rust
    /// use tla_check::{ArrayState, VarRegistry, Value};
    /// use tla_check::state::UndoEntry;
    ///
    /// let registry = VarRegistry::from_names(["x"]);
    /// let idx = registry.get("x").expect("x in registry");
    ///
    /// let mut state = ArrayState::new(registry.len());
    /// let mut undo: Vec<UndoEntry> = Vec::new();
    ///
    /// // Disjunction: try a, restore, try b, restore
    /// let save_point = undo.len();
    /// state.bind(idx, Value::int(1), &mut undo);
    /// state.unbind_to(&mut undo, save_point); // restore for b
    /// state.bind(idx, Value::int(2), &mut undo);
    /// state.unbind_to(&mut undo, save_point); // restore for caller
    /// ```
    #[inline]
    pub fn unbind_to(&mut self, undo: &mut Vec<UndoEntry>, target_len: usize) {
        if undo.len() <= target_len {
            return; // Nothing to unbind
        }
        // Inline loop - avoid repeated function call overhead (z4 solver pattern)
        while let Some(entry) = if undo.len() > target_len {
            undo.pop()
        } else {
            None
        } {
            self.values[entry.idx.as_usize()] = entry.old_value;
        }
        // Invalidate fingerprint once at end, not per unbind
        self.fp_cache = None;
    }

    /// Unbind without invalidating fp_cache.
    ///
    /// Use this on working states created with `clone_for_working()` where
    /// fp_cache is already None and will never be read.
    ///
    /// Part of #188: Batch fingerprint optimization
    #[inline]
    pub fn unbind_to_no_invalidate(&mut self, undo: &mut Vec<UndoEntry>, target_len: usize) {
        while let Some(entry) = if undo.len() > target_len {
            undo.pop()
        } else {
            None
        } {
            self.values[entry.idx.as_usize()] = entry.old_value;
        }
        // Don't invalidate fp_cache - caller guarantees it's not used
    }

    /// Create a snapshot of the current state for storing as a successor.
    ///
    /// This is the ONLY place we clone values during bind/unbind enumeration.
    /// All other operations (bind, unbind) are O(1) mutations.
    ///
    /// Returns a full `State` suitable for storing in the visited set or
    /// successor list.
    #[inline]
    pub fn snapshot(&self, registry: &VarRegistry) -> State {
        let values = self.materialize_values();
        State::from_indexed(&values, registry)
    }

    /// Create an ArrayState snapshot with fingerprint computed.
    ///
    /// This avoids the State conversion overhead when callers need ArrayState output.
    /// The fingerprint is computed before cloning so successors have cached fingerprints.
    ///
    /// Part of #131: Close 5x performance gap vs TLC
    #[inline]
    pub fn snapshot_array(&mut self, registry: &VarRegistry) -> ArrayState {
        // Ensure fingerprint is computed before cloning
        let _ = self.fingerprint(registry);
        self.clone()
    }
}
