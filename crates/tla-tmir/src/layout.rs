// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! State layout for tMIR lowering.
//!
//! Maps state variable indices (as used by `LoadVar`/`StoreVar` bytecodes) to
//! i64 slot offsets in the flat state buffer passed to compiled functions.
//!
//! # Current model (Phase D)
//!
//! The layout is trivial: `var_idx` maps 1:1 to slot offset. Each state
//! variable occupies exactly one i64 slot. This works for all scalar specs
//! (integers, booleans, model value enums).
//!
//! # Future model (Phase E)
//!
//! When compound state variables (records, arrays, sets) are flattened into
//! the state buffer, the layout becomes non-trivial: a record with 3 fields
//! occupies 3 consecutive slots, and `var_idx` no longer equals slot offset.
//! This module will then compute offsets from type information.

/// State layout description for compiled functions.
///
/// Determines how `var_idx` values in `LoadVar`/`StoreVar`/`LoadPrime`
/// bytecodes map to i64 slot offsets in the state buffer.
#[derive(Debug, Clone)]
pub struct TmirStateLayout {
    /// Slot offset for each variable index. `offsets[var_idx]` is the
    /// starting i64 slot for that variable.
    offsets: Vec<usize>,
    /// Number of i64 slots per variable. `slot_counts[var_idx]` is the
    /// number of contiguous slots occupied.
    slot_counts: Vec<usize>,
    /// Total number of i64 slots in the flat buffer.
    total_slots: usize,
}

impl TmirStateLayout {
    /// Create a trivial layout where each variable occupies one i64 slot.
    ///
    /// This is the Phase D default: `var_idx` == slot offset.
    #[must_use]
    pub fn trivial(var_count: usize) -> Self {
        let offsets: Vec<usize> = (0..var_count).collect();
        let slot_counts = vec![1; var_count];
        TmirStateLayout {
            offsets,
            slot_counts,
            total_slots: var_count,
        }
    }

    /// Get the starting slot offset for a variable.
    #[must_use]
    pub fn offset(&self, var_idx: u16) -> Option<usize> {
        self.offsets.get(usize::from(var_idx)).copied()
    }

    /// Get the number of i64 slots occupied by a variable.
    #[must_use]
    pub fn slot_count(&self, var_idx: u16) -> Option<usize> {
        self.slot_counts.get(usize::from(var_idx)).copied()
    }

    /// Total number of i64 slots in the flat state buffer.
    #[must_use]
    pub fn total_slots(&self) -> usize {
        self.total_slots
    }

    /// Number of state variables.
    #[must_use]
    pub fn var_count(&self) -> usize {
        self.offsets.len()
    }

    /// True when every variable occupies exactly one slot (trivial layout).
    #[must_use]
    pub fn is_trivial(&self) -> bool {
        self.slot_counts.iter().all(|&c| c == 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trivial_layout_basic() {
        let layout = TmirStateLayout::trivial(5);
        assert_eq!(layout.var_count(), 5);
        assert_eq!(layout.total_slots(), 5);
        assert!(layout.is_trivial());

        for i in 0..5u16 {
            assert_eq!(layout.offset(i), Some(usize::from(i)));
            assert_eq!(layout.slot_count(i), Some(1));
        }

        assert_eq!(layout.offset(5), None);
        assert_eq!(layout.slot_count(5), None);
    }

    #[test]
    fn test_trivial_layout_empty() {
        let layout = TmirStateLayout::trivial(0);
        assert_eq!(layout.var_count(), 0);
        assert_eq!(layout.total_slots(), 0);
        assert!(layout.is_trivial());
        assert_eq!(layout.offset(0), None);
    }
}
