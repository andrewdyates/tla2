// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! State layout for flat i64 state representation.
//!
//! Maps each state variable to a contiguous region of slots in a flat `[i64]`
//! buffer. Unlike the JIT's `compound_layout::StateLayout` (which uses
//! self-describing type tags for Cranelift), this layout is a fixed-offset
//! scheme for the model checker's state storage and comparison.
//!
//! # Slot mapping
//!
//! ```text
//! Variable 0 (Scalar):       [slot 0]
//! Variable 1 (IntArray(3)):  [slot 1, slot 2, slot 3]
//! Variable 2 (Bitmask):      [slot 4]
//! Variable 3 (Dynamic):      [slot 5]  (pointer/index to side table)
//! ```
//!
//! Part of #3986.

use std::sync::Arc;

use crate::var_index::VarRegistry;

/// Describes how a single state variable maps onto i64 slots.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct VarLayout {
    /// Human-readable variable name (for debugging).
    pub(crate) name: Arc<str>,
    /// Starting offset in the flat i64 buffer.
    pub(crate) offset: usize,
    /// Number of i64 slots this variable occupies.
    pub(crate) slot_count: usize,
    /// What kind of mapping is used.
    pub(crate) kind: VarLayoutKind,
}

/// Classification of how a variable's value maps to i64 slots.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum VarLayoutKind {
    /// Int — 1 slot. Raw i64 value.
    Scalar,
    /// Bool — 1 slot. 0 = false, 1 = true.
    /// Distinct from `Scalar` so that roundtrip conversion preserves
    /// `Value::Bool` instead of returning `Value::SmallInt`.
    ScalarBool,
    /// Integer-indexed array `[lo..hi -> Int/Bool]` — `len` contiguous slots.
    /// Each element is a scalar i64 (int value or 0/1 for bool).
    IntArray {
        /// Inclusive lower bound of the domain interval.
        lo: i64,
        /// Number of elements (= hi - lo + 1).
        len: usize,
        /// When true, all array elements are Bool-typed. Enables
        /// `reconstruct_int_array` to emit `Value::Bool(slot != 0)`
        /// instead of `Value::SmallInt(slot)`. Fixes #4014.
        elements_are_bool: bool,
    },
    /// Record with known field names — one scalar slot per field.
    /// Only applicable when ALL fields are scalar (Int/Bool).
    Record {
        /// Field names in canonical (sorted NameId) order.
        field_names: Vec<Arc<str>>,
        /// Per-field Bool type tracking. `field_is_bool[i]` is true when
        /// field `field_names[i]` holds a `Value::Bool`. This enables
        /// `reconstruct_record` to emit `Value::Bool(slot != 0)` instead
        /// of `Value::SmallInt(slot)` for Bool-typed fields. Fixes #4014.
        field_is_bool: Vec<bool>,
    },
    /// Small finite set encoded as a bitmask in a single i64.
    /// Bit i is set iff element i (from a canonical enumeration) is in the set.
    /// Only applicable when the universe has <= 63 elements.
    /// Scaffolding for JIT V2 flat state pipeline (#3986).
    #[allow(dead_code)]
    Bitmask {
        /// Number of elements in the universe.
        universe_size: usize,
    },
    /// Fallback: the variable cannot be flattened statically. The single i64
    /// slot holds 0 as a placeholder, and the actual value must be retrieved
    /// from the originating ArrayState. This allows the layout to always
    /// produce a fixed-size buffer even for heterogeneous states.
    Dynamic,
}

impl VarLayoutKind {
    /// Number of i64 slots this kind occupies.
    #[must_use]
    pub(crate) fn slot_count(&self) -> usize {
        match self {
            VarLayoutKind::Scalar | VarLayoutKind::ScalarBool => 1,
            VarLayoutKind::IntArray { len, .. } => *len,
            VarLayoutKind::Record { field_names, .. } => field_names.len(),
            VarLayoutKind::Bitmask { .. } => 1,
            VarLayoutKind::Dynamic => 1,
        }
    }
}

/// Fixed-offset mapping from variable indices to i64 slots.
///
/// Created once from an initial state (or spec metadata) and shared across
/// all `FlatState` instances for a given model-checking run.
#[derive(Debug, Clone)]
pub(crate) struct StateLayout {
    /// Per-variable layouts in VarIndex order.
    vars: Vec<VarLayout>,
    /// Total number of i64 slots in the flat buffer.
    total_slots: usize,
}

impl StateLayout {
    /// Build a layout from variable descriptors.
    ///
    /// Computes offsets by packing variables contiguously in index order.
    #[must_use]
    pub(crate) fn new(registry: &VarRegistry, kinds: Vec<VarLayoutKind>) -> Self {
        assert_eq!(
            registry.len(),
            kinds.len(),
            "StateLayout::new: registry has {} vars but {} kinds provided",
            registry.len(),
            kinds.len()
        );

        let mut vars = Vec::with_capacity(kinds.len());
        let mut offset = 0;
        for (i, kind) in kinds.into_iter().enumerate() {
            let idx = crate::var_index::VarIndex::new(i);
            let name = Arc::from(registry.name(idx));
            let slot_count = kind.slot_count();
            vars.push(VarLayout {
                name,
                offset,
                slot_count,
                kind,
            });
            offset += slot_count;
        }

        StateLayout {
            vars,
            total_slots: offset,
        }
    }

    /// Total number of i64 slots in the flat buffer.
    #[must_use]
    pub(crate) fn total_slots(&self) -> usize {
        self.total_slots
    }

    /// Number of state variables.
    #[must_use]
    pub(crate) fn var_count(&self) -> usize {
        self.vars.len()
    }

    /// Get the layout for a specific variable by index.
    /// Scaffolding for JIT V2 flat state pipeline (#3986).
    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn var_layout(&self, idx: usize) -> Option<&VarLayout> {
        self.vars.get(idx)
    }

    /// Iterate over all variable layouts.
    /// Scaffolding for JIT V2 flat state pipeline (#3986).
    #[allow(dead_code)]
    pub(crate) fn iter(&self) -> impl Iterator<Item = &VarLayout> {
        self.vars.iter()
    }

    /// True when every variable is `Scalar` (the buffer is 1:1 with ArrayState).
    #[must_use]
    pub(crate) fn is_all_scalar(&self) -> bool {
        self.vars
            .iter()
            .all(|v| matches!(v.kind, VarLayoutKind::Scalar | VarLayoutKind::ScalarBool))
    }

    /// True when every variable is either `Scalar`/`ScalarBool` or `Dynamic`.
    /// In this case the flat buffer has the same number of slots as variables.
    #[must_use]
    pub(crate) fn is_trivial(&self) -> bool {
        self.vars.iter().all(|v| {
            matches!(
                v.kind,
                VarLayoutKind::Scalar | VarLayoutKind::ScalarBool | VarLayoutKind::Dynamic
            )
        })
    }

    /// True when at least one variable has `Dynamic` layout.
    ///
    /// When true, the flat buffer alone is not sufficient for exact state
    /// reconstruction — the original `ArrayState` must be consulted for
    /// dynamic variables. This determines whether the fast-path (flat-only)
    /// or fallback-path (flat + ArrayState) is needed.
    ///
    /// Part of #3986.
    #[must_use]
    pub(crate) fn has_dynamic_vars(&self) -> bool {
        self.vars
            .iter()
            .any(|v| matches!(v.kind, VarLayoutKind::Dynamic))
    }

    /// True when every variable is fully flattenable (no Dynamic vars).
    ///
    /// When true, the flat buffer is a complete representation of the state
    /// and no fallback to ArrayState is needed. This is the condition for
    /// enabling the pure flat-state BFS path.
    ///
    /// Part of #3986.
    #[must_use]
    pub(crate) fn is_fully_flat(&self) -> bool {
        !self.has_dynamic_vars()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::var_index::VarRegistry;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_layout_all_scalar() {
        let registry = VarRegistry::from_names(["x", "y", "z"]);
        let kinds = vec![
            VarLayoutKind::Scalar,
            VarLayoutKind::Scalar,
            VarLayoutKind::Scalar,
        ];
        let layout = StateLayout::new(&registry, kinds);

        assert_eq!(layout.var_count(), 3);
        assert_eq!(layout.total_slots(), 3);
        assert!(layout.is_all_scalar());
        assert!(layout.is_trivial());

        // Check offsets
        assert_eq!(layout.var_layout(0).unwrap().offset, 0);
        assert_eq!(layout.var_layout(1).unwrap().offset, 1);
        assert_eq!(layout.var_layout(2).unwrap().offset, 2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_layout_mixed() {
        let registry = VarRegistry::from_names(["pc", "network", "flags"]);
        let kinds = vec![
            VarLayoutKind::Scalar,
            VarLayoutKind::IntArray {
                lo: 0,
                len: 3,
                elements_are_bool: false,
            },
            VarLayoutKind::Bitmask { universe_size: 5 },
        ];
        let layout = StateLayout::new(&registry, kinds);

        assert_eq!(layout.var_count(), 3);
        assert_eq!(layout.total_slots(), 5); // 1 + 3 + 1
        assert!(!layout.is_all_scalar());
        assert!(!layout.is_trivial());

        // pc at offset 0, 1 slot
        let pc = layout.var_layout(0).unwrap();
        assert_eq!(pc.offset, 0);
        assert_eq!(pc.slot_count, 1);

        // network at offset 1, 3 slots
        let net = layout.var_layout(1).unwrap();
        assert_eq!(net.offset, 1);
        assert_eq!(net.slot_count, 3);

        // flags at offset 4, 1 slot
        let flags = layout.var_layout(2).unwrap();
        assert_eq!(flags.offset, 4);
        assert_eq!(flags.slot_count, 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_var_layout_kind_slot_count() {
        assert_eq!(VarLayoutKind::Scalar.slot_count(), 1);
        assert_eq!(VarLayoutKind::ScalarBool.slot_count(), 1);
        assert_eq!(
            VarLayoutKind::IntArray {
                lo: 1,
                len: 5,
                elements_are_bool: false
            }
            .slot_count(),
            5
        );
        assert_eq!(
            VarLayoutKind::Record {
                field_names: vec![Arc::from("a"), Arc::from("b")],
                field_is_bool: vec![false, false],
            }
            .slot_count(),
            2
        );
        assert_eq!(VarLayoutKind::Bitmask { universe_size: 8 }.slot_count(), 1);
        assert_eq!(VarLayoutKind::Dynamic.slot_count(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_layout_with_dynamic() {
        let registry = VarRegistry::from_names(["a", "b"]);
        let kinds = vec![VarLayoutKind::Scalar, VarLayoutKind::Dynamic];
        let layout = StateLayout::new(&registry, kinds);

        assert!(!layout.is_all_scalar());
        assert!(layout.is_trivial());
        assert_eq!(layout.total_slots(), 2);
        assert!(layout.has_dynamic_vars());
        assert!(!layout.is_fully_flat());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_layout_fully_flat() {
        let registry = VarRegistry::from_names(["x", "y", "z"]);
        let kinds = vec![
            VarLayoutKind::Scalar,
            VarLayoutKind::IntArray {
                lo: 0,
                len: 3,
                elements_are_bool: false,
            },
            VarLayoutKind::ScalarBool,
        ];
        let layout = StateLayout::new(&registry, kinds);

        assert!(!layout.has_dynamic_vars());
        assert!(layout.is_fully_flat());
        assert!(!layout.is_all_scalar());
        assert!(!layout.is_trivial());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_layout_has_dynamic_vars_all_scalar() {
        let registry = VarRegistry::from_names(["a", "b"]);
        let kinds = vec![VarLayoutKind::Scalar, VarLayoutKind::ScalarBool];
        let layout = StateLayout::new(&registry, kinds);

        assert!(!layout.has_dynamic_vars());
        assert!(layout.is_fully_flat());
        assert!(layout.is_all_scalar());
    }
}
