// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compound state variable layout descriptors for the JIT/AOT ABI.
//!
//! The JIT state array is a flat `[i64]` where each slot holds one scalar
//! state variable. This module defines the **pure-data** layout descriptors
//! that describe how compound state variables (records, sequences, sets,
//! functions, tuples) map onto the flat buffer:
//!
//! 1. **`CompoundLayout`** — describes how a compound value maps onto a
//!    contiguous region of the flat state array.
//! 2. **`VarLayout`** — per-variable descriptor (scalar vs. compound).
//! 3. **`StateLayout`** — full description of all state variables.
//! 4. **`TAG_*` constants** — type tag words used in the self-describing
//!    serialized format.
//!
//! Only the pure-data structures live here. The serialization functions
//! (`serialize_value`, `deserialize_value`, `infer_layout`, `infer_var_layout`)
//! live in `tla-jit-runtime::compound_layout` because they require
//! `tla-value::Value`, which transitively pulls in heavy runtime machinery
//! the leaf ABI crate does not want.
//!
//! Part of #4267 (Wave 7d, epic #4251 Stage 2d): consolidated the previously
//! forked `tla-jit-runtime::compound_layout` pure-data types and
//! `tla-llvm2::runtime_abi::compound_layout` duplicates into a single
//! canonical definition that survives the Stage 2d deletion of `tla-jit`,
//! `tla-jit-runtime`, and the Cranelift forks.
//!
//! # Wire format summary
//!
//! ```text
//! Record [a |-> 1, b |-> TRUE]:
//!   slot[0] = TAG_RECORD (1)
//!   slot[1] = 2 (field count)
//!   slot[2] = name_id("a") as i64
//!   slot[3] = TAG_INT (5)
//!   slot[4] = 1
//!   slot[5] = name_id("b") as i64
//!   slot[6] = TAG_BOOL (6)
//!   slot[7] = 1 (TRUE)
//!
//! Sequence <<3, 7>>:
//!   slot[0] = TAG_SEQ (2)
//!   slot[1] = 2 (length)
//!   slot[2] = TAG_INT (5)
//!   slot[3] = 3
//!   slot[4] = TAG_INT (5)
//!   slot[5] = 7
//! ```

use tla_core::NameId;

// ============================================================================
// Value type tags for the flat i64 representation
// ============================================================================

/// Type tag for a record value in the flat i64 state array.
pub const TAG_RECORD: i64 = 1;
/// Type tag for a sequence value.
pub const TAG_SEQ: i64 = 2;
/// Type tag for a set value (finite, enumerated).
pub const TAG_SET: i64 = 3;
/// Type tag for a function value.
pub const TAG_FUNC: i64 = 4;
/// Type tag for an integer scalar.
pub const TAG_INT: i64 = 5;
/// Type tag for a boolean scalar.
pub const TAG_BOOL: i64 = 6;
/// Type tag for a string value (stored as interned NameId).
pub const TAG_STRING: i64 = 7;
/// Type tag for a tuple value.
pub const TAG_TUPLE: i64 = 8;

// ============================================================================
// Compound layout descriptors
// ============================================================================

/// Describes the layout of a single state variable in the JIT state array.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum VarLayout {
    /// Scalar integer — occupies 1 i64 slot.
    ScalarInt,
    /// Scalar boolean — occupies 1 i64 slot (0 = false, 1 = true).
    ScalarBool,
    /// Compound value — occupies a variable number of i64 slots determined
    /// by the value's serialized form. The `CompoundLayout` descriptor
    /// provides the structure, but the actual slot count depends on the
    /// runtime value (e.g., sequence length, record field count).
    Compound(CompoundLayout),
}

/// Describes the expected structure of a compound state variable.
///
/// Used by the JIT to understand the memory layout of compound values
/// and to validate serialized data during deserialization.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CompoundLayout {
    /// Record with known field names (sorted by NameId).
    /// Each field has its own layout descriptor.
    Record {
        /// (field_name_id, field_layout) pairs, sorted by NameId.
        fields: Vec<(NameId, CompoundLayout)>,
    },

    /// Function (domain -> range mapping).
    /// Stored as interleaved key-value pairs.
    Function {
        /// Layout of domain keys.
        key_layout: Box<CompoundLayout>,
        /// Layout of range values.
        value_layout: Box<CompoundLayout>,
        /// Number of key-value pairs when inferred from a concrete value.
        /// `None` when the cardinality is unknown (e.g., parsed from metadata).
        /// When `Some(n)`, `fixed_serialized_slots()` can compute the total
        /// size as `2 + n * (key_size + value_size)`.
        pair_count: Option<usize>,
        /// For integer-domain functions `[lo..hi -> T]`, the inclusive lower
        /// bound of the domain interval. When `Some(lo)` and `pair_count` is
        /// `Some(n)`, the function maps `lo..lo+n-1` to contiguous values.
        /// This enables O(1) direct-index lookup: `value_at(k) = slots[base + 2 + (k - lo) * pair_slots + key_slots]`.
        ///
        /// `None` for non-integer domains or non-contiguous keys.
        ///
        /// Part of #3985: Phase 2 compound layout wiring.
        domain_lo: Option<i64>,
    },

    /// Sequence of homogeneous or heterogeneous elements.
    Sequence {
        /// Layout of each element (all elements share this layout).
        element_layout: Box<CompoundLayout>,
        /// Number of elements when inferred from a concrete value.
        element_count: Option<usize>,
    },

    /// Finite enumerated set.
    Set {
        /// Layout of each element.
        element_layout: Box<CompoundLayout>,
        /// Number of elements when inferred from a concrete value.
        element_count: Option<usize>,
    },

    /// Tuple with known arity and per-position layouts.
    Tuple {
        /// Layout of each position (1-indexed in TLA+, stored 0-indexed).
        element_layouts: Vec<CompoundLayout>,
    },

    /// Scalar integer leaf — no compound structure.
    Int,

    /// Scalar boolean leaf — no compound structure.
    Bool,

    /// String leaf — serialized as its interned NameId (u32 as i64).
    String,

    /// Dynamic (type-tagged) — the actual type is encoded inline via
    /// a tag word. Used for heterogeneous collections where the element
    /// type is not statically known.
    Dynamic,
}

impl CompoundLayout {
    /// Compute the fixed serialized size in i64 slots, if statically known.
    ///
    /// Returns `Some(n)` when the entire compound value has a fixed, predictable
    /// serialized size. Returns `None` for dynamic or variable-length layouts.
    ///
    /// Scalar leaves: TAG + value = 2 slots.
    /// Records: TAG + field_count + sum(name_id + field_serialized_size per field).
    /// Tuples: TAG + elem_count + sum(elem_serialized_size per element).
    /// Functions: TAG + pair_count + sum(key_size + value_size per pair).
    ///   When `pair_count` is `Some(n)` (inferred from a concrete value),
    ///   the total is `2 + n * (key_slots + value_slots)`.
    /// Sequences/Sets: TAG + count + n * element_slots when count is known.
    #[must_use]
    pub fn fixed_serialized_slots(&self) -> Option<usize> {
        match self {
            CompoundLayout::Int | CompoundLayout::Bool | CompoundLayout::String => Some(2),
            CompoundLayout::Record { fields } => {
                let mut total = 2; // TAG_RECORD + field_count
                for (_, field_layout) in fields {
                    total += 1; // name_id slot
                    total += field_layout.fixed_serialized_slots()?;
                }
                Some(total)
            }
            CompoundLayout::Tuple { element_layouts } => {
                let mut total = 2; // TAG_TUPLE + elem_count
                for elem_layout in element_layouts {
                    total += elem_layout.fixed_serialized_slots()?;
                }
                Some(total)
            }
            CompoundLayout::Function {
                key_layout,
                value_layout,
                pair_count,
                ..
            } => {
                let n = (*pair_count)?;
                if n == 0 {
                    return Some(2); // TAG + count header only
                }
                let key_slots = key_layout.fixed_serialized_slots()?;
                let value_slots = value_layout.fixed_serialized_slots()?;
                Some(2 + n * (key_slots + value_slots))
            }
            CompoundLayout::Sequence {
                element_layout,
                element_count,
            } => {
                let n = (*element_count)?;
                if n == 0 {
                    return Some(2); // TAG + count header only
                }
                let elem_slots = element_layout.fixed_serialized_slots()?;
                Some(2 + n * elem_slots)
            }
            CompoundLayout::Set {
                element_layout,
                element_count,
            } => {
                let n = (*element_count)?;
                if n == 0 {
                    return Some(2); // TAG + count header only
                }
                let elem_slots = element_layout.fixed_serialized_slots()?;
                Some(2 + n * elem_slots)
            }
            CompoundLayout::Dynamic => None,
        }
    }

    /// Check if this is a scalar leaf type (Int, Bool, or String).
    #[must_use]
    pub fn is_scalar(&self) -> bool {
        matches!(
            self,
            CompoundLayout::Int | CompoundLayout::Bool | CompoundLayout::String
        )
    }

    /// Check if this function has a contiguous integer domain enabling O(1)
    /// direct-index lookup instead of O(n) linear scan.
    ///
    /// Returns `Some((lo, len))` when the function maps `[lo..lo+len-1] -> T`
    /// with scalar keys and known pair count.
    ///
    /// Part of #3985: Phase 2 compound layout wiring.
    #[must_use]
    pub fn int_array_bounds(&self) -> Option<(i64, usize)> {
        match self {
            CompoundLayout::Function {
                key_layout,
                pair_count: Some(n),
                domain_lo: Some(lo),
                ..
            } if key_layout.is_scalar() && *n > 0 => Some((*lo, *n)),
            _ => None,
        }
    }
}

/// Describes the layout of the full state vector (all state variables).
///
/// Maps each state variable index to its layout descriptor and its
/// starting offset in the flat i64 array.
#[derive(Debug, Clone)]
pub struct StateLayout {
    /// Per-variable layout descriptors, in VarIdx order.
    vars: Vec<VarLayout>,
}

impl StateLayout {
    /// Create a new state layout from variable descriptors.
    pub fn new(vars: Vec<VarLayout>) -> Self {
        StateLayout { vars }
    }

    /// Get the number of state variables.
    pub fn var_count(&self) -> usize {
        self.vars.len()
    }

    /// Get the layout for a specific variable.
    pub fn var_layout(&self, idx: usize) -> Option<&VarLayout> {
        self.vars.get(idx)
    }

    /// Check if all variables are scalar (legacy flat i64 layout).
    pub fn is_all_scalar(&self) -> bool {
        self.vars
            .iter()
            .all(|v| matches!(v, VarLayout::ScalarInt | VarLayout::ScalarBool))
    }

    /// Iterate over all variable layouts.
    pub fn iter(&self) -> impl Iterator<Item = &VarLayout> {
        self.vars.iter()
    }

    /// Compute the starting slot offset for each variable in the flat i64 array.
    ///
    /// Returns a vector where `offsets[i]` is `Some(offset)` for variables
    /// whose starting position can be determined at compile time, or `None`
    /// for variables that come after a dynamic-size compound variable.
    ///
    /// Scalar variables occupy 1 slot. Compound variables with fixed
    /// serialized size occupy their `fixed_serialized_slots()` count.
    /// Once a variable with dynamic size is encountered, all subsequent
    /// variables get `None` (their offsets cannot be computed statically).
    #[must_use]
    pub fn compute_var_offsets(&self) -> Vec<Option<usize>> {
        let mut offsets = Vec::with_capacity(self.vars.len());
        let mut current: Option<usize> = Some(0);
        for var in &self.vars {
            offsets.push(current);
            if let Some(cur) = current {
                match var {
                    VarLayout::ScalarInt | VarLayout::ScalarBool => {
                        current = Some(cur + 1);
                    }
                    VarLayout::Compound(layout) => {
                        current = layout.fixed_serialized_slots().map(|s| cur + s);
                    }
                }
            }
        }
        offsets
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tag_values_stable() {
        // The tag constants are part of the wire format — do not change these
        // values without coordinating with every serializer/deserializer in
        // both backends (Cranelift `tla-jit` and LLVM2 `tla-llvm2`).
        assert_eq!(TAG_RECORD, 1);
        assert_eq!(TAG_SEQ, 2);
        assert_eq!(TAG_SET, 3);
        assert_eq!(TAG_FUNC, 4);
        assert_eq!(TAG_INT, 5);
        assert_eq!(TAG_BOOL, 6);
        assert_eq!(TAG_STRING, 7);
        assert_eq!(TAG_TUPLE, 8);
    }

    #[test]
    fn test_compound_layout_scalar_slot_count() {
        assert_eq!(CompoundLayout::Int.fixed_serialized_slots(), Some(2));
        assert_eq!(CompoundLayout::Bool.fixed_serialized_slots(), Some(2));
        assert_eq!(CompoundLayout::String.fixed_serialized_slots(), Some(2));
        assert!(CompoundLayout::Int.is_scalar());
        assert!(!CompoundLayout::Dynamic.is_scalar());
    }

    #[test]
    fn test_compound_layout_dynamic_has_no_fixed_size() {
        assert_eq!(CompoundLayout::Dynamic.fixed_serialized_slots(), None);
    }

    #[test]
    fn test_compound_layout_function_int_array_bounds() {
        let layout = CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Bool),
            pair_count: Some(4),
            domain_lo: Some(0),
        };
        assert_eq!(layout.int_array_bounds(), Some((0, 4)));
    }

    #[test]
    fn test_compound_layout_function_without_domain_lo() {
        let layout = CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Bool),
            pair_count: Some(4),
            domain_lo: None,
        };
        assert_eq!(layout.int_array_bounds(), None);
    }

    #[test]
    fn test_state_layout_all_scalar() {
        let layout = StateLayout::new(vec![VarLayout::ScalarInt, VarLayout::ScalarBool]);
        assert_eq!(layout.var_count(), 2);
        assert!(layout.is_all_scalar());
    }

    #[test]
    fn test_state_layout_mixed_not_all_scalar() {
        let layout = StateLayout::new(vec![
            VarLayout::ScalarInt,
            VarLayout::Compound(CompoundLayout::Sequence {
                element_layout: Box::new(CompoundLayout::Int),
                element_count: None,
            }),
        ]);
        assert_eq!(layout.var_count(), 2);
        assert!(!layout.is_all_scalar());
    }

    #[test]
    fn test_compute_var_offsets_scalar_run() {
        let layout = StateLayout::new(vec![
            VarLayout::ScalarInt,
            VarLayout::ScalarBool,
            VarLayout::ScalarInt,
        ]);
        assert_eq!(
            layout.compute_var_offsets(),
            vec![Some(0), Some(1), Some(2)]
        );
    }

    #[test]
    fn test_compute_var_offsets_truncates_after_dynamic() {
        let layout = StateLayout::new(vec![
            VarLayout::ScalarInt,
            VarLayout::Compound(CompoundLayout::Dynamic),
            VarLayout::ScalarInt,
        ]);
        assert_eq!(
            layout.compute_var_offsets(),
            vec![Some(0), Some(1), None]
        );
    }
}
