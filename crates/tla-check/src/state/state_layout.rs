// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
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

/// Per-element type tag for flat state encoding.
///
/// Tracks whether each slot in an IntArray or Record field is an integer,
/// boolean, or interned string/model-value. This enables correct roundtrip
/// reconstruction from i64 slots.
///
/// Part of #3908: compound type flat state roundtrip.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SlotType {
    /// Integer value — stored as raw i64.
    Int,
    /// Boolean value — stored as 0/1.
    Bool,
    /// Interned string — stored as NameId (u32 as i64).
    String,
    /// Model value — stored as NameId (u32 as i64), reconstructed as ModelValue.
    ModelValue,
}

/// Scalar value stored as fixed layout metadata.
///
/// Recursive aggregate layouts store function domains and set universes as
/// metadata so the flat buffer only needs to contain range values/bitmasks.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum FlatScalarValue {
    /// Integer key or set element.
    Int(i64),
    /// Boolean key or set element.
    Bool(bool),
    /// String key or set element.
    String(Arc<str>),
    /// Model value key or set element.
    ModelValue(Arc<str>),
}

/// Evidence attached to a recursive sequence capacity.
///
/// `max_len` is just storage width. This marker records whether that width was
/// only observed from sampled states or is backed by a global proof/invariant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SequenceBoundEvidence {
    /// Capacity was inferred from concrete initial/wavefront values.
    Observed,
    /// Capacity and element layout are backed by a fixed finite function-domain
    /// type proof, e.g. `x \in [1..N -> T]`, for a runtime representation that
    /// is stored as a TLA sequence.
    FixedDomainTypeLayout { invariant: Arc<str> },
    /// Capacity is backed by a checked source-level bound.
    ProvenInvariant { invariant: Arc<str> },
    /// Capacity and sequence element layout are both backed by checked
    /// source-level invariants.
    ProvenInvariantWithElementLayout {
        invariant: Arc<str>,
        element_invariant: Arc<str>,
    },
}

impl SequenceBoundEvidence {
    #[must_use]
    pub(crate) fn is_proven(&self) -> bool {
        matches!(
            self,
            SequenceBoundEvidence::FixedDomainTypeLayout { .. }
                | SequenceBoundEvidence::ProvenInvariant { .. }
                | SequenceBoundEvidence::ProvenInvariantWithElementLayout { .. }
        )
    }

    #[must_use]
    pub(crate) fn supports_flat_primary(&self) -> bool {
        matches!(
            self,
            SequenceBoundEvidence::FixedDomainTypeLayout { .. }
                | SequenceBoundEvidence::ProvenInvariantWithElementLayout { .. }
        )
    }
}

impl FlatScalarValue {
    /// Slot type used when this scalar is encoded as a flat i64 value.
    #[must_use]
    pub(crate) fn slot_type(&self) -> SlotType {
        match self {
            FlatScalarValue::Int(_) => SlotType::Int,
            FlatScalarValue::Bool(_) => SlotType::Bool,
            FlatScalarValue::String(_) => SlotType::String,
            FlatScalarValue::ModelValue(_) => SlotType::ModelValue,
        }
    }
}

#[must_use]
pub(crate) fn ordered_dense_int_domain(domain: &[FlatScalarValue]) -> Option<(i64, usize)> {
    let Some(FlatScalarValue::Int(lo)) = domain.first() else {
        return None;
    };

    for (index, value) in domain.iter().enumerate() {
        let index = i64::try_from(index).ok()?;
        let expected = lo.checked_add(index)?;
        if !matches!(value, FlatScalarValue::Int(actual) if *actual == expected) {
            return None;
        }
    }

    Some((*lo, domain.len()))
}

/// Recursive fixed-size value layout for aggregate flat-state encoding.
///
/// This is intentionally compact: function keys, record fields, and set
/// universes are metadata; only mutable range values and sequence lengths are
/// serialized into the flat i64 buffer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum FlatValueLayout {
    /// Single scalar slot.
    Scalar(SlotType),
    /// Function with contiguous integer domain `lo..lo+len-1`.
    IntFunction {
        lo: i64,
        len: usize,
        value_layout: Box<FlatValueLayout>,
    },
    /// Function with a known finite scalar domain in canonical order.
    Function {
        domain: Vec<FlatScalarValue>,
        value_layout: Box<FlatValueLayout>,
    },
    /// Record with known field names and recursive field layouts.
    Record {
        field_names: Vec<Arc<str>>,
        field_layouts: Vec<FlatValueLayout>,
    },
    /// Finite scalar set encoded as one bitmask slot.
    SetBitmask { universe: Vec<FlatScalarValue> },
    /// Sequence with a fixed capacity. Slot 0 stores the current length.
    Sequence {
        bound: SequenceBoundEvidence,
        max_len: usize,
        element_layout: Box<FlatValueLayout>,
    },
}

impl FlatValueLayout {
    /// Number of compact i64 slots occupied by this fixed value layout.
    #[must_use]
    pub(crate) fn slot_count(&self) -> usize {
        match self {
            FlatValueLayout::Scalar(_) => 1,
            FlatValueLayout::IntFunction {
                len, value_layout, ..
            } => len * value_layout.slot_count(),
            FlatValueLayout::Function {
                domain,
                value_layout,
            } => domain.len() * value_layout.slot_count(),
            FlatValueLayout::Record { field_layouts, .. } => {
                field_layouts.iter().map(FlatValueLayout::slot_count).sum()
            }
            FlatValueLayout::SetBitmask { .. } => 1,
            FlatValueLayout::Sequence {
                max_len,
                element_layout,
                ..
            } => 1 + max_len * element_layout.slot_count(),
        }
    }

    /// True when this recursive layout contains a fixed-capacity sequence.
    #[must_use]
    pub(crate) fn contains_sequence(&self) -> bool {
        match self {
            FlatValueLayout::Sequence { .. } => true,
            FlatValueLayout::IntFunction { value_layout, .. }
            | FlatValueLayout::Function { value_layout, .. } => value_layout.contains_sequence(),
            FlatValueLayout::Record { field_layouts, .. } => {
                field_layouts.iter().any(FlatValueLayout::contains_sequence)
            }
            FlatValueLayout::Scalar(_) | FlatValueLayout::SetBitmask { .. } => false,
        }
    }

    /// True when every recursive sequence in this layout has both proven
    /// capacity and proven element layout.
    #[must_use]
    pub(crate) fn supports_flat_primary(&self) -> bool {
        match self {
            FlatValueLayout::Sequence {
                bound,
                element_layout,
                ..
            } => bound.supports_flat_primary() && element_layout.supports_flat_primary(),
            FlatValueLayout::IntFunction { value_layout, .. }
            | FlatValueLayout::Function { value_layout, .. } => {
                value_layout.supports_flat_primary()
            }
            FlatValueLayout::Record {
                field_names,
                field_layouts,
            } => {
                !is_variant_record_fields(field_names)
                    && field_layouts
                        .iter()
                        .all(FlatValueLayout::supports_flat_primary)
            }
            FlatValueLayout::Scalar(_) | FlatValueLayout::SetBitmask { .. } => true,
        }
    }
}

fn slot_type_supports_flat_primary(slot_type: SlotType) -> bool {
    matches!(slot_type, SlotType::Int | SlotType::Bool)
}

// Apalache variants are records with tag/value fields; the value slot can
// change type by tag, while raw flat-primary has no per-successor fallback.
fn is_variant_record_fields(field_names: &[Arc<str>]) -> bool {
    field_names.len() == 2
        && field_names.iter().any(|name| name.as_ref() == "tag")
        && field_names.iter().any(|name| name.as_ref() == "value")
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
    /// String — 1 slot. Interned NameId stored as i64.
    /// Distinct from `Scalar` so roundtrip produces `Value::String`.
    /// Part of #3908.
    ScalarString,
    /// ModelValue — 1 slot. Interned NameId stored as i64.
    /// Distinct from `Scalar` so roundtrip produces `Value::ModelValue`.
    /// Part of #3908.
    ScalarModelValue,
    /// Integer-indexed array `[lo..hi -> Int/Bool/String]` — `len` contiguous slots.
    /// Each element is a scalar i64 (int value, 0/1 for bool, or NameId for string).
    IntArray {
        /// Inclusive lower bound of the domain interval.
        lo: i64,
        /// Number of elements (= hi - lo + 1).
        len: usize,
        /// When true, all array elements are Bool-typed. Enables
        /// `reconstruct_int_array` to emit `Value::Bool(slot != 0)`
        /// instead of `Value::SmallInt(slot)`. Fixes #4014.
        elements_are_bool: bool,
        /// Per-element type tag. When `Some`, enables correct reconstruction
        /// of string/model-value elements. `None` means all elements are
        /// either Int or Bool (determined by `elements_are_bool`).
        /// Part of #3908.
        element_types: Option<Vec<SlotType>>,
    },
    /// Record with known field names — one scalar slot per field.
    /// Only applicable when ALL fields are scalar (Int/Bool/String/ModelValue).
    Record {
        /// Field names in canonical (sorted NameId) order.
        field_names: Vec<Arc<str>>,
        /// Per-field Bool type tracking. `field_is_bool[i]` is true when
        /// field `field_names[i]` holds a `Value::Bool`. This enables
        /// `reconstruct_record` to emit `Value::Bool(slot != 0)` instead
        /// of `Value::SmallInt(slot)` for Bool-typed fields. Fixes #4014.
        field_is_bool: Vec<bool>,
        /// Per-field type tag. Enables correct reconstruction of
        /// string/model-value fields. Part of #3908.
        field_types: Vec<SlotType>,
    },
    /// String-keyed function — `len` contiguous slots for values, domain keys
    /// stored as metadata. Used for `[{"a", "b"} -> Int]` patterns.
    /// Part of #3908: compound type flat state roundtrip.
    StringKeyedArray {
        /// Domain keys as interned NameId values, in canonical sorted order.
        domain_keys: Vec<Arc<str>>,
        /// Per-key type tag indicating whether each `domain_keys[i]` is a
        /// `Value::String` or `Value::ModelValue`. Without this, ModelValue
        /// domains (e.g. `RM = {rm1, rm2, rm3}` from a CONSTANTS config) are
        /// silently reconstructed as `Value::String` and fail the flat
        /// roundtrip equality check. Fixes #4277.
        domain_types: Vec<SlotType>,
        /// Per-element type tag for the range values.
        value_types: Vec<SlotType>,
    },
    /// Recursive fixed-size aggregate layout.
    Recursive { layout: FlatValueLayout },
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
            VarLayoutKind::Scalar
            | VarLayoutKind::ScalarBool
            | VarLayoutKind::ScalarString
            | VarLayoutKind::ScalarModelValue => 1,
            VarLayoutKind::IntArray { len, .. } => *len,
            VarLayoutKind::Record { field_names, .. } => field_names.len(),
            VarLayoutKind::StringKeyedArray { domain_keys, .. } => domain_keys.len(),
            VarLayoutKind::Recursive { layout } => layout.slot_count(),
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
        self.vars.iter().all(|v| {
            matches!(
                v.kind,
                VarLayoutKind::Scalar
                    | VarLayoutKind::ScalarBool
                    | VarLayoutKind::ScalarString
                    | VarLayoutKind::ScalarModelValue
            )
        })
    }

    /// True when every variable is either `Scalar`/`ScalarBool` or `Dynamic`.
    /// In this case the flat buffer has the same number of slots as variables.
    #[must_use]
    pub(crate) fn is_trivial(&self) -> bool {
        self.vars.iter().all(|v| {
            matches!(
                v.kind,
                VarLayoutKind::Scalar
                    | VarLayoutKind::ScalarBool
                    | VarLayoutKind::ScalarString
                    | VarLayoutKind::ScalarModelValue
                    | VarLayoutKind::Dynamic
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

    /// True when the flat buffer is safe as the primary BFS representation.
    ///
    /// `is_fully_flat()` only means every current variable has a fixed slot
    /// layout. Recursive sequences are primary-safe only when source-level
    /// invariants prove both the sequence capacity and the element layout.
    #[must_use]
    pub(crate) fn supports_flat_primary(&self) -> bool {
        self.is_fully_flat()
            && self.vars.iter().all(|var| match &var.kind {
                VarLayoutKind::Scalar | VarLayoutKind::ScalarBool => true,
                VarLayoutKind::ScalarString | VarLayoutKind::ScalarModelValue => false,
                VarLayoutKind::IntArray { element_types, .. } => {
                    element_types.as_ref().is_none_or(|types| {
                        types
                            .iter()
                            .all(|slot| slot_type_supports_flat_primary(*slot))
                    })
                }
                VarLayoutKind::Record {
                    field_names,
                    field_types,
                    ..
                } => {
                    !is_variant_record_fields(field_names)
                        && field_types
                            .iter()
                            .all(|slot| slot_type_supports_flat_primary(*slot))
                }
                VarLayoutKind::StringKeyedArray { value_types, .. } => value_types
                    .iter()
                    .all(|slot| slot_type_supports_flat_primary(*slot)),
                VarLayoutKind::Recursive { layout } => layout.supports_flat_primary(),
                VarLayoutKind::Bitmask { .. } => true,
                VarLayoutKind::Dynamic => false,
            })
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
                element_types: None,
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
                elements_are_bool: false,
                element_types: None,
            }
            .slot_count(),
            5
        );
        assert_eq!(
            VarLayoutKind::Record {
                field_names: vec![Arc::from("a"), Arc::from("b")],
                field_is_bool: vec![false, false],
                field_types: vec![SlotType::Int, SlotType::Int],
            }
            .slot_count(),
            2
        );
        assert_eq!(
            VarLayoutKind::Recursive {
                layout: FlatValueLayout::IntFunction {
                    lo: 1,
                    len: 2,
                    value_layout: Box::new(FlatValueLayout::SetBitmask {
                        universe: vec![FlatScalarValue::Int(1), FlatScalarValue::Int(2)],
                    }),
                },
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
                element_types: None,
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
    fn test_state_layout_variant_record_not_flat_primary_safe() {
        let registry = VarRegistry::from_names(["result"]);
        let kinds = vec![VarLayoutKind::Record {
            field_names: vec![Arc::from("tag"), Arc::from("value")],
            field_is_bool: vec![false, false],
            field_types: vec![SlotType::String, SlotType::String],
        }];
        let layout = StateLayout::new(&registry, kinds);

        assert!(layout.is_fully_flat());
        assert!(!layout.supports_flat_primary());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_layout_string_and_model_value_scalars_not_flat_primary_safe() {
        let registry = VarRegistry::from_names(["text", "token"]);
        let kinds = vec![VarLayoutKind::ScalarString, VarLayoutKind::ScalarModelValue];
        let layout = StateLayout::new(&registry, kinds);

        assert!(layout.is_fully_flat());
        assert!(!layout.supports_flat_primary());
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

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_primary_rejects_recursive_sequences_even_when_bound_proven() {
        let registry = VarRegistry::from_names(["network"]);
        let observed = StateLayout::new(
            &registry,
            vec![VarLayoutKind::Recursive {
                layout: FlatValueLayout::Sequence {
                    bound: SequenceBoundEvidence::Observed,
                    max_len: 3,
                    element_layout: Box::new(FlatValueLayout::Scalar(SlotType::Int)),
                },
            }],
        );
        assert!(observed.is_fully_flat());
        assert!(!observed.supports_flat_primary());

        let proven = StateLayout::new(
            &registry,
            vec![VarLayoutKind::Recursive {
                layout: FlatValueLayout::Sequence {
                    bound: SequenceBoundEvidence::ProvenInvariant {
                        invariant: Arc::from("BoundedNetwork"),
                    },
                    max_len: 3,
                    element_layout: Box::new(FlatValueLayout::Scalar(SlotType::Int)),
                },
            }],
        );
        assert!(proven.is_fully_flat());
        assert!(proven.vars[0].kind.slot_count() > 0);
        assert!(!proven.supports_flat_primary());

        let fixed_domain_type_layout = StateLayout::new(
            &registry,
            vec![VarLayoutKind::Recursive {
                layout: FlatValueLayout::Sequence {
                    bound: SequenceBoundEvidence::FixedDomainTypeLayout {
                        invariant: Arc::from("TypeOK"),
                    },
                    max_len: 3,
                    element_layout: Box::new(FlatValueLayout::Scalar(SlotType::Int)),
                },
            }],
        );
        assert!(fixed_domain_type_layout.is_fully_flat());
        assert!(fixed_domain_type_layout.supports_flat_primary());

        let proven_with_element_layout = StateLayout::new(
            &registry,
            vec![VarLayoutKind::Recursive {
                layout: FlatValueLayout::Sequence {
                    bound: SequenceBoundEvidence::ProvenInvariantWithElementLayout {
                        invariant: Arc::from("BoundedNetwork"),
                        element_invariant: Arc::from("TypeOK"),
                    },
                    max_len: 3,
                    element_layout: Box::new(FlatValueLayout::Record {
                        field_names: vec![Arc::from("clock"), Arc::from("type")],
                        field_layouts: vec![
                            FlatValueLayout::Scalar(SlotType::Int),
                            FlatValueLayout::Scalar(SlotType::String),
                        ],
                    }),
                },
            }],
        );
        assert!(proven_with_element_layout.is_fully_flat());
        assert!(proven_with_element_layout.supports_flat_primary());
    }
}
