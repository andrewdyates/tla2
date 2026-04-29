// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bridge between tla-check's `StateLayout` and tla-jit's `StateLayout`.
//!
//! The model checker (`tla-check`) and the JIT compiler (`tla-jit`) each have
//! their own `StateLayout` type with different trade-offs:
//!
//! | Property            | tla-check layout            | tla-jit layout             |
//! |--------------------|-----------------------------|----------------------------|
//! | Purpose            | BFS flat state storage      | Cranelift codegen metadata |
//! | Var descriptor     | `VarLayoutKind` (enum)      | `VarLayout` (enum)         |
//! | Compound support   | IntArray, Record, Bitmask   | CompoundLayout (recursive) |
//! | Offset tracking    | Built-in (contiguous pack)  | Compact/serialized APIs             |
//! | Buffer format      | Compact (no type tags)      | Self-describing (type tags)|
//!
//! This module provides conversion functions so that:
//!
//! 1. The JIT compiled BFS step can understand the model checker's layout.
//! 2. The model checker can convert JIT-produced buffers back to ArrayState.
//! 3. Layout compatibility is verified at BFS initialization time.
//!
//! # Buffer format conversion
//!
//! The two buffer formats are **not** directly compatible:
//!
//! - **tla-check format** (compact): `[raw_value, raw_value, ...]`
//!   - Scalar: 1 slot, raw i64
//!   - IntArray{lo, len}: `len` contiguous raw i64 values
//!   - Record{fields}: `len(fields)` contiguous raw i64 values
//!   - Dynamic: 1 slot, zero placeholder
//!
//! - **tla-jit format** (tagged): `[TAG, value, TAG, count, TAG, val, ...]`
//!   - Every value prefixed with a type tag word
//!   - Records include field count + per-field name_id
//!   - Self-describing for deserialization without layout
//!
//! For the JIT V2 BFS path, the compiled BFS step will operate directly on
//! the **compact** format (tla-check's). The JIT must generate code aware of
//! the slot offsets, not the self-describing format. This module provides the
//! layout metadata conversion that enables that code generation.
//!
//! Part of #3986: Phase 3 flat state buffer layout bridge.

use super::state_layout::{
    ordered_dense_int_domain, FlatScalarValue, FlatValueLayout, SlotType, StateLayout,
    VarLayoutKind,
};

/// Convert a tla-check `StateLayout` into the equivalent tla-jit `StateLayout`.
///
/// This enables JIT code generation to understand the model checker's flat
/// buffer format. The JIT can use the resulting layout to generate Cranelift IR
/// that reads/writes the compact (no type tags) buffer directly.
///
/// # Mapping
///
/// | tla-check `VarLayoutKind`     | tla-jit `VarLayout`                           |
/// |------------------------------|-----------------------------------------------|
/// | `Scalar`                     | `ScalarInt`                                   |
/// | `ScalarBool`                 | `ScalarBool`                                  |
/// | `ScalarString`               | `Compound(String)` (NameId as i64)            |
/// | `ScalarModelValue`           | `Compound(String)` (NameId as i64)            |
/// | `IntArray { lo, len, bool }` | `Compound(Function { Int->Int/Bool, n })`     |
/// | `Record { fields, bools }`   | `Compound(Record { fields })`                 |
/// | `StringKeyedArray { keys }`  | `Compound(Function { String->T, n })`         |
/// | `Recursive { layout }`       | Recursive `CompoundLayout`                    |
/// | `Recursive SetBitmask`       | `Compound(SetBitmask)` in one compact slot    |
/// | `Bitmask { size }`           | `ScalarInt` (bitmask is a single i64)         |
/// | `Dynamic`                    | `Compound(Dynamic)`                           |
///
/// Note: The returned jit layout describes the **compact** buffer format
/// (offsets match tla-check's slot packing), not the self-describing
/// tagged format used by `serialize_value()`.
#[must_use]
pub(crate) fn check_layout_to_jit_layout(check_layout: &StateLayout) -> tla_jit_abi::StateLayout {
    let jit_vars: Vec<tla_jit_abi::VarLayout> = check_layout
        .iter()
        .map(|var| check_var_to_jit_var(&var.kind))
        .collect();
    tla_jit_abi::StateLayout::new(jit_vars)
}

/// Convert a single tla-check `VarLayoutKind` to a tla-jit `VarLayout`.
fn check_var_to_jit_var(kind: &VarLayoutKind) -> tla_jit_abi::VarLayout {
    match kind {
        VarLayoutKind::Scalar => tla_jit_abi::VarLayout::ScalarInt,
        VarLayoutKind::ScalarBool => tla_jit_abi::VarLayout::ScalarBool,
        VarLayoutKind::IntArray {
            lo,
            len,
            elements_are_bool,
            element_types,
        } => {
            let value_layout = int_array_value_layout(*elements_are_bool, element_types.as_deref());
            tla_jit_abi::VarLayout::Compound(tla_jit_abi::CompoundLayout::Function {
                key_layout: Box::new(tla_jit_abi::CompoundLayout::Int),
                value_layout: Box::new(value_layout),
                pair_count: Some(*len),
                domain_lo: Some(*lo),
            })
        }
        VarLayoutKind::Record {
            field_names,
            field_types,
            ..
        } => {
            let fields: Vec<(tla_core::NameId, tla_jit_abi::CompoundLayout)> = field_names
                .iter()
                .zip(field_types.iter())
                .map(|(name, ty)| {
                    let nid = tla_core::intern_name(name);
                    let layout = match ty {
                        super::state_layout::SlotType::Bool => tla_jit_abi::CompoundLayout::Bool,
                        super::state_layout::SlotType::String
                        | super::state_layout::SlotType::ModelValue => {
                            tla_jit_abi::CompoundLayout::String
                        }
                        super::state_layout::SlotType::Int => tla_jit_abi::CompoundLayout::Int,
                    };
                    (nid, layout)
                })
                .collect();
            tla_jit_abi::VarLayout::Compound(tla_jit_abi::CompoundLayout::Record { fields })
        }
        VarLayoutKind::ScalarString | VarLayoutKind::ScalarModelValue => {
            // String/ModelValue scalars are interned NameIds stored as i64.
            // Preserve their scalar lane so tMIR can distinguish string
            // equality from integer equality after flat-primary promotion.
            tla_jit_abi::VarLayout::Compound(tla_jit_abi::CompoundLayout::String)
        }
        VarLayoutKind::StringKeyedArray {
            domain_keys,
            value_types,
            ..
        } => {
            // String-keyed function: `domain_keys.len()` contiguous i64 slots
            // for the range values. Domain keys are metadata (not in buffer).
            // Map as Function { String -> value_type, n, lo=None }.
            // The value layout is the common element type, or Int if mixed.
            let value_layout = uniform_slot_types_to_jit_compound(value_types);
            tla_jit_abi::VarLayout::Compound(tla_jit_abi::CompoundLayout::Function {
                key_layout: Box::new(tla_jit_abi::CompoundLayout::String),
                value_layout: Box::new(value_layout),
                pair_count: Some(domain_keys.len()),
                domain_lo: None,
            })
        }
        VarLayoutKind::Recursive { layout } => {
            tla_jit_abi::VarLayout::Compound(flat_value_layout_to_jit_compound(layout))
        }
        VarLayoutKind::Bitmask { .. } => {
            // Bitmask is a single i64 slot — treat as scalar for JIT purposes.
            tla_jit_abi::VarLayout::ScalarInt
        }
        VarLayoutKind::Dynamic => {
            tla_jit_abi::VarLayout::Compound(tla_jit_abi::CompoundLayout::Dynamic)
        }
    }
}

fn int_array_value_layout(
    elements_are_bool: bool,
    element_types: Option<&[super::state_layout::SlotType]>,
) -> tla_jit_abi::CompoundLayout {
    match element_types {
        Some(types) => uniform_slot_types_to_jit_compound(types),
        None if elements_are_bool => tla_jit_abi::CompoundLayout::Bool,
        None => tla_jit_abi::CompoundLayout::Int,
    }
}

fn uniform_slot_types_to_jit_compound(
    slot_types: &[super::state_layout::SlotType],
) -> tla_jit_abi::CompoundLayout {
    use super::state_layout::SlotType;

    let Some(first) = slot_types.first() else {
        return tla_jit_abi::CompoundLayout::Dynamic;
    };
    if !slot_types.iter().all(|slot_type| slot_type == first) {
        return tla_jit_abi::CompoundLayout::Dynamic;
    }
    match first {
        SlotType::Bool => tla_jit_abi::CompoundLayout::Bool,
        SlotType::String | SlotType::ModelValue => tla_jit_abi::CompoundLayout::String,
        SlotType::Int => tla_jit_abi::CompoundLayout::Int,
    }
}

fn flat_value_layout_to_jit_compound(
    layout: &super::state_layout::FlatValueLayout,
) -> tla_jit_abi::CompoundLayout {
    match layout {
        super::state_layout::FlatValueLayout::Scalar(slot_type) => {
            slot_type_to_jit_compound(*slot_type)
        }
        super::state_layout::FlatValueLayout::IntFunction {
            lo,
            len,
            value_layout,
        } => tla_jit_abi::CompoundLayout::Function {
            key_layout: Box::new(tla_jit_abi::CompoundLayout::Int),
            value_layout: Box::new(flat_value_layout_to_jit_compound(value_layout)),
            pair_count: Some(*len),
            domain_lo: Some(*lo),
        },
        super::state_layout::FlatValueLayout::Function {
            domain,
            value_layout,
        } => {
            let value_layout = Box::new(flat_value_layout_to_jit_compound(value_layout));
            if let Some((lo, len)) = ordered_dense_int_domain(domain) {
                tla_jit_abi::CompoundLayout::Function {
                    key_layout: Box::new(tla_jit_abi::CompoundLayout::Int),
                    value_layout,
                    pair_count: Some(len),
                    domain_lo: Some(lo),
                }
            } else {
                tla_jit_abi::CompoundLayout::Function {
                    key_layout: Box::new(flat_domain_to_jit_compound(domain)),
                    value_layout,
                    pair_count: Some(domain.len()),
                    domain_lo: None,
                }
            }
        }
        super::state_layout::FlatValueLayout::Record {
            field_names,
            field_layouts,
        } => {
            let fields = field_names
                .iter()
                .zip(field_layouts.iter())
                .map(|(name, field_layout)| {
                    (
                        tla_core::intern_name(name),
                        flat_value_layout_to_jit_compound(field_layout),
                    )
                })
                .collect();
            tla_jit_abi::CompoundLayout::Record { fields }
        }
        super::state_layout::FlatValueLayout::SetBitmask { universe } => {
            tla_jit_abi::CompoundLayout::SetBitmask {
                universe: universe
                    .iter()
                    .map(flat_scalar_to_jit_bitmask_element)
                    .collect(),
            }
        }
        super::state_layout::FlatValueLayout::Sequence {
            max_len,
            element_layout,
            ..
        } => tla_jit_abi::CompoundLayout::Sequence {
            element_layout: Box::new(flat_value_layout_to_jit_compound(element_layout)),
            element_count: Some(*max_len),
        },
    }
}

fn slot_type_to_jit_compound(
    slot_type: super::state_layout::SlotType,
) -> tla_jit_abi::CompoundLayout {
    match slot_type {
        super::state_layout::SlotType::Bool => tla_jit_abi::CompoundLayout::Bool,
        super::state_layout::SlotType::String | super::state_layout::SlotType::ModelValue => {
            tla_jit_abi::CompoundLayout::String
        }
        super::state_layout::SlotType::Int => tla_jit_abi::CompoundLayout::Int,
    }
}

fn flat_domain_to_jit_compound(
    domain: &[super::state_layout::FlatScalarValue],
) -> tla_jit_abi::CompoundLayout {
    let Some(first) = domain.first() else {
        return tla_jit_abi::CompoundLayout::Dynamic;
    };
    let first_type = first.slot_type();
    if domain.iter().all(|key| key.slot_type() == first_type) {
        slot_type_to_jit_compound(first_type)
    } else {
        tla_jit_abi::CompoundLayout::Dynamic
    }
}

fn flat_scalar_to_jit_bitmask_element(
    value: &super::state_layout::FlatScalarValue,
) -> tla_jit_abi::SetBitmaskElement {
    match value {
        super::state_layout::FlatScalarValue::Int(n) => tla_jit_abi::SetBitmaskElement::Int(*n),
        super::state_layout::FlatScalarValue::Bool(b) => tla_jit_abi::SetBitmaskElement::Bool(*b),
        super::state_layout::FlatScalarValue::String(s) => {
            tla_jit_abi::SetBitmaskElement::String(tla_core::intern_name(s))
        }
        super::state_layout::FlatScalarValue::ModelValue(s) => {
            tla_jit_abi::SetBitmaskElement::ModelValue(tla_core::intern_name(s))
        }
    }
}

fn jit_bitmask_element_to_flat_scalar(
    value: tla_jit_abi::SetBitmaskElement,
) -> super::state_layout::FlatScalarValue {
    match value {
        tla_jit_abi::SetBitmaskElement::Int(n) => super::state_layout::FlatScalarValue::Int(n),
        tla_jit_abi::SetBitmaskElement::Bool(b) => super::state_layout::FlatScalarValue::Bool(b),
        tla_jit_abi::SetBitmaskElement::String(name) => {
            super::state_layout::FlatScalarValue::String(tla_core::resolve_name_id(name))
        }
        tla_jit_abi::SetBitmaskElement::ModelValue(name) => {
            super::state_layout::FlatScalarValue::ModelValue(tla_core::resolve_name_id(name))
        }
    }
}

/// Convert a tla-jit `StateLayout` into the equivalent tla-check `StateLayout`.
///
/// This is the inverse of `check_layout_to_jit_layout`. Used when the JIT
/// produces a layout (e.g., from `infer_var_layout`) and the model checker
/// needs to create a compatible flat buffer.
///
/// Requires a `VarRegistry` to populate variable names in the tla-check layout.
///
/// # Mapping
///
/// | tla-jit `VarLayout`           | tla-check `VarLayoutKind`                     |
/// |------------------------------|-----------------------------------------------|
/// | `ScalarInt`                  | `Scalar`                                      |
/// | `ScalarBool`                 | `ScalarBool`                                  |
/// | `Compound(Function{Int,*,n,lo})` | `IntArray { lo, len }` (if int-array-like) |
/// | `Compound(Record{fields})`   | `Record { field_names }` (if all scalar)      |
/// | `Compound(Dynamic)`          | `Dynamic`                                     |
/// | Other `Compound`             | `Dynamic` (fallback)                          |
#[must_use]
pub(crate) fn jit_layout_to_check_layout(
    jit_layout: &tla_jit_abi::StateLayout,
    registry: &crate::var_index::VarRegistry,
) -> StateLayout {
    let kinds: Vec<VarLayoutKind> = (0..jit_layout.var_count())
        .map(|i| {
            let jit_var = jit_layout
                .var_layout(i)
                .expect("jit layout var_count mismatch");
            jit_var_to_check_var(jit_var)
        })
        .collect();
    StateLayout::new(registry, kinds)
}

/// Convert a single tla-jit `VarLayout` to a tla-check `VarLayoutKind`.
fn jit_var_to_check_var(jit_var: &tla_jit_abi::VarLayout) -> VarLayoutKind {
    match jit_var {
        tla_jit_abi::VarLayout::ScalarInt => VarLayoutKind::Scalar,
        tla_jit_abi::VarLayout::ScalarBool => VarLayoutKind::ScalarBool,
        tla_jit_abi::VarLayout::Compound(compound) => compound_to_check_var(compound),
        // non_exhaustive: future VarLayout variants fall back to Dynamic.
        _ => VarLayoutKind::Dynamic,
    }
}

/// Convert a tla-jit `CompoundLayout` to a tla-check `VarLayoutKind`.
fn compound_to_check_var(compound: &tla_jit_abi::CompoundLayout) -> VarLayoutKind {
    match compound {
        tla_jit_abi::CompoundLayout::Int => VarLayoutKind::Scalar,
        tla_jit_abi::CompoundLayout::Bool => VarLayoutKind::ScalarBool,
        tla_jit_abi::CompoundLayout::String => VarLayoutKind::ScalarString,

        // Integer-array function: [lo..hi -> Int/Bool]
        tla_jit_abi::CompoundLayout::Function {
            key_layout,
            value_layout,
            pair_count: Some(len),
            domain_lo: Some(lo),
        } if key_layout.is_scalar() && value_layout.is_scalar() => {
            let elements_are_bool = matches!(**value_layout, tla_jit_abi::CompoundLayout::Bool);
            VarLayoutKind::IntArray {
                lo: *lo,
                len: *len,
                elements_are_bool,
                element_types: None,
            }
        }

        // String-keyed function: [{"a","b"} -> Int/Bool/String]
        // Reverse of StringKeyedArray -> Function { String -> T, n, None }.
        // Part of #3908.
        tla_jit_abi::CompoundLayout::Function {
            key_layout,
            value_layout,
            pair_count: Some(len),
            domain_lo: None,
        } if matches!(**key_layout, tla_jit_abi::CompoundLayout::String)
            && value_layout.is_scalar() =>
        {
            // We cannot recover the domain key strings from the JIT layout
            // alone (NameIds are not stored). Return Dynamic as a safe fallback
            // for the reverse direction. The forward direction (check -> jit) is
            // what matters for JIT compilation; the reverse is only used for
            // testing roundtrips which typically go through the check layout.
            // To make this fully invertible we'd need to store domain_keys in
            // the JIT CompoundLayout, which is future work.
            let _ = len;
            VarLayoutKind::Dynamic
        }

        // Record with all-scalar fields
        tla_jit_abi::CompoundLayout::Record { fields } => {
            let all_scalar = fields.iter().all(|(_, layout)| layout.is_scalar());
            if all_scalar && !fields.is_empty() {
                let field_names: Vec<std::sync::Arc<str>> = fields
                    .iter()
                    .map(|(nid, _)| tla_core::resolve_name_id(*nid))
                    .collect();
                let field_is_bool: Vec<bool> = fields
                    .iter()
                    .map(|(_, layout)| matches!(layout, tla_jit_abi::CompoundLayout::Bool))
                    .collect();
                let field_types: Vec<super::state_layout::SlotType> = fields
                    .iter()
                    .map(|(_, layout)| match layout {
                        tla_jit_abi::CompoundLayout::Bool => super::state_layout::SlotType::Bool,
                        tla_jit_abi::CompoundLayout::String => {
                            super::state_layout::SlotType::String
                        }
                        _ => super::state_layout::SlotType::Int,
                    })
                    .collect();
                VarLayoutKind::Record {
                    field_names,
                    field_is_bool,
                    field_types,
                }
            } else {
                VarLayoutKind::Dynamic
            }
        }

        // Explicit dynamic
        tla_jit_abi::CompoundLayout::Dynamic => VarLayoutKind::Dynamic,

        tla_jit_abi::CompoundLayout::SetBitmask { universe } => VarLayoutKind::Recursive {
            layout: super::state_layout::FlatValueLayout::SetBitmask {
                universe: universe
                    .iter()
                    .copied()
                    .map(jit_bitmask_element_to_flat_scalar)
                    .collect(),
            },
        },

        // All other compound types: fallback to Dynamic
        _ => VarLayoutKind::Dynamic,
    }
}

/// Verify that two layouts are structurally compatible for buffer sharing.
///
/// Two layouts are compatible when they produce the same total slot count,
/// each variable maps to the same compact offset/width, and compound shapes
/// agree recursively. This means a flat buffer created with one layout can be
/// read by code using the other without changing bit meaning.
///
/// Does NOT require the layouts to be identical — scalar slot-compatible
/// shapes may still share a buffer.
/// For example, tla-check's `IntArray{lo=0, len=3}` is compatible with
/// tla-jit's `Compound(Function{Int->Int, n=3, lo=0})` because both
/// produce 3 contiguous i64 slots.
#[must_use]
pub(crate) fn layouts_compatible(
    check_layout: &StateLayout,
    jit_layout: &tla_jit_abi::StateLayout,
) -> bool {
    if check_layout.var_count() != jit_layout.var_count() {
        return false;
    }

    let jit_offsets = jit_layout.compute_compact_var_offsets();
    for i in 0..check_layout.var_count() {
        let check_var = check_layout
            .var_layout(i)
            .expect("check var_count mismatch");
        let jit_var = jit_layout.var_layout(i).expect("jit var_count mismatch");

        let check_slots = check_var.kind.slot_count();
        let jit_slots = jit_var.compact_slot_count();

        if check_var.offset != jit_offsets[i] || check_slots != jit_slots {
            return false;
        }

        if !compact_var_layouts_compatible(&check_var.kind, jit_var) {
            return false;
        }
    }

    true
}

fn compact_var_layouts_compatible(
    check_kind: &VarLayoutKind,
    jit_var: &tla_jit_abi::VarLayout,
) -> bool {
    match check_kind {
        VarLayoutKind::Scalar => scalar_var_compatible(SlotType::Int, jit_var),
        VarLayoutKind::ScalarBool => scalar_var_compatible(SlotType::Bool, jit_var),
        VarLayoutKind::ScalarString | VarLayoutKind::ScalarModelValue => {
            scalar_var_compatible(SlotType::String, jit_var)
        }
        VarLayoutKind::IntArray {
            lo,
            len,
            elements_are_bool,
            element_types,
        } => match jit_var {
            tla_jit_abi::VarLayout::Compound(tla_jit_abi::CompoundLayout::Function {
                key_layout,
                value_layout,
                pair_count: Some(pair_count),
                domain_lo: Some(domain_lo),
            }) => {
                matches!(key_layout.as_ref(), tla_jit_abi::CompoundLayout::Int)
                    && lo == domain_lo
                    && len == pair_count
                    && compound_layout_matches_slot_types(
                        value_layout,
                        *elements_are_bool,
                        element_types.as_deref(),
                    )
            }
            _ => false,
        },
        VarLayoutKind::Record {
            field_names,
            field_types,
            ..
        } => match jit_var {
            tla_jit_abi::VarLayout::Compound(tla_jit_abi::CompoundLayout::Record { fields }) => {
                fields.len() == field_names.len()
                    && field_names
                        .iter()
                        .zip(field_types.iter())
                        .zip(fields.iter())
                        .all(|((check_name, check_type), (jit_name, jit_layout))| {
                            tla_core::intern_name(check_name) == *jit_name
                                && compound_layout_matches_slot_type(jit_layout, *check_type)
                        })
            }
            _ => false,
        },
        VarLayoutKind::StringKeyedArray {
            domain_keys,
            value_types,
            ..
        } => match jit_var {
            tla_jit_abi::VarLayout::Compound(tla_jit_abi::CompoundLayout::Function {
                key_layout,
                value_layout,
                pair_count: Some(pair_count),
                domain_lo: None,
            }) => {
                matches!(key_layout.as_ref(), tla_jit_abi::CompoundLayout::String)
                    && *pair_count == domain_keys.len()
                    && compound_layout_matches_uniform_slot_types(value_layout, value_types)
            }
            _ => false,
        },
        VarLayoutKind::Recursive { layout } => match jit_var {
            tla_jit_abi::VarLayout::Compound(jit_layout) => {
                flat_layout_compact_compatible(layout, jit_layout)
            }
            _ => false,
        },
        VarLayoutKind::Bitmask { .. } => matches!(jit_var, tla_jit_abi::VarLayout::ScalarInt),
        VarLayoutKind::Dynamic => matches!(
            jit_var,
            tla_jit_abi::VarLayout::Compound(tla_jit_abi::CompoundLayout::Dynamic)
        ),
    }
}

fn scalar_var_compatible(slot_type: SlotType, jit_var: &tla_jit_abi::VarLayout) -> bool {
    match (slot_type, jit_var) {
        (SlotType::Int, tla_jit_abi::VarLayout::ScalarInt)
        | (SlotType::Bool, tla_jit_abi::VarLayout::ScalarBool) => true,
        (_, tla_jit_abi::VarLayout::Compound(layout)) => {
            compound_layout_matches_slot_type(layout, slot_type)
        }
        _ => false,
    }
}

fn compound_layout_matches_slot_types(
    jit: &tla_jit_abi::CompoundLayout,
    elements_are_bool: bool,
    slot_types: Option<&[SlotType]>,
) -> bool {
    match slot_types {
        Some(types) => compound_layout_matches_uniform_slot_types(jit, types),
        None if elements_are_bool => compound_layout_matches_slot_type(jit, SlotType::Bool),
        None => compound_layout_matches_slot_type(jit, SlotType::Int),
    }
}

fn compound_layout_matches_uniform_slot_types(
    jit: &tla_jit_abi::CompoundLayout,
    slot_types: &[SlotType],
) -> bool {
    let Some(first) = slot_types.first() else {
        return matches!(jit, tla_jit_abi::CompoundLayout::Dynamic);
    };
    if !slot_types.iter().all(|slot_type| slot_type == first) {
        return matches!(jit, tla_jit_abi::CompoundLayout::Dynamic);
    }
    compound_layout_matches_slot_type(jit, *first)
}

fn compound_layout_matches_slot_type(
    jit: &tla_jit_abi::CompoundLayout,
    slot_type: SlotType,
) -> bool {
    matches!(
        (slot_type, jit),
        (SlotType::Int, tla_jit_abi::CompoundLayout::Int)
            | (SlotType::Bool, tla_jit_abi::CompoundLayout::Bool)
            | (
                SlotType::String | SlotType::ModelValue,
                tla_jit_abi::CompoundLayout::String
            )
    )
}

fn flat_layout_compact_compatible(
    check: &FlatValueLayout,
    jit: &tla_jit_abi::CompoundLayout,
) -> bool {
    match (check, jit) {
        (FlatValueLayout::Scalar(slot_type), _) => {
            compound_layout_matches_slot_type(jit, *slot_type)
        }
        (
            FlatValueLayout::SetBitmask { universe: check },
            tla_jit_abi::CompoundLayout::SetBitmask { universe: jit },
        ) => set_bitmask_universe_compatible(check, jit),
        (
            FlatValueLayout::IntFunction {
                lo,
                len,
                value_layout,
            },
            tla_jit_abi::CompoundLayout::Function {
                key_layout,
                pair_count: Some(pair_count),
                domain_lo: Some(domain_lo),
                value_layout: jit_value,
            },
        ) => {
            matches!(key_layout.as_ref(), tla_jit_abi::CompoundLayout::Int)
                && lo == domain_lo
                && len == pair_count
                && flat_layout_compact_compatible(value_layout, jit_value)
        }
        (
            FlatValueLayout::Function {
                domain,
                value_layout,
            },
            tla_jit_abi::CompoundLayout::Function {
                key_layout,
                pair_count: Some(pair_count),
                domain_lo: Some(domain_lo),
                value_layout: jit_value,
            },
        ) => {
            matches!(key_layout.as_ref(), tla_jit_abi::CompoundLayout::Int)
                && ordered_dense_int_domain(domain) == Some((*domain_lo, *pair_count))
                && flat_layout_compact_compatible(value_layout, jit_value)
        }
        (
            FlatValueLayout::Function {
                domain,
                value_layout,
            },
            tla_jit_abi::CompoundLayout::Function {
                key_layout,
                pair_count: Some(pair_count),
                domain_lo: None,
                value_layout: jit_value,
            },
        ) => {
            domain.len() == *pair_count
                && ordered_dense_int_domain(domain).is_none()
                && flat_domain_compact_compatible(domain, key_layout)
                && flat_layout_compact_compatible(value_layout, jit_value)
        }
        (
            FlatValueLayout::Record {
                field_names,
                field_layouts,
            },
            tla_jit_abi::CompoundLayout::Record { fields },
        ) if field_names.len() == fields.len() => field_names
            .iter()
            .zip(field_layouts.iter())
            .zip(fields.iter())
            .all(|((check_name, check_layout), (jit_name, jit_layout))| {
                tla_core::intern_name(check_name) == *jit_name
                    && flat_layout_compact_compatible(check_layout, jit_layout)
            }),
        (
            FlatValueLayout::Sequence {
                max_len,
                element_layout,
                ..
            },
            tla_jit_abi::CompoundLayout::Sequence {
                element_count: Some(element_count),
                element_layout: jit_element,
            },
        ) => {
            max_len == element_count && flat_layout_compact_compatible(element_layout, jit_element)
        }
        _ => false,
    }
}

fn flat_domain_compact_compatible(
    domain: &[FlatScalarValue],
    jit: &tla_jit_abi::CompoundLayout,
) -> bool {
    let Some(first) = domain.first() else {
        return matches!(jit, tla_jit_abi::CompoundLayout::Dynamic);
    };
    let first_type = first.slot_type();
    domain.iter().all(|key| key.slot_type() == first_type)
        && compound_layout_matches_slot_type(jit, first_type)
}

fn set_bitmask_universe_compatible(
    check: &[FlatScalarValue],
    jit: &[tla_jit_abi::SetBitmaskElement],
) -> bool {
    check.len() == jit.len()
        && check
            .iter()
            .zip(jit.iter())
            .all(|(check, jit)| flat_scalar_to_jit_bitmask_element(check) == *jit)
}

/// Compute the compact (no-tag) slot count for an entire JIT layout.
///
/// This matches the check-side flat buffer width, not the JIT tagged
/// serialization width.
#[must_use]
pub(crate) fn jit_layout_compact_slot_count(jit_layout: &tla_jit_abi::StateLayout) -> usize {
    jit_layout.compact_slot_count()
}

/// Return the first variable whose check and JIT compact slot widths disagree.
#[must_use]
pub(crate) fn first_layout_slot_mismatch(
    check_layout: &StateLayout,
    jit_layout: &tla_jit_abi::StateLayout,
) -> Option<(usize, usize, usize)> {
    let count = check_layout.var_count().min(jit_layout.var_count());
    for i in 0..count {
        let check_slots = check_layout.var_layout(i)?.kind.slot_count();
        let jit_slots = jit_layout.var_layout(i)?.compact_slot_count();
        if check_slots != jit_slots {
            return Some((i, check_slots, jit_slots));
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::layout_inference::infer_layout;
    use crate::state::ArrayState;
    use crate::var_index::VarRegistry;
    use crate::Value;
    use std::sync::Arc;
    use tla_value::value::IntIntervalFunc;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_check_to_jit_all_scalar() {
        let registry = VarRegistry::from_names(["x", "y", "z"]);
        let state = ArrayState::from_values(vec![
            Value::SmallInt(42),
            Value::Bool(true),
            Value::SmallInt(-7),
        ]);
        let check_layout = infer_layout(&state, &registry);
        let jit_layout = check_layout_to_jit_layout(&check_layout);

        assert_eq!(jit_layout.var_count(), 3);
        assert!(jit_layout.is_all_scalar());

        // Verify individual var layouts
        assert_eq!(
            jit_layout.var_layout(0),
            Some(&tla_jit_abi::VarLayout::ScalarInt)
        );
        assert_eq!(
            jit_layout.var_layout(1),
            Some(&tla_jit_abi::VarLayout::ScalarBool)
        );
        assert_eq!(
            jit_layout.var_layout(2),
            Some(&tla_jit_abi::VarLayout::ScalarInt)
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_check_to_jit_int_array() {
        let registry = VarRegistry::from_names(["active"]);
        let func = IntIntervalFunc::new(
            0,
            2,
            vec![Value::Bool(false), Value::Bool(true), Value::Bool(false)],
        );
        let state = ArrayState::from_values(vec![Value::IntFunc(Arc::new(func))]);
        let check_layout = infer_layout(&state, &registry);
        let jit_layout = check_layout_to_jit_layout(&check_layout);

        assert_eq!(jit_layout.var_count(), 1);
        let var = jit_layout.var_layout(0).unwrap();
        match var {
            tla_jit_abi::VarLayout::Compound(tla_jit_abi::CompoundLayout::Function {
                pair_count,
                domain_lo,
                ..
            }) => {
                assert_eq!(*pair_count, Some(3));
                assert_eq!(*domain_lo, Some(0));
            }
            other => panic!("expected Compound(Function), got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_recursive_set_bitmask_keeps_set_shape_and_one_compact_slot() {
        use super::super::state_layout::{FlatScalarValue, FlatValueLayout};

        let registry = VarRegistry::from_names(["ack"]);
        let proc_domain = vec![
            FlatScalarValue::Int(1),
            FlatScalarValue::Int(2),
            FlatScalarValue::Int(3),
        ];
        let check_layout = StateLayout::new(
            &registry,
            vec![VarLayoutKind::Recursive {
                layout: FlatValueLayout::IntFunction {
                    lo: 1,
                    len: 3,
                    value_layout: Box::new(FlatValueLayout::SetBitmask {
                        universe: proc_domain,
                    }),
                },
            }],
        );

        let jit_layout = check_layout_to_jit_layout(&check_layout);

        assert_eq!(check_layout.total_slots(), 3);
        assert_eq!(jit_layout_compact_slot_count(&jit_layout), 3);
        assert_eq!(first_layout_slot_mismatch(&check_layout, &jit_layout), None);
        assert!(layouts_compatible(&check_layout, &jit_layout));
        match jit_layout.var_layout(0).unwrap() {
            tla_jit_abi::VarLayout::Compound(tla_jit_abi::CompoundLayout::Function {
                value_layout,
                ..
            }) => match value_layout.as_ref() {
                tla_jit_abi::CompoundLayout::SetBitmask { universe } => {
                    assert_eq!(
                        universe.as_slice(),
                        &[
                            tla_jit_abi::SetBitmaskElement::Int(1),
                            tla_jit_abi::SetBitmaskElement::Int(2),
                            tla_jit_abi::SetBitmaskElement::Int(3),
                        ]
                    );
                }
                other => panic!("expected set-bitmask range layout, got {other:?}"),
            },
            other => panic!("expected recursive function layout, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_recursive_set_bitmask_plus_tail_uses_abi_compact_offsets() {
        use super::super::state_layout::{FlatScalarValue, FlatValueLayout};

        let registry = VarRegistry::from_names(["ack", "tail"]);
        let check_layout = StateLayout::new(
            &registry,
            vec![
                VarLayoutKind::Recursive {
                    layout: FlatValueLayout::IntFunction {
                        lo: 1,
                        len: 3,
                        value_layout: Box::new(FlatValueLayout::SetBitmask {
                            universe: vec![
                                FlatScalarValue::Int(1),
                                FlatScalarValue::Int(2),
                                FlatScalarValue::Int(3),
                            ],
                        }),
                    },
                },
                VarLayoutKind::ScalarBool,
            ],
        );
        let jit_layout = check_layout_to_jit_layout(&check_layout);

        assert_eq!(check_layout.total_slots(), 4);
        assert_eq!(check_layout.var_layout(1).unwrap().offset, 3);
        assert_eq!(jit_layout.compact_slot_count(), 4);
        assert_eq!(jit_layout.compute_compact_var_offsets(), vec![0, 3]);
        assert_eq!(jit_layout.compute_var_offsets(), vec![Some(0), Some(11)]);
        assert_ne!(
            jit_layout.compute_compact_var_offsets(),
            jit_layout
                .compute_var_offsets()
                .into_iter()
                .map(|offset| offset.unwrap())
                .collect::<Vec<_>>()
        );
        assert_eq!(first_layout_slot_mismatch(&check_layout, &jit_layout), None);
        assert!(layouts_compatible(&check_layout, &jit_layout));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_layouts_incompatible_recursive_set_bitmask_universe_value_mismatch() {
        use super::super::state_layout::{FlatScalarValue, FlatValueLayout};

        let registry = VarRegistry::from_names(["ack"]);
        let check_layout = StateLayout::new(
            &registry,
            vec![VarLayoutKind::Recursive {
                layout: FlatValueLayout::IntFunction {
                    lo: 1,
                    len: 3,
                    value_layout: Box::new(FlatValueLayout::SetBitmask {
                        universe: vec![
                            FlatScalarValue::Int(1),
                            FlatScalarValue::Int(2),
                            FlatScalarValue::Int(3),
                        ],
                    }),
                },
            }],
        );
        let jit_layout = tla_jit_abi::StateLayout::new(vec![tla_jit_abi::VarLayout::Compound(
            tla_jit_abi::CompoundLayout::Function {
                key_layout: Box::new(tla_jit_abi::CompoundLayout::Int),
                value_layout: Box::new(tla_jit_abi::CompoundLayout::SetBitmask {
                    universe: vec![
                        tla_jit_abi::SetBitmaskElement::Int(1),
                        tla_jit_abi::SetBitmaskElement::Int(2),
                        tla_jit_abi::SetBitmaskElement::Int(4),
                    ],
                }),
                pair_count: Some(3),
                domain_lo: Some(1),
            },
        )]);

        assert_eq!(first_layout_slot_mismatch(&check_layout, &jit_layout), None);
        assert!(!layouts_compatible(&check_layout, &jit_layout));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_layouts_incompatible_recursive_set_bitmask_universe_order_mismatch() {
        use super::super::state_layout::{FlatScalarValue, FlatValueLayout};

        let registry = VarRegistry::from_names(["ack"]);
        let check_layout = StateLayout::new(
            &registry,
            vec![VarLayoutKind::Recursive {
                layout: FlatValueLayout::IntFunction {
                    lo: 1,
                    len: 3,
                    value_layout: Box::new(FlatValueLayout::SetBitmask {
                        universe: vec![
                            FlatScalarValue::Int(1),
                            FlatScalarValue::Int(2),
                            FlatScalarValue::Int(3),
                        ],
                    }),
                },
            }],
        );
        let jit_layout = tla_jit_abi::StateLayout::new(vec![tla_jit_abi::VarLayout::Compound(
            tla_jit_abi::CompoundLayout::Function {
                key_layout: Box::new(tla_jit_abi::CompoundLayout::Int),
                value_layout: Box::new(tla_jit_abi::CompoundLayout::SetBitmask {
                    universe: vec![
                        tla_jit_abi::SetBitmaskElement::Int(2),
                        tla_jit_abi::SetBitmaskElement::Int(1),
                        tla_jit_abi::SetBitmaskElement::Int(3),
                    ],
                }),
                pair_count: Some(3),
                domain_lo: Some(1),
            },
        )]);

        assert_eq!(first_layout_slot_mismatch(&check_layout, &jit_layout), None);
        assert!(!layouts_compatible(&check_layout, &jit_layout));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_layouts_incompatible_recursive_set_bitmask_replaced_by_scalar() {
        use super::super::state_layout::{FlatScalarValue, FlatValueLayout};

        let registry = VarRegistry::from_names(["enabled"]);
        let check_layout = StateLayout::new(
            &registry,
            vec![VarLayoutKind::Recursive {
                layout: FlatValueLayout::SetBitmask {
                    universe: vec![FlatScalarValue::Int(1), FlatScalarValue::Int(2)],
                },
            }],
        );
        let jit_layout = tla_jit_abi::StateLayout::new(vec![tla_jit_abi::VarLayout::ScalarInt]);

        assert_eq!(first_layout_slot_mismatch(&check_layout, &jit_layout), None);
        assert!(!layouts_compatible(&check_layout, &jit_layout));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_layouts_incompatible_sequence_set_bitmask_universe_mismatch() {
        use super::super::state_layout::{FlatScalarValue, FlatValueLayout, SequenceBoundEvidence};

        let registry = VarRegistry::from_names(["history"]);
        let check_layout = StateLayout::new(
            &registry,
            vec![VarLayoutKind::Recursive {
                layout: FlatValueLayout::Sequence {
                    bound: SequenceBoundEvidence::ProvenInvariant {
                        invariant: Arc::from("BoundedHistory"),
                    },
                    max_len: 2,
                    element_layout: Box::new(FlatValueLayout::SetBitmask {
                        universe: vec![
                            FlatScalarValue::Int(1),
                            FlatScalarValue::Int(2),
                            FlatScalarValue::Int(3),
                        ],
                    }),
                },
            }],
        );
        let jit_layout = tla_jit_abi::StateLayout::new(vec![tla_jit_abi::VarLayout::Compound(
            tla_jit_abi::CompoundLayout::Sequence {
                element_layout: Box::new(tla_jit_abi::CompoundLayout::SetBitmask {
                    universe: vec![
                        tla_jit_abi::SetBitmaskElement::Int(1),
                        tla_jit_abi::SetBitmaskElement::Int(2),
                        tla_jit_abi::SetBitmaskElement::Int(4),
                    ],
                }),
                element_count: Some(2),
            },
        )]);

        assert_eq!(first_layout_slot_mismatch(&check_layout, &jit_layout), None);
        assert!(!layouts_compatible(&check_layout, &jit_layout));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_recursive_sequence_of_set_bitmask_uses_compact_set_slots() {
        use super::super::state_layout::{FlatScalarValue, FlatValueLayout, SequenceBoundEvidence};

        let registry = VarRegistry::from_names(["history"]);
        let proc_domain = vec![
            FlatScalarValue::Int(1),
            FlatScalarValue::Int(2),
            FlatScalarValue::Int(3),
        ];
        let check_layout = StateLayout::new(
            &registry,
            vec![VarLayoutKind::Recursive {
                layout: FlatValueLayout::Sequence {
                    bound: SequenceBoundEvidence::ProvenInvariant {
                        invariant: Arc::from("BoundedHistory"),
                    },
                    max_len: 2,
                    element_layout: Box::new(FlatValueLayout::SetBitmask {
                        universe: proc_domain,
                    }),
                },
            }],
        );

        let jit_layout = check_layout_to_jit_layout(&check_layout);

        assert_eq!(check_layout.total_slots(), 3);
        assert_eq!(jit_layout_compact_slot_count(&jit_layout), 3);
        assert_eq!(first_layout_slot_mismatch(&check_layout, &jit_layout), None);
        assert!(layouts_compatible(&check_layout, &jit_layout));
        match jit_layout.var_layout(0).unwrap() {
            tla_jit_abi::VarLayout::Compound(tla_jit_abi::CompoundLayout::Sequence {
                element_layout,
                element_count,
            }) => {
                assert_eq!(*element_count, Some(2));
                assert_eq!(element_layout.compact_slot_count(), 1);
                match element_layout.as_ref() {
                    tla_jit_abi::CompoundLayout::SetBitmask { universe } => {
                        assert_eq!(
                            universe.as_slice(),
                            &[
                                tla_jit_abi::SetBitmaskElement::Int(1),
                                tla_jit_abi::SetBitmaskElement::Int(2),
                                tla_jit_abi::SetBitmaskElement::Int(3),
                            ]
                        );
                    }
                    other => panic!("expected compact set-bitmask sequence element, got {other:?}"),
                }
            }
            other => panic!("expected recursive sequence layout, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_roundtrip_check_to_jit_to_check() {
        let registry = VarRegistry::from_names(["pc", "counter", "flag"]);
        let func = IntIntervalFunc::new(
            1,
            3,
            vec![
                Value::SmallInt(10),
                Value::SmallInt(20),
                Value::SmallInt(30),
            ],
        );
        let state = ArrayState::from_values(vec![
            Value::SmallInt(0),
            Value::IntFunc(Arc::new(func)),
            Value::Bool(true),
        ]);
        let check_layout = infer_layout(&state, &registry);
        let jit_layout = check_layout_to_jit_layout(&check_layout);
        let roundtrip_layout = jit_layout_to_check_layout(&jit_layout, &registry);

        // Verify structural equivalence
        assert_eq!(check_layout.var_count(), roundtrip_layout.var_count());
        assert_eq!(check_layout.total_slots(), roundtrip_layout.total_slots());
        assert_eq!(
            check_layout.is_all_scalar(),
            roundtrip_layout.is_all_scalar()
        );
        assert_eq!(
            check_layout.is_fully_flat(),
            roundtrip_layout.is_fully_flat()
        );

        // Verify per-variable slot counts match
        for i in 0..check_layout.var_count() {
            let orig = check_layout.var_layout(i).unwrap();
            let rt = roundtrip_layout.var_layout(i).unwrap();
            assert_eq!(
                orig.slot_count, rt.slot_count,
                "var {i} slot_count mismatch: orig={}, roundtrip={}",
                orig.slot_count, rt.slot_count
            );
            assert_eq!(
                orig.offset, rt.offset,
                "var {i} offset mismatch: orig={}, roundtrip={}",
                orig.offset, rt.offset
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_layouts_compatible_all_scalar() {
        let registry = VarRegistry::from_names(["x", "y"]);
        let state = ArrayState::from_values(vec![Value::SmallInt(1), Value::Bool(false)]);
        let check_layout = infer_layout(&state, &registry);
        let jit_layout = check_layout_to_jit_layout(&check_layout);

        assert!(layouts_compatible(&check_layout, &jit_layout));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_layouts_compatible_int_array() {
        let registry = VarRegistry::from_names(["pc", "arr"]);
        let func = IntIntervalFunc::new(
            0,
            2,
            vec![Value::SmallInt(0), Value::SmallInt(0), Value::SmallInt(0)],
        );
        let state =
            ArrayState::from_values(vec![Value::SmallInt(0), Value::IntFunc(Arc::new(func))]);
        let check_layout = infer_layout(&state, &registry);
        let jit_layout = check_layout_to_jit_layout(&check_layout);

        assert!(layouts_compatible(&check_layout, &jit_layout));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_layouts_compatible_dynamic_var() {
        let registry = VarRegistry::from_names(["count", "data"]);
        let set = tla_value::value::SortedSet::from_sorted_vec(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
        ]);
        let state = ArrayState::from_values(vec![Value::SmallInt(99), Value::Set(Arc::new(set))]);
        let check_layout = infer_layout(&state, &registry);
        let jit_layout = check_layout_to_jit_layout(&check_layout);

        assert!(layouts_compatible(&check_layout, &jit_layout));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_layouts_incompatible_var_count_mismatch() {
        let registry2 = VarRegistry::from_names(["x", "y"]);
        let state2 = ArrayState::from_values(vec![Value::SmallInt(1), Value::SmallInt(2)]);
        let check_layout = infer_layout(&state2, &registry2);

        // Create a JIT layout with 3 vars
        let jit_layout = tla_jit_abi::StateLayout::new(vec![
            tla_jit_abi::VarLayout::ScalarInt,
            tla_jit_abi::VarLayout::ScalarInt,
            tla_jit_abi::VarLayout::ScalarInt,
        ]);

        assert!(!layouts_compatible(&check_layout, &jit_layout));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_ewd998_layout_bridge() {
        // EWD998 N=3: 7 variables including IntFunc arrays
        let registry = VarRegistry::from_names([
            "active",
            "color",
            "counter",
            "pending",
            "token_pos",
            "token_q",
            "token_color",
        ]);
        let active = IntIntervalFunc::new(
            0,
            2,
            vec![Value::Bool(true), Value::Bool(false), Value::Bool(false)],
        );
        let color = IntIntervalFunc::new(
            0,
            2,
            vec![
                Value::String(Arc::from("white")),
                Value::String(Arc::from("white")),
                Value::String(Arc::from("white")),
            ],
        );
        let counter = IntIntervalFunc::new(
            0,
            2,
            vec![Value::SmallInt(0), Value::SmallInt(0), Value::SmallInt(0)],
        );
        let pending = IntIntervalFunc::new(
            0,
            2,
            vec![Value::SmallInt(0), Value::SmallInt(0), Value::SmallInt(0)],
        );

        let state = ArrayState::from_values(vec![
            Value::IntFunc(Arc::new(active)),
            Value::IntFunc(Arc::new(color)),
            Value::IntFunc(Arc::new(counter)),
            Value::IntFunc(Arc::new(pending)),
            Value::SmallInt(0),
            Value::SmallInt(0),
            Value::String(Arc::from("black")),
        ]);

        let check_layout = infer_layout(&state, &registry);
        assert_eq!(check_layout.total_slots(), 15);
        assert!(check_layout.is_fully_flat());

        let jit_layout = check_layout_to_jit_layout(&check_layout);
        assert_eq!(jit_layout.var_count(), 7);
        match jit_layout.var_layout(1).unwrap() {
            tla_jit_abi::VarLayout::Compound(tla_jit_abi::CompoundLayout::Function {
                value_layout,
                domain_lo,
                pair_count,
                ..
            }) => {
                assert_eq!(*domain_lo, Some(0));
                assert_eq!(*pair_count, Some(3));
                assert!(matches!(
                    value_layout.as_ref(),
                    tla_jit_abi::CompoundLayout::String
                ));
            }
            other => panic!("expected string-valued color function layout, got {other:?}"),
        }
        assert!(matches!(
            jit_layout.var_layout(6).unwrap(),
            tla_jit_abi::VarLayout::Compound(tla_jit_abi::CompoundLayout::String)
        ));

        // Verify compatibility
        assert!(layouts_compatible(&check_layout, &jit_layout));

        // Roundtrip
        let roundtrip = jit_layout_to_check_layout(&jit_layout, &registry);
        assert_eq!(roundtrip.total_slots(), 15);
        assert!(roundtrip.is_fully_flat());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_recursive_layout_bridge_uses_compound_layout() {
        use super::super::state_layout::{FlatValueLayout, SlotType};

        let registry = VarRegistry::from_names(["network"]);
        let message_layout = FlatValueLayout::Record {
            field_names: vec![Arc::from("clock"), Arc::from("type")],
            field_layouts: vec![
                FlatValueLayout::Scalar(SlotType::Int),
                FlatValueLayout::Scalar(SlotType::String),
            ],
        };
        let check_layout = StateLayout::new(
            &registry,
            vec![VarLayoutKind::Recursive {
                layout: FlatValueLayout::IntFunction {
                    lo: 1,
                    len: 2,
                    value_layout: Box::new(FlatValueLayout::IntFunction {
                        lo: 1,
                        len: 2,
                        value_layout: Box::new(FlatValueLayout::Sequence {
                            bound:
                                super::super::state_layout::SequenceBoundEvidence::ProvenInvariant {
                                    invariant: Arc::from("BoundedNetwork"),
                                },
                            max_len: 3,
                            element_layout: Box::new(message_layout),
                        }),
                    }),
                },
            }],
        );

        let jit_layout = check_layout_to_jit_layout(&check_layout);

        assert_eq!(check_layout.total_slots(), 28);
        assert_eq!(jit_layout_compact_slot_count(&jit_layout), 28);
        assert_eq!(first_layout_slot_mismatch(&check_layout, &jit_layout), None);
        assert!(layouts_compatible(&check_layout, &jit_layout));
        match jit_layout.var_layout(0).unwrap() {
            tla_jit_abi::VarLayout::Compound(tla_jit_abi::CompoundLayout::Function {
                pair_count,
                value_layout,
                domain_lo,
                ..
            }) => {
                assert_eq!(*pair_count, Some(2));
                assert_eq!(*domain_lo, Some(1));
                assert!(matches!(
                    value_layout.as_ref(),
                    tla_jit_abi::CompoundLayout::Function {
                        pair_count: Some(2),
                        ..
                    }
                ));
            }
            other => panic!("expected recursive Compound(Function), got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_dense_ordered_generic_function_bridges_with_domain_lo() {
        use super::super::state_layout::{FlatScalarValue, FlatValueLayout, SlotType};

        let registry = VarRegistry::from_names(["clock"]);
        let check_layout = StateLayout::new(
            &registry,
            vec![VarLayoutKind::Recursive {
                layout: FlatValueLayout::Function {
                    domain: vec![
                        FlatScalarValue::Int(2),
                        FlatScalarValue::Int(3),
                        FlatScalarValue::Int(4),
                    ],
                    value_layout: Box::new(FlatValueLayout::Scalar(SlotType::Int)),
                },
            }],
        );

        let jit_layout = check_layout_to_jit_layout(&check_layout);

        assert_eq!(first_layout_slot_mismatch(&check_layout, &jit_layout), None);
        assert!(layouts_compatible(&check_layout, &jit_layout));
        match jit_layout.var_layout(0).unwrap() {
            tla_jit_abi::VarLayout::Compound(tla_jit_abi::CompoundLayout::Function {
                key_layout,
                pair_count,
                domain_lo,
                value_layout,
            }) => {
                assert!(matches!(
                    key_layout.as_ref(),
                    tla_jit_abi::CompoundLayout::Int
                ));
                assert_eq!(*pair_count, Some(3));
                assert_eq!(*domain_lo, Some(2));
                assert!(matches!(
                    value_layout.as_ref(),
                    tla_jit_abi::CompoundLayout::Int
                ));
            }
            other => panic!("expected dense generic function bridge, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_dense_generic_function_incompatible_with_domain_lo_none() {
        use super::super::state_layout::{FlatScalarValue, FlatValueLayout, SlotType};

        let registry = VarRegistry::from_names(["clock"]);
        let check_layout = StateLayout::new(
            &registry,
            vec![VarLayoutKind::Recursive {
                layout: FlatValueLayout::Function {
                    domain: vec![
                        FlatScalarValue::Int(2),
                        FlatScalarValue::Int(3),
                        FlatScalarValue::Int(4),
                    ],
                    value_layout: Box::new(FlatValueLayout::Scalar(SlotType::Int)),
                },
            }],
        );
        let jit_layout = tla_jit_abi::StateLayout::new(vec![tla_jit_abi::VarLayout::Compound(
            tla_jit_abi::CompoundLayout::Function {
                key_layout: Box::new(tla_jit_abi::CompoundLayout::Int),
                value_layout: Box::new(tla_jit_abi::CompoundLayout::Int),
                pair_count: Some(3),
                domain_lo: None,
            },
        )]);

        assert_eq!(first_layout_slot_mismatch(&check_layout, &jit_layout), None);
        assert!(!layouts_compatible(&check_layout, &jit_layout));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_domain_lo_some_requires_dense_ordered_generic_function_domain() {
        use super::super::state_layout::{FlatScalarValue, FlatValueLayout, SlotType};

        let registry = VarRegistry::from_names(["clock"]);
        for domain in [
            vec![
                FlatScalarValue::Int(2),
                FlatScalarValue::Int(4),
                FlatScalarValue::Int(5),
            ],
            vec![
                FlatScalarValue::Int(2),
                FlatScalarValue::Int(4),
                FlatScalarValue::Int(3),
            ],
        ] {
            let check_layout = StateLayout::new(
                &registry,
                vec![VarLayoutKind::Recursive {
                    layout: FlatValueLayout::Function {
                        domain,
                        value_layout: Box::new(FlatValueLayout::Scalar(SlotType::Int)),
                    },
                }],
            );
            let jit_layout = tla_jit_abi::StateLayout::new(vec![tla_jit_abi::VarLayout::Compound(
                tla_jit_abi::CompoundLayout::Function {
                    key_layout: Box::new(tla_jit_abi::CompoundLayout::Int),
                    value_layout: Box::new(tla_jit_abi::CompoundLayout::Int),
                    pair_count: Some(3),
                    domain_lo: Some(2),
                },
            )]);

            assert_eq!(first_layout_slot_mismatch(&check_layout, &jit_layout), None);
            assert!(
                !layouts_compatible(&check_layout, &jit_layout),
                "domain_lo Some must reject non-dense or wrong-order generic function domains"
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_layouts_compatible_recursive_record_exact_field_order() {
        use super::super::state_layout::{FlatValueLayout, SlotType};

        let registry = VarRegistry::from_names(["token"]);
        let check_layout = StateLayout::new(
            &registry,
            vec![VarLayoutKind::Recursive {
                layout: FlatValueLayout::Record {
                    field_names: vec![Arc::from("pos"), Arc::from("color"), Arc::from("q")],
                    field_layouts: vec![
                        FlatValueLayout::Scalar(SlotType::Int),
                        FlatValueLayout::Scalar(SlotType::String),
                        FlatValueLayout::Scalar(SlotType::Int),
                    ],
                },
            }],
        );
        let jit_layout = tla_jit_abi::StateLayout::new(vec![tla_jit_abi::VarLayout::Compound(
            tla_jit_abi::CompoundLayout::Record {
                fields: vec![
                    (
                        tla_core::intern_name("pos"),
                        tla_jit_abi::CompoundLayout::Int,
                    ),
                    (
                        tla_core::intern_name("color"),
                        tla_jit_abi::CompoundLayout::String,
                    ),
                    (tla_core::intern_name("q"), tla_jit_abi::CompoundLayout::Int),
                ],
            },
        )]);

        assert_eq!(first_layout_slot_mismatch(&check_layout, &jit_layout), None);
        assert!(layouts_compatible(&check_layout, &jit_layout));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_layouts_incompatible_recursive_record_same_width_field_order_mismatch() {
        use super::super::state_layout::{FlatValueLayout, SlotType};

        let registry = VarRegistry::from_names(["token"]);
        let check_layout = StateLayout::new(
            &registry,
            vec![VarLayoutKind::Recursive {
                layout: FlatValueLayout::Record {
                    field_names: vec![Arc::from("pos"), Arc::from("color"), Arc::from("q")],
                    field_layouts: vec![
                        FlatValueLayout::Scalar(SlotType::Int),
                        FlatValueLayout::Scalar(SlotType::String),
                        FlatValueLayout::Scalar(SlotType::Int),
                    ],
                },
            }],
        );
        let jit_layout = tla_jit_abi::StateLayout::new(vec![tla_jit_abi::VarLayout::Compound(
            tla_jit_abi::CompoundLayout::Record {
                fields: vec![
                    (
                        tla_core::intern_name("color"),
                        tla_jit_abi::CompoundLayout::String,
                    ),
                    (
                        tla_core::intern_name("pos"),
                        tla_jit_abi::CompoundLayout::Int,
                    ),
                    (tla_core::intern_name("q"), tla_jit_abi::CompoundLayout::Int),
                ],
            },
        )]);

        assert_eq!(first_layout_slot_mismatch(&check_layout, &jit_layout), None);
        assert!(!layouts_compatible(&check_layout, &jit_layout));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compact_slot_count_scalars() {
        assert_eq!(tla_jit_abi::CompoundLayout::Int.compact_slot_count(), 1);
        assert_eq!(tla_jit_abi::CompoundLayout::Bool.compact_slot_count(), 1);
        assert_eq!(tla_jit_abi::CompoundLayout::String.compact_slot_count(), 1);
        assert_eq!(tla_jit_abi::CompoundLayout::Dynamic.compact_slot_count(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compact_slot_count_int_array() {
        let func_layout = tla_jit_abi::CompoundLayout::Function {
            key_layout: Box::new(tla_jit_abi::CompoundLayout::Int),
            value_layout: Box::new(tla_jit_abi::CompoundLayout::Int),
            pair_count: Some(5),
            domain_lo: Some(0),
        };
        assert_eq!(func_layout.compact_slot_count(), 5);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compact_slot_count_record() {
        let nid_a = tla_core::intern_name("a");
        let nid_b = tla_core::intern_name("b");
        let rec_layout = tla_jit_abi::CompoundLayout::Record {
            fields: vec![
                (nid_a, tla_jit_abi::CompoundLayout::Int),
                (nid_b, tla_jit_abi::CompoundLayout::Bool),
            ],
        };
        assert_eq!(rec_layout.compact_slot_count(), 2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_record_plus_scalar_compact_offsets_do_not_use_jit_serialized_offsets() {
        use super::super::state_layout::SlotType;

        let registry = VarRegistry::from_names(["rec", "tail"]);
        let check_layout = StateLayout::new(
            &registry,
            vec![
                VarLayoutKind::Record {
                    field_names: vec![Arc::from("a"), Arc::from("b")],
                    field_is_bool: vec![false, false],
                    field_types: vec![SlotType::Int, SlotType::Int],
                },
                VarLayoutKind::Scalar,
            ],
        );
        let jit_layout = check_layout_to_jit_layout(&check_layout);

        assert_eq!(check_layout.total_slots(), 3);
        assert_eq!(check_layout.var_layout(0).unwrap().offset, 0);
        assert_eq!(check_layout.var_layout(1).unwrap().offset, 2);
        assert_eq!(jit_layout_compact_slot_count(&jit_layout), 3);
        assert_eq!(first_layout_slot_mismatch(&check_layout, &jit_layout), None);
        assert!(layouts_compatible(&check_layout, &jit_layout));

        let serialized_offsets = jit_layout.compute_var_offsets();
        assert_eq!(serialized_offsets, vec![Some(0), Some(8)]);
        assert_ne!(
            serialized_offsets[1],
            Some(check_layout.var_layout(1).unwrap().offset),
            "active compact paths must use check-layout offsets/compact slot counts, not tla-jit-abi::StateLayout::compute_var_offsets"
        );
    }
}
