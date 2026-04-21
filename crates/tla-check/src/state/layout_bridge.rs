// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
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
//! | Offset tracking    | Built-in (contiguous pack)  | Computed via `compute_var_offsets()` |
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

use super::state_layout::{StateLayout, VarLayoutKind};

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
/// | `IntArray { lo, len, bool }` | `Compound(Function { Int->Int/Bool, n })`     |
/// | `Record { fields, bools }`   | `Compound(Record { fields })`                 |
/// | `Bitmask { size }`           | `ScalarInt` (bitmask is a single i64)         |
/// | `Dynamic`                    | `Compound(Dynamic)`                           |
///
/// Note: The returned jit layout describes the **compact** buffer format
/// (offsets match tla-check's slot packing), not the self-describing
/// tagged format used by `serialize_value()`.
#[cfg(feature = "jit")]
#[must_use]
pub(crate) fn check_layout_to_jit_layout(
    check_layout: &StateLayout,
) -> tla_jit::StateLayout {
    let jit_vars: Vec<tla_jit::VarLayout> = check_layout
        .iter()
        .map(|var| check_var_to_jit_var(&var.kind))
        .collect();
    tla_jit::StateLayout::new(jit_vars)
}

/// Convert a single tla-check `VarLayoutKind` to a tla-jit `VarLayout`.
#[cfg(feature = "jit")]
fn check_var_to_jit_var(kind: &VarLayoutKind) -> tla_jit::VarLayout {
    match kind {
        VarLayoutKind::Scalar => tla_jit::VarLayout::ScalarInt,
        VarLayoutKind::ScalarBool => tla_jit::VarLayout::ScalarBool,
        VarLayoutKind::IntArray {
            lo,
            len,
            elements_are_bool,
        } => {
            let value_layout = if *elements_are_bool {
                tla_jit::CompoundLayout::Bool
            } else {
                tla_jit::CompoundLayout::Int
            };
            tla_jit::VarLayout::Compound(tla_jit::CompoundLayout::Function {
                key_layout: Box::new(tla_jit::CompoundLayout::Int),
                value_layout: Box::new(value_layout),
                pair_count: Some(*len),
                domain_lo: Some(*lo),
            })
        }
        VarLayoutKind::Record {
            field_names,
            field_is_bool,
        } => {
            let fields: Vec<(tla_core::NameId, tla_jit::CompoundLayout)> = field_names
                .iter()
                .zip(field_is_bool.iter())
                .map(|(name, is_bool)| {
                    let nid = tla_core::intern_name(name);
                    let layout = if *is_bool {
                        tla_jit::CompoundLayout::Bool
                    } else {
                        tla_jit::CompoundLayout::Int
                    };
                    (nid, layout)
                })
                .collect();
            tla_jit::VarLayout::Compound(tla_jit::CompoundLayout::Record { fields })
        }
        VarLayoutKind::Bitmask { .. } => {
            // Bitmask is a single i64 slot — treat as scalar for JIT purposes.
            tla_jit::VarLayout::ScalarInt
        }
        VarLayoutKind::Dynamic => {
            tla_jit::VarLayout::Compound(tla_jit::CompoundLayout::Dynamic)
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
#[cfg(feature = "jit")]
#[must_use]
pub(crate) fn jit_layout_to_check_layout(
    jit_layout: &tla_jit::StateLayout,
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
#[cfg(feature = "jit")]
fn jit_var_to_check_var(jit_var: &tla_jit::VarLayout) -> VarLayoutKind {
    match jit_var {
        tla_jit::VarLayout::ScalarInt => VarLayoutKind::Scalar,
        tla_jit::VarLayout::ScalarBool => VarLayoutKind::ScalarBool,
        tla_jit::VarLayout::Compound(compound) => compound_to_check_var(compound),
        // non_exhaustive: future VarLayout variants fall back to Dynamic.
        _ => VarLayoutKind::Dynamic,
    }
}

/// Convert a tla-jit `CompoundLayout` to a tla-check `VarLayoutKind`.
#[cfg(feature = "jit")]
fn compound_to_check_var(compound: &tla_jit::CompoundLayout) -> VarLayoutKind {
    match compound {
        // Integer-array function: [lo..hi -> Int/Bool]
        tla_jit::CompoundLayout::Function {
            key_layout,
            value_layout,
            pair_count: Some(len),
            domain_lo: Some(lo),
        } if key_layout.is_scalar() && value_layout.is_scalar() => {
            let elements_are_bool = matches!(**value_layout, tla_jit::CompoundLayout::Bool);
            VarLayoutKind::IntArray {
                lo: *lo,
                len: *len,
                elements_are_bool,
            }
        }

        // Record with all-scalar fields
        tla_jit::CompoundLayout::Record { fields } => {
            let all_scalar = fields.iter().all(|(_, layout)| layout.is_scalar());
            if all_scalar && !fields.is_empty() {
                let field_names: Vec<std::sync::Arc<str>> = fields
                    .iter()
                    .map(|(nid, _)| tla_core::resolve_name_id(*nid))
                    .collect();
                let field_is_bool: Vec<bool> = fields
                    .iter()
                    .map(|(_, layout)| matches!(layout, tla_jit::CompoundLayout::Bool))
                    .collect();
                VarLayoutKind::Record {
                    field_names,
                    field_is_bool,
                }
            } else {
                VarLayoutKind::Dynamic
            }
        }

        // Explicit dynamic
        tla_jit::CompoundLayout::Dynamic => VarLayoutKind::Dynamic,

        // All other compound types: fallback to Dynamic
        _ => VarLayoutKind::Dynamic,
    }
}

/// Verify that two layouts are structurally compatible for buffer sharing.
///
/// Two layouts are compatible when they produce the same total slot count
/// and each variable maps to the same number of slots. This means a flat
/// buffer created with one layout can be read by code using the other.
///
/// Does NOT require the layouts to be identical — only that slot counts match.
/// For example, tla-check's `IntArray{lo=0, len=3}` is compatible with
/// tla-jit's `Compound(Function{Int->Int, n=3, lo=0})` because both
/// produce 3 contiguous i64 slots.
#[cfg(feature = "jit")]
#[must_use]
pub(crate) fn layouts_compatible(
    check_layout: &StateLayout,
    jit_layout: &tla_jit::StateLayout,
) -> bool {
    if check_layout.var_count() != jit_layout.var_count() {
        return false;
    }

    for i in 0..check_layout.var_count() {
        let check_var = check_layout.var_layout(i).expect("check var_count mismatch");
        let jit_var = jit_layout.var_layout(i).expect("jit var_count mismatch");

        let check_slots = check_var.kind.slot_count();
        let jit_slots = match jit_var {
            tla_jit::VarLayout::ScalarInt | tla_jit::VarLayout::ScalarBool => 1,
            tla_jit::VarLayout::Compound(compound) => {
                // For compact buffer compatibility, we need the compact slot count,
                // NOT the tagged serialized size. The compact slot count for a
                // function with n pairs and scalar keys/values is n (just values),
                // not 2 + n * (key_slots + value_slots).
                compact_slot_count(compound)
            }
            // non_exhaustive: future VarLayout variants get 1 placeholder slot.
            _ => 1,
        };

        if check_slots != jit_slots {
            return false;
        }
    }

    true
}

/// Compute the number of compact (no-tag) i64 slots a compound layout occupies.
///
/// This is different from `CompoundLayout::fixed_serialized_slots()` which
/// counts the self-describing tagged format. The compact format used by
/// tla-check's flat buffer has no tags.
#[cfg(feature = "jit")]
fn compact_slot_count(compound: &tla_jit::CompoundLayout) -> usize {
    match compound {
        tla_jit::CompoundLayout::Int
        | tla_jit::CompoundLayout::Bool
        | tla_jit::CompoundLayout::String => 1,

        // IntArray-like function: n contiguous value slots
        tla_jit::CompoundLayout::Function {
            pair_count: Some(n),
            domain_lo: Some(_),
            value_layout,
            key_layout,
        } if key_layout.is_scalar() && value_layout.is_scalar() => *n,

        // Record with all-scalar fields: one slot per field
        tla_jit::CompoundLayout::Record { fields }
            if fields.iter().all(|(_, l)| l.is_scalar()) =>
        {
            fields.len()
        }

        // Dynamic: 1 placeholder slot
        tla_jit::CompoundLayout::Dynamic => 1,

        // Everything else: 1 placeholder slot (Dynamic equivalent)
        _ => 1,
    }
}

#[cfg(all(test, feature = "jit"))]
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
            Some(&tla_jit::VarLayout::ScalarInt)
        );
        assert_eq!(
            jit_layout.var_layout(1),
            Some(&tla_jit::VarLayout::ScalarBool)
        );
        assert_eq!(
            jit_layout.var_layout(2),
            Some(&tla_jit::VarLayout::ScalarInt)
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
            tla_jit::VarLayout::Compound(tla_jit::CompoundLayout::Function {
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
    fn test_roundtrip_check_to_jit_to_check() {
        let registry = VarRegistry::from_names(["pc", "counter", "flag"]);
        let func = IntIntervalFunc::new(
            1,
            3,
            vec![Value::SmallInt(10), Value::SmallInt(20), Value::SmallInt(30)],
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
        assert_eq!(check_layout.is_all_scalar(), roundtrip_layout.is_all_scalar());
        assert_eq!(check_layout.is_fully_flat(), roundtrip_layout.is_fully_flat());

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
        let state = ArrayState::from_values(vec![
            Value::SmallInt(0),
            Value::IntFunc(Arc::new(func)),
        ]);
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
        let state = ArrayState::from_values(vec![
            Value::SmallInt(99),
            Value::Set(Arc::new(set)),
        ]);
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
        let jit_layout = tla_jit::StateLayout::new(vec![
            tla_jit::VarLayout::ScalarInt,
            tla_jit::VarLayout::ScalarInt,
            tla_jit::VarLayout::ScalarInt,
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
            vec![Value::SmallInt(0), Value::SmallInt(0), Value::SmallInt(0)],
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
            Value::SmallInt(0),
        ]);

        let check_layout = infer_layout(&state, &registry);
        assert_eq!(check_layout.total_slots(), 15);
        assert!(check_layout.is_fully_flat());

        let jit_layout = check_layout_to_jit_layout(&check_layout);
        assert_eq!(jit_layout.var_count(), 7);

        // Verify compatibility
        assert!(layouts_compatible(&check_layout, &jit_layout));

        // Roundtrip
        let roundtrip = jit_layout_to_check_layout(&jit_layout, &registry);
        assert_eq!(roundtrip.total_slots(), 15);
        assert!(roundtrip.is_fully_flat());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compact_slot_count_scalars() {
        assert_eq!(compact_slot_count(&tla_jit::CompoundLayout::Int), 1);
        assert_eq!(compact_slot_count(&tla_jit::CompoundLayout::Bool), 1);
        assert_eq!(compact_slot_count(&tla_jit::CompoundLayout::String), 1);
        assert_eq!(compact_slot_count(&tla_jit::CompoundLayout::Dynamic), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compact_slot_count_int_array() {
        let func_layout = tla_jit::CompoundLayout::Function {
            key_layout: Box::new(tla_jit::CompoundLayout::Int),
            value_layout: Box::new(tla_jit::CompoundLayout::Int),
            pair_count: Some(5),
            domain_lo: Some(0),
        };
        assert_eq!(compact_slot_count(&func_layout), 5);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compact_slot_count_record() {
        let nid_a = tla_core::intern_name("a");
        let nid_b = tla_core::intern_name("b");
        let rec_layout = tla_jit::CompoundLayout::Record {
            fields: vec![
                (nid_a, tla_jit::CompoundLayout::Int),
                (nid_b, tla_jit::CompoundLayout::Bool),
            ],
        };
        assert_eq!(compact_slot_count(&rec_layout), 2);
    }
}
