// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Layout inference from initial state values.
//!
//! Given an `ArrayState` (typically the first initial state), infers a
//! `StateLayout` that maps each variable to its optimal flat representation.
//!
//! # Inference rules
//!
//! | Value type                     | VarLayoutKind            |
//! |-------------------------------|--------------------------|
//! | Bool                          | ScalarBool               |
//! | SmallInt / Int                | Scalar                   |
//! | IntFunc (int interval domain) | IntArray { lo, len }     |
//! | Record (all scalar fields)    | Record { field_names }   |
//! | Set                           | Dynamic (Bitmask deferred)|
//! | Everything else               | Dynamic                  |
//!
//! Part of #3986.

use super::array_state::ArrayState;
use std::sync::Arc;

use super::state_layout::{SlotType, StateLayout, VarLayoutKind};
use crate::var_index::VarRegistry;
use crate::Value;

/// Infer a `StateLayout` from an initial state.
///
/// Examines each variable's value to determine the best flat representation.
/// The inferred layout is valid for all states in a model-checking run IF the
/// variable types are uniform (which is guaranteed by TLA+ typing: a variable
/// that starts as a function stays a function through all transitions).
///
/// # Arguments
///
/// * `initial_state` - The first initial state to analyze.
/// * `registry` - Variable name registry.
#[must_use]
pub(crate) fn infer_layout(initial_state: &ArrayState, registry: &VarRegistry) -> StateLayout {
    let compact_values = initial_state.values();
    let mut kinds = Vec::with_capacity(compact_values.len());

    for cv in compact_values.iter() {
        let kind = infer_var_kind(cv);
        kinds.push(kind);
    }

    StateLayout::new(registry, kinds)
}

/// Infer a `StateLayout` from a wavefront of states (~first 1000 states).
///
/// Examines multiple states and merges their inferred layouts conservatively:
/// for each variable, if all sampled states agree on the layout kind, that kind
/// is used; if any state disagrees, the variable falls back to `Dynamic`.
///
/// This is more robust than single-state inference because it handles edge
/// cases where the first initial state might have an unusual shape (e.g.,
/// an empty function that later becomes non-empty, or a record with
/// different field sets across initial states).
///
/// # Arguments
///
/// * `states` - Slice of initial/wavefront states to analyze. Must be non-empty.
/// * `registry` - Variable name registry.
///
/// # Panics
///
/// Panics if `states` is empty.
///
/// Part of #3986: Layout inference from first wavefront (~1000 states).
#[must_use]
pub(crate) fn infer_layout_from_wavefront(
    states: &[ArrayState],
    registry: &VarRegistry,
) -> StateLayout {
    assert!(
        !states.is_empty(),
        "infer_layout_from_wavefront requires at least one state"
    );

    // Start with the first state's layout.
    let first_values = states[0].values();
    let num_vars = first_values.len();
    let mut kinds: Vec<VarLayoutKind> = first_values
        .iter()
        .map(|cv| infer_var_kind(cv))
        .collect();

    // Merge with subsequent states: if any disagree, downgrade to Dynamic.
    for state in &states[1..] {
        let values = state.values();
        debug_assert_eq!(
            values.len(),
            num_vars,
            "infer_layout_from_wavefront: all states must have the same number of variables"
        );

        for (var_idx, cv) in values.iter().enumerate() {
            // Skip variables already downgraded to Dynamic.
            if matches!(kinds[var_idx], VarLayoutKind::Dynamic) {
                continue;
            }

            let new_kind = infer_var_kind(cv);
            if !layout_kinds_compatible(&kinds[var_idx], &new_kind) {
                // Incompatible shapes: fall back to Dynamic.
                kinds[var_idx] = VarLayoutKind::Dynamic;
            }
        }
    }

    StateLayout::new(registry, kinds)
}

/// Check if two `VarLayoutKind`s are compatible (same structure).
///
/// Two kinds are compatible if they describe the same representation:
/// same variant, same dimensions, same field names. This is stricter
/// than just matching the variant — `IntArray{lo=0, len=3}` is NOT
/// compatible with `IntArray{lo=0, len=4}`.
fn layout_kinds_compatible(a: &VarLayoutKind, b: &VarLayoutKind) -> bool {
    match (a, b) {
        (VarLayoutKind::Scalar, VarLayoutKind::Scalar) => true,
        (VarLayoutKind::ScalarBool, VarLayoutKind::ScalarBool) => true,
        (VarLayoutKind::ScalarString, VarLayoutKind::ScalarString) => true,
        (VarLayoutKind::ScalarModelValue, VarLayoutKind::ScalarModelValue) => true,
        (
            VarLayoutKind::IntArray {
                lo: lo_a,
                len: len_a,
                elements_are_bool: eb_a,
                ..
            },
            VarLayoutKind::IntArray {
                lo: lo_b,
                len: len_b,
                elements_are_bool: eb_b,
                ..
            },
        ) => lo_a == lo_b && len_a == len_b && eb_a == eb_b,
        (
            VarLayoutKind::Record {
                field_names: fn_a,
                field_is_bool: fb_a,
                ..
            },
            VarLayoutKind::Record {
                field_names: fn_b,
                field_is_bool: fb_b,
                ..
            },
        ) => fn_a == fn_b && fb_a == fb_b,
        (
            VarLayoutKind::StringKeyedArray {
                domain_keys: dk_a,
                domain_types: dt_a,
                ..
            },
            VarLayoutKind::StringKeyedArray {
                domain_keys: dk_b,
                domain_types: dt_b,
                ..
            },
        ) => dk_a == dk_b && dt_a == dt_b,
        (
            VarLayoutKind::Bitmask {
                universe_size: ua,
            },
            VarLayoutKind::Bitmask {
                universe_size: ub,
            },
        ) => ua == ub,
        (VarLayoutKind::Dynamic, VarLayoutKind::Dynamic) => true,
        _ => false,
    }
}

/// Infer the layout kind for a single variable from its CompactValue.
fn infer_var_kind(cv: &tla_value::CompactValue) -> VarLayoutKind {
    if cv.is_bool() {
        return VarLayoutKind::ScalarBool;
    }
    if cv.is_int() {
        return VarLayoutKind::Scalar;
    }

    // For heap values, convert to Value and inspect the structure.
    if cv.is_heap() {
        let value = Value::from(cv);
        return infer_kind_from_value(&value);
    }

    // String: use ScalarString to preserve type through roundtrip.
    // Part of #3908.
    if cv.is_string() {
        return VarLayoutKind::ScalarString;
    }

    // ModelValue: use ScalarModelValue to preserve type through roundtrip.
    // Part of #3908.
    if cv.is_model_value() {
        return VarLayoutKind::ScalarModelValue;
    }

    VarLayoutKind::Dynamic
}

/// Infer layout kind from a full Value.
fn infer_kind_from_value(value: &Value) -> VarLayoutKind {
    match value {
        Value::Bool(_) => VarLayoutKind::ScalarBool,
        Value::SmallInt(_) | Value::Int(_) => VarLayoutKind::Scalar,
        Value::String(_) => VarLayoutKind::ScalarString,
        Value::ModelValue(_) => VarLayoutKind::ScalarModelValue,

        // Integer-indexed function: flatten to IntArray if all values are scalar.
        Value::IntFunc(func) => {
            let f = func.as_ref();
            let all_scalar = f.values().iter().all(is_scalar_value);
            if all_scalar && f.len() > 0 {
                let elements_are_bool = f.values().iter().all(|v| matches!(v, Value::Bool(_)));
                let has_string = f
                    .values()
                    .iter()
                    .any(|v| matches!(v, Value::String(_) | Value::ModelValue(_)));
                let element_types = if has_string || !elements_are_bool {
                    // Track per-element types when there are mixed types.
                    Some(f.values().iter().map(slot_type_from_value).collect())
                } else {
                    None
                };
                VarLayoutKind::IntArray {
                    lo: f.min(),
                    len: f.len(),
                    elements_are_bool,
                    element_types,
                }
            } else if f.len() == 0 {
                // Empty function: treat as scalar (zero slots would be odd).
                VarLayoutKind::Dynamic
            } else {
                VarLayoutKind::Dynamic
            }
        }

        // General function: flatten to IntArray if domain is integer interval
        // and all range values are scalar, or StringKeyedArray if domain is
        // strings/model-values.
        Value::Func(func) => {
            if func.domain_is_empty() {
                return VarLayoutKind::Dynamic;
            }

            // Check if domain is contiguous integers.
            let mut is_int_domain = true;
            let mut is_string_domain = true;
            let mut min_key = i64::MAX;
            let mut max_key = i64::MIN;
            for key in func.domain_iter() {
                match key {
                    Value::SmallInt(n) => {
                        is_string_domain = false;
                        min_key = min_key.min(*n);
                        max_key = max_key.max(*n);
                    }
                    Value::String(_) | Value::ModelValue(_) => {
                        is_int_domain = false;
                    }
                    _ => {
                        is_int_domain = false;
                        is_string_domain = false;
                        break;
                    }
                }
            }

            if is_int_domain {
                let expected_len = (max_key - min_key + 1) as usize;
                if expected_len == func.domain_len() {
                    // Contiguous integer domain. Check range values.
                    if let Some(int_array) =
                        try_int_array_from_func(func, min_key, expected_len)
                    {
                        return int_array;
                    }
                }
            }

            // String-keyed function: flatten to StringKeyedArray.
            // Part of #3908: compound type flat state roundtrip.
            if is_string_domain {
                let all_range_scalar = func.iter().all(|(_, v)| is_scalar_value(v));
                if all_range_scalar {
                    let mut domain_keys: Vec<Arc<str>> = Vec::with_capacity(func.domain_len());
                    let mut domain_types: Vec<SlotType> = Vec::with_capacity(func.domain_len());
                    let mut value_types: Vec<SlotType> = Vec::with_capacity(func.domain_len());
                    for (key, val) in func.iter() {
                        let (key_str, key_ty) = match key {
                            Value::String(s) => (Arc::clone(s), SlotType::String),
                            Value::ModelValue(s) => (Arc::clone(s), SlotType::ModelValue),
                            _ => unreachable!("checked is_string_domain above"),
                        };
                        domain_keys.push(key_str);
                        domain_types.push(key_ty);
                        value_types.push(slot_type_from_value(val));
                    }
                    return VarLayoutKind::StringKeyedArray {
                        domain_keys,
                        domain_types,
                        value_types,
                    };
                }
            }

            VarLayoutKind::Dynamic
        }

        // Record: flatten if all fields are scalar.
        Value::Record(rec) => {
            let mut all_scalar = true;
            let mut field_names = Vec::with_capacity(rec.len());
            let mut field_is_bool = Vec::with_capacity(rec.len());
            let mut field_types = Vec::with_capacity(rec.len());

            for (nid, val) in rec.iter() {
                field_names.push(tla_core::resolve_name_id(nid));
                field_is_bool.push(matches!(val, Value::Bool(_)));
                field_types.push(slot_type_from_value(val));
                if !is_scalar_value(val) {
                    all_scalar = false;
                    break;
                }
            }

            if all_scalar && !field_names.is_empty() {
                VarLayoutKind::Record {
                    field_names,
                    field_is_bool,
                    field_types,
                }
            } else {
                VarLayoutKind::Dynamic
            }
        }

        // Sets: always Dynamic for now. Bitmask encoding requires universe
        // enumeration context that is not yet implemented. Deferred to Phase 6.
        // See #4007.
        Value::Set(_) => VarLayoutKind::Dynamic,

        // Everything else: Dynamic fallback.
        _ => VarLayoutKind::Dynamic,
    }
}

/// Try to create an IntArray layout from a Func with contiguous integer domain.
fn try_int_array_from_func(
    func: &tla_value::value::FuncValue,
    min_key: i64,
    expected_len: usize,
) -> Option<VarLayoutKind> {
    let mut all_scalar = true;
    let mut all_bool = true;
    let mut has_string = false;
    for (_key, val) in func.iter() {
        if !is_scalar_value(val) {
            all_scalar = false;
            break;
        }
        if !matches!(val, Value::Bool(_)) {
            all_bool = false;
        }
        if matches!(val, Value::String(_) | Value::ModelValue(_)) {
            has_string = true;
        }
    }
    if all_scalar {
        let element_types = if has_string || !all_bool {
            // Collect per-element types for reconstruction.
            let mut types = Vec::with_capacity(expected_len);
            for i in 0..expected_len {
                let key = Value::SmallInt(min_key + i as i64);
                if let Some(val) = func.apply(&key) {
                    types.push(slot_type_from_value(val));
                } else {
                    types.push(SlotType::Int);
                }
            }
            Some(types)
        } else {
            None
        };
        Some(VarLayoutKind::IntArray {
            lo: min_key,
            len: expected_len,
            elements_are_bool: all_bool,
            element_types,
        })
    } else {
        None
    }
}

/// Check if a Value is a scalar that fits in a single i64.
fn is_scalar_value(value: &Value) -> bool {
    matches!(
        value,
        Value::Bool(_)
            | Value::SmallInt(_)
            | Value::Int(_)
            | Value::String(_)
            | Value::ModelValue(_)
    )
}

/// Determine the SlotType for a scalar Value.
/// Part of #3908.
fn slot_type_from_value(value: &Value) -> SlotType {
    match value {
        Value::Bool(_) => SlotType::Bool,
        Value::String(_) => SlotType::String,
        Value::ModelValue(_) => SlotType::ModelValue,
        _ => SlotType::Int,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::var_index::VarRegistry;
    use std::sync::Arc;
    use tla_value::value::{IntIntervalFunc, RecordValue, SortedSet};

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_all_scalar() {
        let registry = VarRegistry::from_names(["x", "y", "z"]);
        let state = ArrayState::from_values(vec![
            Value::SmallInt(1),
            Value::Bool(true),
            Value::SmallInt(-5),
        ]);

        let layout = infer_layout(&state, &registry);
        assert_eq!(layout.var_count(), 3);
        assert_eq!(layout.total_slots(), 3);
        assert!(layout.is_all_scalar());

        // Bool variable gets ScalarBool, not Scalar.
        assert!(matches!(
            layout.var_layout(0).unwrap().kind,
            VarLayoutKind::Scalar
        ));
        assert!(matches!(
            layout.var_layout(1).unwrap().kind,
            VarLayoutKind::ScalarBool
        ));
        assert!(matches!(
            layout.var_layout(2).unwrap().kind,
            VarLayoutKind::Scalar
        ));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_int_func() {
        let registry = VarRegistry::from_names(["active"]);
        // active = [0 |-> FALSE, 1 |-> TRUE, 2 |-> FALSE]
        let func = IntIntervalFunc::new(
            0,
            2,
            vec![Value::Bool(false), Value::Bool(true), Value::Bool(false)],
        );
        let state = ArrayState::from_values(vec![Value::IntFunc(Arc::new(func))]);

        let layout = infer_layout(&state, &registry);
        assert_eq!(layout.var_count(), 1);
        assert_eq!(layout.total_slots(), 3);

        let vl = layout.var_layout(0).unwrap();
        match &vl.kind {
            VarLayoutKind::IntArray {
                lo,
                len,
                elements_are_bool,
                ..
            } => {
                assert_eq!(*lo, 0);
                assert_eq!(*len, 3);
                assert!(
                    *elements_are_bool,
                    "Bool-valued IntFunc should have elements_are_bool=true"
                );
            }
            other => panic!("expected IntArray, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_record_all_scalar() {
        let registry = VarRegistry::from_names(["msg"]);
        let rec = RecordValue::from_sorted_str_entries(vec![
            (Arc::from("src"), Value::SmallInt(1)),
            (Arc::from("type"), Value::SmallInt(0)),
        ]);
        let state = ArrayState::from_values(vec![Value::Record(rec)]);

        let layout = infer_layout(&state, &registry);
        assert_eq!(layout.var_count(), 1);

        let vl = layout.var_layout(0).unwrap();
        match &vl.kind {
            VarLayoutKind::Record { field_names, .. } => {
                assert_eq!(field_names.len(), 2);
            }
            other => panic!("expected Record, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_small_set_as_dynamic() {
        // Sets are always Dynamic until bitmask encoding is implemented (Phase 6).
        // See #4007.
        let registry = VarRegistry::from_names(["nodes"]);
        let set = SortedSet::from_sorted_vec(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(3),
        ]);
        let state = ArrayState::from_values(vec![Value::Set(Arc::new(set))]);

        let layout = infer_layout(&state, &registry);
        let vl = layout.var_layout(0).unwrap();
        assert!(
            matches!(&vl.kind, VarLayoutKind::Dynamic),
            "expected Dynamic for set, got {:?}",
            vl.kind
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_mixed() {
        let registry = VarRegistry::from_names(["pc", "network", "msgs"]);

        // pc = 0 (scalar)
        // network = [0 |-> 0, 1 |-> 0, 2 |-> 0] (IntArray)
        // msgs = <<1, 2>> (Dynamic - sequence)
        let func = IntIntervalFunc::new(
            0,
            2,
            vec![Value::SmallInt(0), Value::SmallInt(0), Value::SmallInt(0)],
        );
        let seq =
            tla_value::value::SeqValue::from_vec(vec![Value::SmallInt(1), Value::SmallInt(2)]);
        let state = ArrayState::from_values(vec![
            Value::SmallInt(0),
            Value::IntFunc(Arc::new(func)),
            Value::Seq(Arc::new(seq)),
        ]);

        let layout = infer_layout(&state, &registry);
        assert_eq!(layout.var_count(), 3);
        // pc: 1 slot + network: 3 slots + msgs: 1 slot (Dynamic) = 5
        assert_eq!(layout.total_slots(), 5);
        assert!(!layout.is_all_scalar());
        assert!(!layout.is_trivial());

        // Verify kinds
        assert!(matches!(
            layout.var_layout(0).unwrap().kind,
            VarLayoutKind::Scalar
        ));
        assert!(matches!(
            layout.var_layout(1).unwrap().kind,
            VarLayoutKind::IntArray { lo: 0, len: 3, .. }
        ));
        assert!(matches!(
            layout.var_layout(2).unwrap().kind,
            VarLayoutKind::Dynamic
        ));
    }

    // ====================================================================
    // Wavefront inference tests (Part of #3986)
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_from_wavefront_single_state() {
        // Wavefront with one state should match single-state inference.
        let registry = VarRegistry::from_names(["x", "y"]);
        let state = ArrayState::from_values(vec![Value::SmallInt(1), Value::Bool(true)]);

        let single = infer_layout(&state, &registry);
        let wavefront = infer_layout_from_wavefront(&[state], &registry);

        assert_eq!(single.var_count(), wavefront.var_count());
        assert_eq!(single.total_slots(), wavefront.total_slots());
        for i in 0..single.var_count() {
            assert_eq!(
                single.var_layout(i).unwrap().kind,
                wavefront.var_layout(i).unwrap().kind,
                "var {i} layout kind mismatch between single and wavefront"
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_from_wavefront_consistent_states() {
        // Multiple states with the same structure should produce the same layout.
        let registry = VarRegistry::from_names(["x", "y"]);
        let states = vec![
            ArrayState::from_values(vec![Value::SmallInt(1), Value::Bool(true)]),
            ArrayState::from_values(vec![Value::SmallInt(2), Value::Bool(false)]),
            ArrayState::from_values(vec![Value::SmallInt(3), Value::Bool(true)]),
        ];

        let layout = infer_layout_from_wavefront(&states, &registry);

        assert_eq!(layout.var_count(), 2);
        assert!(matches!(
            layout.var_layout(0).unwrap().kind,
            VarLayoutKind::Scalar
        ));
        assert!(matches!(
            layout.var_layout(1).unwrap().kind,
            VarLayoutKind::ScalarBool
        ));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_from_wavefront_int_array_consistent() {
        // Multiple states with compatible IntFunc should keep IntArray layout.
        let registry = VarRegistry::from_names(["arr"]);
        let mk_state = |a: i64, b: i64, c: i64| {
            let func = IntIntervalFunc::new(
                0,
                2,
                vec![Value::SmallInt(a), Value::SmallInt(b), Value::SmallInt(c)],
            );
            ArrayState::from_values(vec![Value::IntFunc(Arc::new(func))])
        };

        let states = vec![mk_state(1, 2, 3), mk_state(4, 5, 6), mk_state(7, 8, 9)];
        let layout = infer_layout_from_wavefront(&states, &registry);

        assert_eq!(layout.total_slots(), 3);
        assert!(matches!(
            layout.var_layout(0).unwrap().kind,
            VarLayoutKind::IntArray {
                lo: 0,
                len: 3,
                elements_are_bool: false,
                ..
            }
        ));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_from_wavefront_incompatible_downgrades() {
        // If one state has a Scalar but another has a different shape,
        // the wavefront should downgrade to Dynamic.
        let registry = VarRegistry::from_names(["x"]);
        let state_int = ArrayState::from_values(vec![Value::SmallInt(42)]);
        let state_bool = ArrayState::from_values(vec![Value::Bool(true)]);

        // SmallInt -> Scalar, Bool -> ScalarBool: these are incompatible.
        let layout = infer_layout_from_wavefront(&[state_int, state_bool], &registry);

        assert!(
            matches!(layout.var_layout(0).unwrap().kind, VarLayoutKind::Dynamic),
            "incompatible Scalar vs ScalarBool should downgrade to Dynamic, got {:?}",
            layout.var_layout(0).unwrap().kind
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_from_wavefront_int_array_length_mismatch() {
        // IntArray with different lengths should downgrade to Dynamic.
        let registry = VarRegistry::from_names(["arr"]);
        let func3 = IntIntervalFunc::new(
            0,
            2,
            vec![Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)],
        );
        let func4 = IntIntervalFunc::new(
            0,
            3,
            vec![
                Value::SmallInt(1),
                Value::SmallInt(2),
                Value::SmallInt(3),
                Value::SmallInt(4),
            ],
        );

        let states = vec![
            ArrayState::from_values(vec![Value::IntFunc(Arc::new(func3))]),
            ArrayState::from_values(vec![Value::IntFunc(Arc::new(func4))]),
        ];
        let layout = infer_layout_from_wavefront(&states, &registry);

        assert!(
            matches!(layout.var_layout(0).unwrap().kind, VarLayoutKind::Dynamic),
            "IntArray with different lengths should downgrade to Dynamic, got {:?}",
            layout.var_layout(0).unwrap().kind
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_infer_layout_from_wavefront_mixed_keeps_stable() {
        // A wavefront where some vars are stable and others are not.
        let registry = VarRegistry::from_names(["stable_int", "unstable"]);
        let states = vec![
            ArrayState::from_values(vec![Value::SmallInt(1), Value::SmallInt(10)]),
            ArrayState::from_values(vec![Value::SmallInt(2), Value::Bool(true)]),
        ];

        let layout = infer_layout_from_wavefront(&states, &registry);

        // stable_int: Scalar in both states -> stays Scalar
        assert!(matches!(
            layout.var_layout(0).unwrap().kind,
            VarLayoutKind::Scalar
        ));
        // unstable: Scalar in first, ScalarBool in second -> Dynamic
        assert!(matches!(
            layout.var_layout(1).unwrap().kind,
            VarLayoutKind::Dynamic
        ));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_layout_kinds_compatible_same() {
        assert!(layout_kinds_compatible(
            &VarLayoutKind::Scalar,
            &VarLayoutKind::Scalar
        ));
        assert!(layout_kinds_compatible(
            &VarLayoutKind::ScalarBool,
            &VarLayoutKind::ScalarBool
        ));
        assert!(layout_kinds_compatible(
            &VarLayoutKind::Dynamic,
            &VarLayoutKind::Dynamic
        ));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_layout_kinds_compatible_different_variant() {
        assert!(!layout_kinds_compatible(
            &VarLayoutKind::Scalar,
            &VarLayoutKind::ScalarBool
        ));
        assert!(!layout_kinds_compatible(
            &VarLayoutKind::Scalar,
            &VarLayoutKind::Dynamic
        ));
    }
}
