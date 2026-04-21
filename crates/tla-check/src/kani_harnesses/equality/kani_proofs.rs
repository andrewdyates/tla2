// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::kani_harnesses::kani_generators::*;
use crate::state::State;
use crate::value::{FuncValue, Value};
use std::sync::Arc;

// P2: Value Equality Reflexivity

#[kani::proof]
fn verify_bool_equality_reflexive() {
    let v = any_bool_value();
    assert!(v == v, "Value equality must be reflexive");
}

#[kani::proof]
fn verify_int_equality_reflexive() {
    let v = any_small_int_value();
    assert!(v == v, "Value equality must be reflexive");
}

#[kani::proof]
fn verify_string_equality_reflexive() {
    let v = any_short_string_value();
    assert!(v == v, "Value equality must be reflexive");
}

#[kani::proof]
fn verify_value_equality_reflexive() {
    let v = any_primitive_value();
    assert!(v == v, "Value equality must be reflexive");
}

// P3: Value Equality Symmetry

#[kani::proof]
fn verify_bool_equality_symmetric() {
    let v1 = any_bool_value();
    let v2 = any_bool_value();
    if v1 == v2 {
        assert!(v2 == v1, "Value equality must be symmetric");
    }
}

#[kani::proof]
fn verify_int_equality_symmetric() {
    let v1 = any_small_int_value();
    let v2 = any_small_int_value();
    if v1 == v2 {
        assert!(v2 == v1, "Value equality must be symmetric");
    }
}

#[kani::proof]
fn verify_string_equality_symmetric() {
    let v1 = any_short_string_value();
    let v2 = any_short_string_value();
    if v1 == v2 {
        assert!(v2 == v1, "Value equality must be symmetric");
    }
}

// P5: Type Discrimination

#[kani::proof]
fn verify_bool_int_not_equal() {
    let b = any_bool_value();
    let i = any_small_int_value();
    assert!(b != i, "Bool and Int must never be equal");
}

#[kani::proof]
fn verify_bool_string_not_equal() {
    let b = any_bool_value();
    let s = any_short_string_value();
    assert!(b != s, "Bool and String must never be equal");
}

#[kani::proof]
fn verify_int_string_not_equal() {
    let i = any_small_int_value();
    let s = any_short_string_value();
    assert!(i != s, "Int and String must never be equal");
}

// Per-type equality reflexivity

#[kani::proof]
fn verify_set_equality_reflexive() {
    let s = any_small_set();
    assert!(s == s, "Set equality must be reflexive");
}

#[kani::proof]
fn verify_func_equality_reflexive() {
    let f = any_small_func();
    let v = Value::Func(Arc::new(f));
    assert!(v == v, "Function equality must be reflexive");
}

#[kani::proof]
fn verify_record_equality_reflexive() {
    let r = any_small_record();
    assert!(r == r, "Record equality must be reflexive");
}

#[kani::proof]
fn verify_seq_equality_reflexive() {
    let s = any_small_seq();
    assert!(s == s, "Sequence equality must be reflexive");
}

#[kani::proof]
fn verify_tuple_equality_reflexive() {
    let t = any_small_tuple();
    assert!(t == t, "Tuple equality must be reflexive");
}

// P15: Cross-type properties

#[kani::proof]
fn verify_set_seq_not_equal() {
    let s = any_small_set();
    let seq = any_small_seq();
    assert!(s != seq, "Set and Sequence must never be equal");
}

#[kani::proof]
fn verify_set_func_not_equal() {
    let s = any_small_set();
    let f = Value::Func(Arc::new(any_small_func()));
    assert!(s != f, "Set and Function must never be equal");
}

#[kani::proof]
fn verify_set_record_not_equal() {
    let s = any_small_set();
    let r = any_small_record();
    assert!(s != r, "Set and Record must never be equal");
}

// P24: Value Clone Correctness

#[kani::proof]
fn verify_value_clone_equality() {
    let v = any_primitive_value();
    let v_clone = v.clone();
    assert!(v == v_clone, "Cloned value must equal original");
}

#[kani::proof]
fn verify_set_clone_equality() {
    let s = any_small_set();
    let s_clone = s.clone();
    assert!(s == s_clone, "Cloned set must equal original");
}

// P25: State Clone Correctness

#[kani::proof]
fn verify_state_clone_equality() {
    let v = any_primitive_value();
    let s = State::from_pairs([("x", v)]);
    let s_clone = s.clone();
    assert!(s == s_clone, "Cloned state must equal original");
    assert!(
        s.fingerprint() == s_clone.fingerprint(),
        "Cloned state must have same fingerprint"
    );
}

// P50: Function Equality Semantics

#[kani::proof]
fn verify_func_equality_same_domain_required() {
    let val = Value::Bool(true);
    let f1 = make_func(vec![(Value::int(1), val.clone())]);
    let f2 = make_func(vec![(Value::int(2), val)]);

    let (v1, v2) = (Value::Func(Arc::new(f1)), Value::Func(Arc::new(f2)));
    assert!(
        v1 != v2,
        "Functions with different domains must not be equal"
    );
}

#[kani::proof]
fn verify_func_equality_same_mapping_required() {
    let key = Value::int(1);
    let f1 = make_func(vec![(key.clone(), Value::Bool(true))]);
    let f2 = make_func(vec![(key, Value::Bool(false))]);

    let v1 = Value::Func(Arc::new(f1));
    let v2 = Value::Func(Arc::new(f2));
    assert!(
        v1 != v2,
        "Functions with different mappings must not be equal"
    );
}

#[kani::proof]
fn verify_func_equality_when_identical() {
    let f1 = any_small_func();
    let entries: Vec<(Value, Value)> = f1
        .mapping_iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    let f2 = FuncValue::from_sorted_entries(entries);

    let v1 = Value::Func(Arc::new(f1));
    let v2 = Value::Func(Arc::new(f2));
    assert!(
        v1 == v2,
        "Functions with same domain and mapping must be equal"
    );
}

// P11: Function structural equality

#[kani::proof]
fn verify_func_structural_equality() {
    let f1 = any_small_func();
    let entries: Vec<(Value, Value)> = f1
        .mapping_iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    let f2 = FuncValue::from_sorted_entries(entries);
    let v1 = Value::Func(Arc::new(f1));
    let v2 = Value::Func(Arc::new(f2));
    assert!(
        v1 == v2,
        "Functions with same domain and mapping must be equal"
    );
}

// P55: ModelValue Equality

#[kani::proof]
fn verify_model_value_equality_by_name() {
    let name1 = any_model_value_name();
    let name2 = any_model_value_name();
    let v1 = Value::ModelValue(name1.clone());
    let v2 = Value::ModelValue(name2.clone());

    if name1 == name2 {
        assert!(v1 == v2, "Same name model values must be equal");
    } else {
        assert!(v1 != v2, "Different name model values must not be equal");
    }
}

#[kani::proof]
fn verify_model_value_equality_reflexive() {
    let name = any_model_value_name();
    let v = Value::ModelValue(name);
    assert!(v == v, "ModelValue equality must be reflexive");
}

#[kani::proof]
fn verify_model_value_type_discrimination() {
    let mv = Value::ModelValue(Arc::from("m1"));
    let b = Value::Bool(true);
    let i = Value::int(1);
    let s = Value::String(Arc::from("m1"));

    assert!(mv != b, "ModelValue must not equal Bool");
    assert!(mv != i, "ModelValue must not equal Int");
    assert!(mv != s, "ModelValue must not equal String with same text");
}

// P-BoolOnly equality

#[kani::proof]
fn verify_set_equality_reflexive_boolonly() {
    let s = any_small_set_boolonly();
    assert!(s == s, "Set equality must be reflexive");
}

#[kani::proof]
fn verify_seq_equality_reflexive_boolonly() {
    let s = any_small_seq_boolonly();
    assert!(s == s, "Sequence equality must be reflexive");
}
