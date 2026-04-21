// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::kani_harnesses::test_helpers::{make_func, make_set};
use crate::state::State;
use crate::value::{RecordBuilder, Value};
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_equality_reflexive() {
    let values = vec![
        Value::Bool(true),
        Value::Bool(false),
        Value::int(0),
        Value::int(42),
        Value::string("hello"),
        Value::string(""),
    ];
    for v in values {
        assert_eq!(v, v, "Value equality must be reflexive");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_type_discrimination() {
    let b = Value::Bool(true);
    let i = Value::int(1);
    let s = Value::string("true");

    assert_ne!(b, i, "Bool and Int must never be equal");
    assert_ne!(b, s, "Bool and String must never be equal");
    assert_ne!(i, s, "Int and String must never be equal");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_equality_reflexive() {
    let s = make_set(vec![Value::Bool(true), Value::Bool(false)]);
    assert_eq!(s, s, "Set equality must be reflexive");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_equality_reflexive() {
    let f = Value::Func(Arc::new(make_func(vec![(
        Value::int(1),
        Value::Bool(true),
    )])));
    assert_eq!(f, f, "Function equality must be reflexive");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_structural_equality() {
    let entries = vec![(Value::int(1), Value::Bool(true))];
    let f1 = make_func(entries.clone());
    let f2 = make_func(entries);
    let v1 = Value::Func(Arc::new(f1));
    let v2 = Value::Func(Arc::new(f2));
    assert_eq!(
        v1, v2,
        "Functions with same domain and mapping must be equal"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_equality_reflexive() {
    let mut builder = RecordBuilder::new();
    builder.insert_str("x", Value::Bool(true));
    builder.insert_str("y", Value::int(42));
    let r = Value::Record(builder.build());

    assert_eq!(r, r, "Record equality must be reflexive");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seq_equality_reflexive() {
    let s = Value::Seq(Arc::new(vec![Value::int(1), Value::int(2)].into()));
    assert_eq!(s, s, "Sequence equality must be reflexive");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_equality_reflexive() {
    let t = Value::Tuple(vec![Value::Bool(true), Value::int(42)].into());
    assert_eq!(t, t, "Tuple equality must be reflexive");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cross_type_inequality() {
    let s = make_set(vec![Value::int(1)]);
    let seq = Value::Seq(Arc::new(vec![Value::int(1)].into()));
    let f = Value::Func(Arc::new(make_func(vec![(
        Value::int(1),
        Value::Bool(true),
    )])));

    let mut builder = RecordBuilder::new();
    builder.insert_str("x", Value::int(1));
    let r = Value::Record(builder.build());

    assert_ne!(s, seq, "Set and Sequence must never be equal");
    assert_ne!(s, f, "Set and Function must never be equal");
    assert_ne!(s, r, "Set and Record must never be equal");
    assert_ne!(seq, f, "Sequence and Function must never be equal");
    assert_ne!(seq, r, "Sequence and Record must never be equal");
    assert_ne!(f, r, "Function and Record must never be equal");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_clone_equality() {
    let values = vec![
        Value::Bool(true),
        Value::Bool(false),
        Value::int(0),
        Value::int(-999),
        Value::string(""),
        Value::string("test"),
    ];

    for v in values {
        let v_clone = v.clone();
        assert_eq!(v, v_clone, "Cloned value must equal original");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_clone_equality() {
    let s = make_set(vec![Value::int(1), Value::int(2)]);
    let s_clone = s.clone();
    assert_eq!(s, s_clone, "Cloned set must equal original");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_clone_equality() {
    let s = State::from_pairs([("x", Value::Bool(true)), ("y", Value::int(42))]);
    let s_clone = s.clone();

    assert_eq!(s, s_clone, "Cloned state must equal original");
    assert_eq!(
        s.fingerprint(),
        s_clone.fingerprint(),
        "Cloned state must have same fingerprint"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_clone_independence() {
    let v = Value::int(42);
    let s1 = State::from_pairs([("x", v)]);
    let s2 = s1.clone();
    let s3 = s2.with_var("x", Value::int(100));

    assert_eq!(s1, s2);
    assert_ne!(s1, s3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_value_equality_by_name() {
    let v1 = Value::ModelValue(Arc::from("m1"));
    let v2 = Value::ModelValue(Arc::from("m1"));
    let v3 = Value::ModelValue(Arc::from("m2"));

    assert_eq!(v1, v2, "Same name model values must be equal");
    assert_ne!(v1, v3, "Different name model values must not be equal");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_value_equality_reflexive() {
    for name in ["m1", "m2", "m3"] {
        let v = Value::ModelValue(Arc::from(name));
        assert_eq!(v, v, "ModelValue equality must be reflexive");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_value_type_discrimination() {
    let mv = Value::ModelValue(Arc::from("m1"));
    let b = Value::Bool(true);
    let i = Value::int(1);
    let s = Value::String(Arc::from("m1"));

    assert_ne!(mv, b, "ModelValue must not equal Bool");
    assert_ne!(mv, i, "ModelValue must not equal Int");
    assert_ne!(mv, s, "ModelValue must not equal String with same text");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_equality_different_domains() {
    let val = Value::Bool(true);
    let f1 = make_func(vec![(Value::int(1), val.clone())]);
    let f2 = make_func(vec![(Value::int(2), val)]);

    let v1 = Value::Func(Arc::new(f1));
    let v2 = Value::Func(Arc::new(f2));
    assert_ne!(v1, v2, "Functions with different domains must not be equal");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_equality_different_mappings() {
    let key = Value::int(1);
    let f1 = make_func(vec![(key.clone(), Value::Bool(true))]);
    let f2 = make_func(vec![(key, Value::Bool(false))]);

    let v1 = Value::Func(Arc::new(f1));
    let v2 = Value::Func(Arc::new(f2));
    assert_ne!(
        v1, v2,
        "Functions with different mappings must not be equal"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_equality_when_identical() {
    let entries = vec![
        (Value::int(1), Value::Bool(false)),
        (Value::int(2), Value::Bool(true)),
        (Value::int(3), Value::Bool(false)),
    ];
    let f1 = make_func(entries.clone());
    let f2 = make_func(entries);

    let v1 = Value::Func(Arc::new(f1));
    let v2 = Value::Func(Arc::new(f2));
    assert_eq!(
        v1, v2,
        "Functions with same domain and mapping must be equal"
    );
}
