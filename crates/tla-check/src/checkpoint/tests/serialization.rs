// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for value/state serialization roundtrips and parse error handling.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_serializable_value_roundtrip() {
    // Test basic types
    let bool_val = Value::Bool(true);
    let sv = SerializableValue::from_value(&bool_val).unwrap();
    assert_eq!(sv.to_value().unwrap(), bool_val);

    let int_val = Value::int(42);
    let sv = SerializableValue::from_value(&int_val).unwrap();
    assert_eq!(sv.to_value().unwrap(), int_val);

    let str_val = Value::String(Arc::from("hello"));
    let sv = SerializableValue::from_value(&str_val).unwrap();
    assert_eq!(sv.to_value().unwrap(), str_val);

    let model_val = Value::try_model_value("mv_checkpoint").unwrap();
    let sv = SerializableValue::from_value(&model_val).unwrap();
    assert_eq!(sv.to_value().unwrap(), model_val);

    // Test collections
    let set_val = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
    let sv = SerializableValue::from_value(&set_val).unwrap();
    assert_eq!(sv.to_value().unwrap(), set_val);

    let seq_val = Value::seq(vec![Value::int(1), Value::int(2)]);
    let sv = SerializableValue::from_value(&seq_val).unwrap();
    assert_eq!(sv.to_value().unwrap(), seq_val);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_serializable_state_roundtrip() {
    let mut state = State::new();
    state = state.with_var("x", Value::int(42));
    state = state.with_var("y", Value::Bool(true));
    state = state.with_var(
        "s",
        Value::set([Value::int(1), Value::int(2), Value::int(3)]),
    );

    let ss = SerializableState::from_state(&state).unwrap();
    let restored = ss.to_state().unwrap();

    assert_eq!(restored.get("x").unwrap(), &Value::int(42));
    assert_eq!(restored.get("y").unwrap(), &Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_serializable_value_int_parse_failure_returns_error() {
    let sv = SerializableValue::Int("not-a-decimal".to_string());
    let err = sv.to_value().unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(err
        .to_string()
        .contains("invalid integer in checkpoint Int"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_serializable_value_interval_parse_failure_returns_error() {
    let sv = SerializableValue::Interval {
        lo: "1".to_string(),
        hi: "bad-bound".to_string(),
    };
    let err = sv.to_value().unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(err
        .to_string()
        .contains("invalid integer in checkpoint Interval.hi"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_serializable_value_interval_lo_parse_failure_returns_error() {
    let sv = SerializableValue::Interval {
        lo: "bad-bound".to_string(),
        hi: "2".to_string(),
    };
    let err = sv.to_value().unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(err
        .to_string()
        .contains("invalid integer in checkpoint Interval.lo"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_load_fails_on_corrupted_integer_string() {
    let dir = tempdir().unwrap();
    let checkpoint_dir = dir.path().join("checkpoint");

    let mut checkpoint = Checkpoint::new();
    let mut state = State::new();
    state = state.with_var("x", Value::int(42));
    checkpoint.frontier = vec![state];

    checkpoint.save(&checkpoint_dir).unwrap();

    fs::write(
        checkpoint_dir.join("frontier.json"),
        r#"[{"vars":[["x",{"type":"Int","value":"not-a-decimal"}]]}]"#,
    )
    .unwrap();

    let err = Checkpoint::load(&checkpoint_dir).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(err
        .to_string()
        .contains("invalid integer in checkpoint Int"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_load_fails_on_corrupted_interval_bound() {
    let dir = tempdir().unwrap();
    let checkpoint_dir = dir.path().join("checkpoint");

    let mut checkpoint = Checkpoint::new();
    let mut state = State::new();
    state = state.with_var(
        "x",
        Value::Interval(Arc::new(crate::value::IntervalValue::new(
            BigInt::from(1),
            BigInt::from(2),
        ))),
    );
    checkpoint.frontier = vec![state];

    checkpoint.save(&checkpoint_dir).unwrap();

    fs::write(
        checkpoint_dir.join("frontier.json"),
        r#"[{"vars":[["x",{"type":"Interval","value":{"lo":"bad-bound","hi":"2"}}]]}]"#,
    )
    .unwrap();

    let err = Checkpoint::load(&checkpoint_dir).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(err
        .to_string()
        .contains("invalid integer in checkpoint Interval.lo"));
}
