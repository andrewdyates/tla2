// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_new() {
    let state = State::new();
    assert!(state.is_empty());
    assert_eq!(state.len(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_from_iter() {
    let state = State::from_pairs([("x", Value::int(1)), ("y", Value::int(2))]);
    assert_eq!(state.len(), 2);
    assert_eq!(state.get("x"), Some(&Value::int(1)));
    assert_eq!(state.get("y"), Some(&Value::int(2)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_with_var() {
    let s1 = State::new();
    let s2 = s1.with_var("x", Value::int(1));
    let s3 = s2.with_var("y", Value::int(2));

    assert!(s1.is_empty());
    assert_eq!(s2.len(), 1);
    assert_eq!(s3.len(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_deterministic() {
    let s1 = State::from_pairs([("x", Value::int(1)), ("y", Value::int(2))]);
    let s2 = State::from_pairs([("y", Value::int(2)), ("x", Value::int(1))]);

    assert_eq!(s1.fingerprint(), s2.fingerprint());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_smallint_signed_bytes_matches_bigint() {
    fn smallint_signed_bytes_le(n: i64) -> Vec<u8> {
        let bytes = n.to_le_bytes();
        let mut len = bytes.len();
        if n >= 0 {
            while len > 1 && bytes[len - 1] == 0x00 && (bytes[len - 2] & 0x80) == 0 {
                len -= 1;
            }
        } else {
            while len > 1 && bytes[len - 1] == 0xFF && (bytes[len - 2] & 0x80) != 0 {
                len -= 1;
            }
        }
        bytes[..len].to_vec()
    }

    for n in [
        0i64,
        1,
        -1,
        2,
        -2,
        127,
        128,
        255,
        256,
        -127,
        -128,
        -129,
        i64::MAX,
        i64::MIN,
    ] {
        let big = n.to_bigint().unwrap();
        assert_eq!(smallint_signed_bytes_le(n), big.to_signed_bytes_le());
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_different_values() {
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s2 = State::from_pairs([("x", Value::int(2))]);

    assert_ne!(s1.fingerprint(), s2.fingerprint());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_different_vars() {
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s2 = State::from_pairs([("y", Value::int(1))]);

    assert_ne!(s1.fingerprint(), s2.fingerprint());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_equality() {
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s2 = State::from_pairs([("x", Value::int(1))]);
    let s3 = State::from_pairs([("x", Value::int(2))]);

    assert_eq!(s1, s2);
    assert_ne!(s1, s3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_complex_values() {
    let s1 = State::from_pairs([
        ("set", Value::set([Value::int(1), Value::int(2)])),
        ("seq", Value::seq([Value::string("a"), Value::string("b")])),
    ]);
    let s2 = State::from_pairs([
        ("seq", Value::seq([Value::string("a"), Value::string("b")])),
        ("set", Value::set([Value::int(2), Value::int(1)])),
    ]);

    assert_eq!(s1.fingerprint(), s2.fingerprint());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_func_tuple_seq_intfunc_equivalence() {
    let elems = vec![
        Value::String(Arc::from("tok")),
        Value::SmallInt(42),
        Value::Bool(true),
    ];

    let func = Value::Func(Arc::new(crate::value::FuncValue::from_sorted_entries(
        vec![
            (Value::SmallInt(1), elems[0].clone()),
            (Value::SmallInt(2), elems[1].clone()),
            (Value::SmallInt(3), elems[2].clone()),
        ],
    )));
    let tuple = Value::Tuple(elems.clone().into());
    let seq = Value::Seq(Arc::new(crate::value::SeqValue::from(elems.clone())));
    let intfunc = Value::IntFunc(Arc::new(crate::value::IntIntervalFunc::new(1, 3, elems)));

    let func_state = State::from_pairs([("x", func)]);
    let tuple_state = State::from_pairs([("x", tuple)]);
    let seq_state = State::from_pairs([("x", seq)]);
    let intfunc_state = State::from_pairs([("x", intfunc)]);

    assert_eq!(func_state.fingerprint(), tuple_state.fingerprint());
    assert_eq!(func_state.fingerprint(), seq_state.fingerprint());
    assert_eq!(func_state.fingerprint(), intfunc_state.fingerprint());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_func_shifted_intfunc_equivalence() {
    let vals = vec![
        Value::String(Arc::from("left")),
        Value::String(Arc::from("right")),
    ];

    let func = Value::Func(Arc::new(crate::value::FuncValue::from_sorted_entries(
        vec![
            (Value::SmallInt(2), vals[0].clone()),
            (Value::SmallInt(3), vals[1].clone()),
        ],
    )));
    let intfunc = Value::IntFunc(Arc::new(crate::value::IntIntervalFunc::new(2, 3, vals)));

    let func_state = State::from_pairs([("x", func)]);
    let intfunc_state = State::from_pairs([("x", intfunc)]);

    assert_eq!(func_state.fingerprint(), intfunc_state.fingerprint());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_func_record_equivalence() {
    let func = Value::Func(Arc::new(crate::value::FuncValue::from_sorted_entries(
        vec![
            (Value::String(Arc::from("a")), Value::SmallInt(1)),
            (
                Value::String(Arc::from("b")),
                Value::String(Arc::from("tok")),
            ),
        ],
    )));
    let record = Value::record([
        ("a", Value::SmallInt(1)),
        ("b", Value::String(Arc::from("tok"))),
    ]);

    let func_state = State::from_pairs([("x", func)]);
    let record_state = State::from_pairs([("x", record)]);

    assert_eq!(func_state.fingerprint(), record_state.fingerprint());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_interval_set_equivalence() {
    let interval = Value::Interval(Arc::new(crate::value::IntervalValue::new(
        1.into(),
        3.into(),
    )));
    let set = Value::set([Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)]);

    let interval_state = State::from_pairs([("x", interval)]);
    let set_state = State::from_pairs([("x", set)]);

    assert_eq!(interval_state.fingerprint(), set_state.fingerprint());
}
