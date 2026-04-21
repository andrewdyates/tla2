// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constructor and accessor surface tests for core Value types.
//!
//! Covers: bool, int, string, set, seq, tuple, record, func constructors,
//! basic accessors, tuple-like coercion, and type-ordering smoke check.

use super::super::super::*;
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bool_values() {
    let t = Value::bool(true);
    let f = Value::bool(false);
    assert_eq!(t, Value::Bool(true));
    assert_eq!(f, Value::Bool(false));
    assert_eq!(t.as_bool(), Some(true));
    assert_eq!(f.as_bool(), Some(false));
    assert_eq!(Value::int(0).as_bool(), None);
    assert_eq!(Value::string("TRUE").as_bool(), None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_values() {
    // Value::int() now creates SmallInt for i64 values
    assert_eq!(Value::int(42), Value::SmallInt(42));
    assert_eq!(Value::int(-5).as_i64(), Some(-5));
    // SmallInt and Int should compare equal for same value
    assert_eq!(Value::SmallInt(42), Value::big_int(BigInt::from(42)));
    // big_int normalizes to SmallInt when value fits
    assert_eq!(Value::big_int(BigInt::from(100)), Value::SmallInt(100));
    assert_eq!(Value::int(i64::MAX).as_i64(), Some(i64::MAX));
    assert_eq!(Value::int(i64::MIN).as_i64(), Some(i64::MIN));

    // Values outside i64 must stay in Int variant and not round-trip through as_i64().
    let above_i64 = BigInt::from(i64::MAX) + BigInt::from(1);
    let below_i64 = BigInt::from(i64::MIN) - BigInt::from(1);
    assert!(matches!(Value::big_int(above_i64.clone()), Value::Int(_)));
    assert!(matches!(Value::big_int(below_i64.clone()), Value::Int(_)));
    assert_eq!(Value::big_int(above_i64).as_i64(), None);
    assert_eq!(Value::big_int(below_i64).as_i64(), None);
    assert_eq!(Value::string("42").as_i64(), None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_string_values() {
    let s = Value::string("hello");
    assert_eq!(s.as_string(), Some("hello"));
    let escaped = Value::string("line1\\nline2");
    assert_eq!(escaped.as_string(), Some("line1\\nline2"));
    let unicode = Value::string("\u{03C0}");
    assert_eq!(unicode.as_string(), Some("\u{03C0}"));
    // Empty string
    let empty = Value::string("");
    assert_eq!(empty.as_string(), Some(""));
    // Negative: non-string value
    assert_eq!(Value::int(42).as_string(), None);
    assert_eq!(Value::bool(true).as_string(), None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_values() {
    let s = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
    let set = s.as_set().unwrap();
    assert_eq!(set.len(), 3);
    // Verify ALL elements present, not just one
    assert!(set.contains(&Value::int(1)), "set missing element 1");
    assert!(set.contains(&Value::int(2)), "set missing element 2");
    assert!(set.contains(&Value::int(3)), "set missing element 3");
    // Negative: non-member
    assert!(!set.contains(&Value::int(4)), "set should not contain 4");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_deduplication() {
    let s = Value::set([Value::int(1), Value::int(1), Value::int(2)]);
    let set = s.as_set().unwrap();
    assert_eq!(set.len(), 2);
    assert!(set.contains(&Value::int(1)));
    assert!(set.contains(&Value::int(2)));
    assert!(!set.contains(&Value::int(3)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seq_values() {
    let s = Value::seq([Value::int(1), Value::int(2), Value::int(3)]);
    let seq = s.as_seq().unwrap();
    assert_eq!(seq.len(), 3);
    // Verify ALL elements, not just the first
    assert_eq!(seq[0], Value::int(1));
    assert_eq!(seq[1], Value::int(2));
    assert_eq!(seq[2], Value::int(3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_values() {
    let t = Value::tuple([Value::int(1), Value::string("a"), Value::bool(true)]);
    let tuple = t.as_tuple().unwrap();
    assert_eq!(tuple.len(), 3);
    assert_eq!(tuple[0], Value::int(1));
    assert_eq!(tuple[1], Value::string("a"));
    assert_eq!(tuple[2], Value::bool(true));
}

/// Test to_tuple_like_elements() for TLC-parity tuple coercion.
/// Part of #700: tuple patterns should accept Tuple, Seq, and sequence-like functions.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_tuple_like_elements() {
    // Tuple - direct extraction
    let t = Value::tuple([Value::int(1), Value::int(2)]);
    let elems = t.to_tuple_like_elements().unwrap();
    assert_eq!(elems.len(), 2);
    assert_eq!(elems[0], Value::int(1));
    assert_eq!(elems[1], Value::int(2));

    // Seq - convert to slice
    let s = Value::seq([Value::int(3), Value::int(4)]);
    let elems = s.to_tuple_like_elements().unwrap();
    assert_eq!(elems.len(), 2);
    assert_eq!(elems[0], Value::int(3));
    assert_eq!(elems[1], Value::int(4));

    // IntFunc with min=1 - sequence-like
    let int_func = Value::IntFunc(Arc::new(crate::value::IntIntervalFunc::new(
        1,
        2,
        vec![Value::int(5), Value::int(6)],
    )));
    let elems = int_func.to_tuple_like_elements().unwrap();
    assert_eq!(elems.len(), 2);
    assert_eq!(elems[0], Value::int(5));
    assert_eq!(elems[1], Value::int(6));

    // IntFunc with min!=1 - NOT sequence-like
    let int_func_2 = Value::IntFunc(Arc::new(crate::value::IntIntervalFunc::new(
        2,
        3,
        vec![Value::int(7), Value::int(8)],
    )));
    assert!(int_func_2.to_tuple_like_elements().is_none());

    // Func with domain 1..n - sequence-like
    let mut fb = FuncBuilder::new();
    fb.insert(Value::int(1), Value::int(9));
    fb.insert(Value::int(2), Value::int(10));
    let func = Value::Func(Arc::new(fb.build()));
    let elems = func.to_tuple_like_elements().unwrap();
    assert_eq!(elems.len(), 2);
    assert_eq!(elems[0], Value::int(9));
    assert_eq!(elems[1], Value::int(10));

    // Func with domain NOT 1..n - NOT sequence-like
    let mut fb2 = FuncBuilder::new();
    fb2.insert(Value::int(0), Value::int(11));
    fb2.insert(Value::int(1), Value::int(12));
    let func2 = Value::Func(Arc::new(fb2.build()));
    assert!(func2.to_tuple_like_elements().is_none());

    // Empty tuple/seq/func
    let empty_tuple = Value::tuple([]);
    assert_eq!(empty_tuple.to_tuple_like_elements().unwrap().len(), 0);

    let empty_seq = Value::seq([]);
    assert_eq!(empty_seq.to_tuple_like_elements().unwrap().len(), 0);

    // Non-tuple-like values should return None
    assert!(Value::int(42).to_tuple_like_elements().is_none());
    assert!(Value::Bool(true).to_tuple_like_elements().is_none());
    assert!(Value::string("hello").to_tuple_like_elements().is_none());

    // Func with non-integer keys - NOT sequence-like
    let mut fb3 = FuncBuilder::new();
    fb3.insert(Value::string("a"), Value::int(13));
    fb3.insert(Value::string("b"), Value::int(14));
    let func3 = Value::Func(Arc::new(fb3.build()));
    assert!(func3.to_tuple_like_elements().is_none());

    // Func with gaps in keys (1, 3 instead of 1, 2) - NOT sequence-like
    let mut fb4 = FuncBuilder::new();
    fb4.insert(Value::int(1), Value::int(15));
    fb4.insert(Value::int(3), Value::int(16));
    let func4 = Value::Func(Arc::new(fb4.build()));
    assert!(func4.to_tuple_like_elements().is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_values() {
    let r = Value::record([("x", Value::int(1)), ("y", Value::int(2))]);
    let rec = r.as_record().unwrap();
    assert_eq!(rec.len(), 2);
    assert_eq!(rec.get(&Arc::from("x")), Some(&Value::int(1)));
    assert_eq!(rec.get(&Arc::from("y")), Some(&Value::int(2)));
    assert_eq!(rec.get(&Arc::from("z")), None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_values() {
    let mut fb = FuncBuilder::new();
    fb.insert(Value::int(1), Value::string("a"));
    fb.insert(Value::int(2), Value::string("b"));
    let f = Value::Func(Arc::new(fb.build()));
    let func = f.as_func().unwrap();
    assert_eq!(func.apply(&Value::int(1)), Some(&Value::string("a")));
    assert_eq!(func.apply(&Value::int(2)), Some(&Value::string("b")));
    assert_eq!(func.apply(&Value::int(3)), None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_ordering() {
    // Different types ordered by type
    assert!(Value::bool(true) < Value::int(0));
    assert!(Value::int(0) < Value::string(""));

    // Same type ordered by value
    assert!(Value::int(1) < Value::int(2));
    assert!(Value::string("a") < Value::string("b"));
}
