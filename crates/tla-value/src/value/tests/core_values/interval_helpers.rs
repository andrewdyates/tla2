// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Interval and range helper tests.
//!
//! Covers: range_set construction, IntervalValue iteration parity, empty ranges,
//! checked_interval_len, and IntIntervalFunc::new invariants.

use super::super::super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_set() {
    let r = range_set(&BigInt::from(1), &BigInt::from(3));
    // range_set now returns Value::Interval (lazy), so use to_sorted_set()
    let set = r.to_sorted_set().unwrap();
    assert_eq!(set.len(), 3);
    assert!(set.contains(&Value::int(1)));
    assert!(set.contains(&Value::int(2)));
    assert!(set.contains(&Value::int(3)));

    // Singleton interval
    let singleton = range_set(&BigInt::from(1), &BigInt::from(1));
    let singleton_set = singleton.to_sorted_set().unwrap();
    assert_eq!(singleton_set.len(), 1);
    assert!(singleton_set.contains(&Value::int(1)));

    // Interval starting at 0
    let zero_start = range_set(&BigInt::from(0), &BigInt::from(2));
    let zero_start_set = zero_start.to_sorted_set().unwrap();
    assert_eq!(zero_start_set.len(), 3);
    assert!(zero_start_set.contains(&Value::int(0)));
    assert!(zero_start_set.contains(&Value::int(1)));
    assert!(zero_start_set.contains(&Value::int(2)));

    // Negative interval
    let negative = range_set(&BigInt::from(-2), &BigInt::from(0));
    let negative_set = negative.to_sorted_set().unwrap();
    assert_eq!(negative_set.len(), 3);
    assert!(negative_set.contains(&Value::int(-2)));
    assert!(negative_set.contains(&Value::int(-1)));
    assert!(negative_set.contains(&Value::int(0)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interval_sorted_set_matches_interval_iteration_contents() {
    let interval = IntervalValue::new(BigInt::from(-2), BigInt::from(2));
    let sorted_values: Vec<Value> = interval.to_sorted_set().iter().cloned().collect();
    let legacy_values: Vec<Value> = interval.iter_values().collect();

    assert_eq!(sorted_values, legacy_values);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_empty_range() {
    let r = range_set(&BigInt::from(5), &BigInt::from(3));
    let set = r.as_set().unwrap();
    assert!(set.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checked_interval_len() {
    // Normal cases
    assert_eq!(checked_interval_len(1, 3), Some(3));
    assert_eq!(checked_interval_len(5, 5), Some(1));
    assert_eq!(checked_interval_len(0, 9), Some(10));

    // Inverted intervals (max < min) are empty
    assert_eq!(checked_interval_len(2, 1), Some(0));
    assert_eq!(checked_interval_len(100, 0), Some(0));
    assert_eq!(checked_interval_len(i64::MAX, i64::MIN), Some(0));

    // Overflow: i64::MAX - 0 + 1 overflows i64
    assert_eq!(checked_interval_len(0, i64::MAX), None);

    // Full range: i64::MAX - i64::MIN overflows i64
    assert_eq!(checked_interval_len(i64::MIN, i64::MAX), None);

    // Negative intervals
    assert_eq!(checked_interval_len(-5, -3), Some(3));
    assert_eq!(checked_interval_len(-1, 1), Some(3));

    // Zero-based
    assert_eq!(checked_interval_len(0, 0), Some(1));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_interval_func_new_normal() {
    let func = crate::value::IntIntervalFunc::new(
        3,
        5,
        vec![Value::int(10), Value::int(20), Value::int(30)],
    );
    assert_eq!(func.apply(&Value::int(3)), Some(&Value::int(10)));
    assert_eq!(func.apply(&Value::int(5)), Some(&Value::int(30)));
    assert_eq!(func.apply(&Value::int(6)), None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
#[should_panic(expected = "must equal interval length")]
fn test_int_interval_func_new_length_mismatch_panics() {
    // min=i64::MAX-2, max=i64::MAX: interval length = 3, but we provide 5 values
    crate::value::IntIntervalFunc::new(
        i64::MAX - 2,
        i64::MAX,
        vec![
            Value::int(1),
            Value::int(2),
            Value::int(3),
            Value::int(4),
            Value::int(5),
        ],
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_interval_func_new_empty() {
    // Canonical empty interval: min=1, max=0
    let func = crate::value::IntIntervalFunc::new(1, 0, vec![]);
    // Empty function: no domain element should resolve.
    assert_eq!(func.apply(&Value::int(42)), None);
    assert_eq!(func.apply(&Value::int(0)), None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
#[should_panic(expected = "must equal interval length")]
fn test_int_interval_func_new_invalid_bounds() {
    // min > max with non-empty values should panic in release mode too (assert, not debug_assert).
    crate::value::IntIntervalFunc::new(5, 3, vec![Value::int(1)]);
}
