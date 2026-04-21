// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Focused proof coverage for FuncValue domain helpers and FuncSet membership.
//!
//! Split from `set_ops_tests.rs` after the function-domain coverage for `#3073`
//! pushed that file past the size limit.

use super::super::*;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_manual_func_domain_eq_sorted_set_matches_expected_domain() {
    let func = FuncValue::from_sorted_entries(vec![
        (Value::int(1), Value::string("a")),
        (Value::int(3), Value::string("b")),
    ]);
    let expected = Value::set([Value::int(1), Value::int(3)])
        .to_sorted_set()
        .expect("set literal should be a sorted set");
    let wrong = Value::set([Value::int(1), Value::int(2)])
        .to_sorted_set()
        .expect("set literal should be a sorted set");

    assert!(func.domain_eq_sorted_set(&expected));
    assert!(!func.domain_eq_sorted_set(&wrong));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_funcset_contains_manual_func_matches_domain_and_range() {
    let func_set = FuncSetValue::new(
        Value::set([Value::int(1), Value::int(3)]),
        Value::set([Value::string("a"), Value::string("b")]),
    );

    let func = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (Value::int(1), Value::string("a")),
        (Value::int(3), Value::string("b")),
    ])));
    assert_eq!(
        func_set.contains(&func),
        Some(true),
        "manual Func should match [{{1,3}} -> {{\"a\",\"b\"}}]"
    );

    let wrong_domain = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (Value::int(1), Value::string("a")),
        (Value::int(2), Value::string("b")),
    ])));
    assert_eq!(func_set.contains(&wrong_domain), Some(false));

    let wrong_range = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (Value::int(1), Value::string("a")),
        (Value::int(3), Value::string("c")),
    ])));
    assert_eq!(func_set.contains(&wrong_range), Some(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_domain_is_sequence_accepts_only_one_based_contiguous_domains() {
    let seq_domain = FuncValue::from_sorted_entries(vec![
        (Value::int(1), Value::string("a")),
        (Value::int(2), Value::string("b")),
        (Value::int(3), Value::string("c")),
    ]);
    let shifted_domain = FuncValue::from_sorted_entries(vec![
        (Value::int(2), Value::string("a")),
        (Value::int(3), Value::string("b")),
    ]);
    let gapped_domain = FuncValue::from_sorted_entries(vec![
        (Value::int(1), Value::string("a")),
        (Value::int(3), Value::string("b")),
    ]);

    assert!(seq_domain.domain_is_sequence());
    assert!(!shifted_domain.domain_is_sequence());
    assert!(!gapped_domain.domain_is_sequence());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_funcset_contains_tuple_seq_and_intfunc_on_interval_domain() {
    let func_set = FuncSetValue::new(
        Value::Interval(Arc::new(IntervalValue::new(1.into(), 2.into()))),
        Value::set([Value::string("a"), Value::string("b")]),
    );

    let tuple = Value::tuple([Value::string("a"), Value::string("b")]);
    assert_eq!(
        func_set.contains(&tuple),
        Some(true),
        "tuple should match [1..2 -> {{\"a\",\"b\"}}]"
    );

    let seq = Value::seq([Value::string("a"), Value::string("b")]);
    assert_eq!(func_set.contains(&seq), Some(true));

    let intfunc = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![Value::string("a"), Value::string("b")],
    )));
    assert_eq!(func_set.contains(&intfunc), Some(true));

    let shifted_intfunc = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        2,
        3,
        vec![Value::string("a"), Value::string("b")],
    )));
    assert_eq!(func_set.contains(&shifted_intfunc), Some(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_interval_domain_helpers_match_tla_sequence_and_integer_domains() {
    let seq_domain = Value::Interval(Arc::new(IntervalValue::new(1.into(), 3.into())));
    assert!(seq_domain.is_sequence_domain(3));
    assert!(!seq_domain.is_sequence_domain(2));
    assert!(!seq_domain.is_sequence_domain(4));

    let shifted_domain = Value::Interval(Arc::new(IntervalValue::new(2.into(), 4.into())));
    assert!(!shifted_domain.is_sequence_domain(3));

    let int_domain = Value::Interval(Arc::new(IntervalValue::new((-2).into(), 1.into())));
    assert!(int_domain.is_integer_interval(-2, 1));
    assert!(!int_domain.is_integer_interval(-1, 1));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_interval_sequence_domain_rejects_lengths_beyond_i64() {
    let max_i64_len_domain =
        Value::Interval(Arc::new(IntervalValue::new(1.into(), i64::MAX.into())));
    assert!(max_i64_len_domain.is_sequence_domain(i64::MAX as usize));
    assert!(!max_i64_len_domain.is_sequence_domain((i64::MAX as usize) + 1));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_funcset_to_sorted_set_preserves_small_extensional_hash_and_order() {
    fn hash_value(value: &Value) -> u64 {
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    let func_set = FuncSetValue::new(
        Value::Interval(Arc::new(IntervalValue::new(1.into(), 2.into()))),
        Value::set([Value::string("a"), Value::string("b")]),
    );
    let materialized = func_set
        .to_sorted_set()
        .expect("small func set should materialize");
    let extensional = Value::Set(materialized.clone().into());
    let lazy = Value::FuncSet(func_set);

    let expected = Value::set([
        Value::seq([Value::string("a"), Value::string("a")]),
        Value::seq([Value::string("a"), Value::string("b")]),
        Value::seq([Value::string("b"), Value::string("a")]),
        Value::seq([Value::string("b"), Value::string("b")]),
    ])
    .to_sorted_set()
    .expect("expected function set should materialize");

    assert_eq!(materialized, expected);
    assert_eq!(lazy, extensional);
    assert_eq!(lazy.cmp(&extensional), std::cmp::Ordering::Equal);
    assert_eq!(hash_value(&lazy), hash_value(&extensional));
}
