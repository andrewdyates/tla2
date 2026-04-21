// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::{FuncBuilder, IntIntervalFunc, Value};
use std::cmp::Ordering;
use std::sync::Arc;

// === Ord/Eq consistency ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_consistency_eq_implies_equal_cmp() {
    // For all pairs: (a == b) iff (a.cmp(b) == Equal)
    let values = vec![
        Value::bool(true),
        Value::bool(false),
        Value::int(0),
        Value::int(42),
        Value::string(""),
        Value::string("abc"),
        Value::set([Value::int(1)]),
        Value::tuple([Value::int(1)]),
    ];

    for a in &values {
        for b in &values {
            let eq_result = a == b;
            let cmp_result = a.cmp(b) == Ordering::Equal;
            assert_eq!(
                eq_result,
                cmp_result,
                "Ord/Eq inconsistency: {:?} == {:?} is {}, cmp is {:?}",
                a,
                b,
                eq_result,
                a.cmp(b)
            );
        }
    }
}

// === Antisymmetry ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_antisymmetry() {
    // if a < b then b > a
    let pairs: Vec<(Value, Value)> = vec![
        (Value::bool(false), Value::bool(true)),
        (Value::int(1), Value::int(2)),
        (Value::string("a"), Value::string("b")),
    ];

    for (a, b) in &pairs {
        assert_eq!(a.cmp(b), Ordering::Less, "Expected {a:?} < {b:?}");
        assert_eq!(b.cmp(a), Ordering::Greater, "Expected {b:?} > {a:?}");
    }
}

// === Ord/Eq consistency for cross-type pairs ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_consistency_cross_type_func_pairs() {
    // Build equivalent representations and verify Ord/Eq consistency
    let tuple = Value::tuple([Value::int(1), Value::int(2)]);
    let seq = Value::seq([Value::int(1), Value::int(2)]);
    let intfunc = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![Value::int(1), Value::int(2)],
    )));
    let mut fb = FuncBuilder::new();
    fb.insert(Value::int(1), Value::int(1));
    fb.insert(Value::int(2), Value::int(2));
    let func = Value::Func(Arc::new(fb.build()));

    let all = [&tuple, &seq, &intfunc, &func];
    for a in &all {
        for b in &all {
            let eq_result = *a == *b;
            let cmp_result = a.cmp(b) == Ordering::Equal;
            assert_eq!(
                eq_result,
                cmp_result,
                "Ord/Eq inconsistency: {:?} == {:?}: eq={}, cmp={:?}",
                a,
                b,
                eq_result,
                a.cmp(b)
            );
            // All four should be equal
            assert!(eq_result, "{a:?} and {b:?} should be equal");
        }
    }
}
