// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FuncSet iterator semantics tests.

use super::super::super::*;
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_funcset_iterator_produces_seq_for_domain_1_n() {
    // FuncSetIterator should produce Seq values when domain is 1..n
    // (because in TLA+, functions with domain 1..n are semantically sequences)
    use crate::value::{FuncSetValue, IntervalValue, SortedSet};

    // Create [1..4 -> {"A", "B"}]
    let domain = Value::Interval(Arc::new(IntervalValue::new(
        BigInt::from(1),
        BigInt::from(4),
    )));
    let codomain = Value::Set(Arc::new(SortedSet::from_iter(vec![
        Value::String("A".into()),
        Value::String("B".into()),
    ])));

    let func_set = FuncSetValue::new(domain, codomain);
    let mut all_elems: Vec<Value> = func_set
        .iter()
        .expect("should be able to iterate")
        .collect();

    // [1..4 -> {"A", "B"}] should have 2^4 = 16 elements
    assert_eq!(
        all_elems.len(),
        16,
        "Expected 2^4 = 16 functions from 1..4 -> {{A, B}}"
    );

    all_elems.sort();
    all_elems.dedup();
    assert_eq!(all_elems.len(), 16, "All functions should be distinct");

    let symbols = [Value::String("A".into()), Value::String("B".into())];
    let mut expected = Vec::new();
    for e1 in &symbols {
        for e2 in &symbols {
            for e3 in &symbols {
                for e4 in &symbols {
                    expected.push(Value::seq([e1.clone(), e2.clone(), e3.clone(), e4.clone()]));
                }
            }
        }
    }
    expected.sort();
    expected.dedup();
    assert_eq!(
        expected.len(),
        16,
        "Expected set should contain 16 unique sequences"
    );

    // Verify exact set equality, not just count/type checks.
    assert_eq!(
        all_elems, expected,
        "FuncSet iterator did not enumerate 1..n sequences exactly"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_funcset_iterator_produces_intfunc_for_non_one_start() {
    // FuncSetIterator should produce IntFunc when domain is NOT 1..n (e.g., 2..5)
    use crate::value::{FuncSetValue, IntervalValue, SortedSet};

    // Create [2..4 -> {"A", "B"}] - domain starts at 2, not 1
    let domain = Value::Interval(Arc::new(IntervalValue::new(
        BigInt::from(2),
        BigInt::from(4),
    )));
    let codomain = Value::Set(Arc::new(SortedSet::from_iter(vec![
        Value::String("A".into()),
        Value::String("B".into()),
    ])));

    let func_set = FuncSetValue::new(domain, codomain);
    let iter = func_set.iter().expect("should be able to iterate");

    // Check that all produced values are IntFunc (domain 2..n is NOT a sequence)
    let mut found_intfunc = false;
    for func in iter.take(5) {
        match func {
            Value::IntFunc(_) => found_intfunc = true,
            _ => panic!("FuncSetIterator produced unexpected type for domain 2..n: {func:?}",),
        }
    }

    assert!(
        found_intfunc,
        "FuncSetIterator should produce IntFunc for domain not starting at 1"
    );
}
