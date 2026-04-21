// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bug #179 regression suite: Tuple/Func/Seq cross-type equality and
//! FuncSet membership.
//!
//! Generic PartialEq/Ord::cmp consistency tests live in cmp_consistency.rs (#3462).

use super::super::super::*;
use std::sync::Arc;

/// Bug #179: Tuple should equal Func with same domain 1..n and same values
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_179_tuple_equals_func() {
    // Create tuple <<1, 1, 1, 1>>
    let tuple = Value::Tuple(
        vec![
            Value::SmallInt(1),
            Value::SmallInt(1),
            Value::SmallInt(1),
            Value::SmallInt(1),
        ]
        .into(),
    );

    // Create equivalent function [1 |-> 1, 2 |-> 1, 3 |-> 1, 4 |-> 1]
    let mut fb = FuncBuilder::new();
    fb.insert(Value::SmallInt(1), Value::SmallInt(1));
    fb.insert(Value::SmallInt(2), Value::SmallInt(1));
    fb.insert(Value::SmallInt(3), Value::SmallInt(1));
    fb.insert(Value::SmallInt(4), Value::SmallInt(1));
    let func = Value::Func(Arc::new(fb.build()));

    // They should be equal
    assert_eq!(
        tuple.cmp(&func),
        std::cmp::Ordering::Equal,
        "Tuple should equal equivalent Func"
    );
    assert_eq!(
        func.cmp(&tuple),
        std::cmp::Ordering::Equal,
        "Func should equal equivalent Tuple"
    );
    assert_eq!(tuple, func, "Tuple and Func should be PartialEq equal");

    // A set containing the func should find the tuple
    let set = SortedSet::from_iter(vec![func.clone()]);
    assert!(
        set.contains(&tuple),
        "SortedSet containing Func should find equivalent Tuple"
    );
    assert!(
        set.contains(&func),
        "SortedSet containing Func should find Func"
    );
}

/// Bug #179: ROOT CAUSE - func_set_eager produces Func but FuncSetIterator produces Seq
/// This inconsistency causes big_union (which uses to_ord_set -> func_set_eager)
/// to produce different Value types than what FuncSetIterator would produce.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_179_func_set_eager_vs_iterator_inconsistency() {
    // Create [1..4 -> {1, 2, 3}]
    let codomain = Value::set([Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)]);
    let fs4 = FuncSetValue::new(
        Value::Interval(Arc::new(IntervalValue::new(
            BigInt::from(1),
            BigInt::from(4),
        ))),
        codomain.clone(),
    );

    // Get elements via iterator (produces Seq for domain 1..n)
    let iter_elems: Vec<Value> = fs4.iter().unwrap().take(3).collect();
    eprintln!("FuncSetIterator produces:");
    for elem in &iter_elems {
        eprintln!("  {:?}", std::mem::discriminant(elem));
        assert!(
            matches!(elem, Value::Seq(_)),
            "FuncSetIterator should produce Seq for domain 1..n"
        );
    }

    // Get elements via to_sorted_set (production path — uses iterator, not func_set_eager)
    let sorted_set = fs4.to_sorted_set().unwrap();
    // Iterator produces Seq/IntFunc for integer domain 1..n (not Func)
    for elem in sorted_set.iter().take(3) {
        assert!(
            !matches!(elem, Value::Func(_)),
            "to_sorted_set should produce Seq/IntFunc values for integer domain, got {:?}",
            std::mem::discriminant(elem)
        );
    }

    // Verify that Seq needle membership works in the materialized set
    // (this was the original Bug #179 — binary search failed due to type mismatch)
    let needle = Value::Seq(Arc::new(
        vec![
            Value::SmallInt(1),
            Value::SmallInt(1),
            Value::SmallInt(1),
            Value::SmallInt(1),
        ]
        .into(),
    ));

    assert!(
        sorted_set.contains(&needle),
        "Seq needle should be found in materialized FuncSet (Bug #179 regression)"
    );
}

/// Bug #179: CRITICAL - Test FuncSet membership with Tuple needle (cross-type search)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_179_tuple_in_func_set() {
    // Tuple <<1,1,1,1>> must be found in [1..4 -> {1,2,3}] via to_sorted_set().
    // Original bug: binary search failed when Tuple vs Func comparison was inconsistent.

    // Create the function set
    let codomain = Value::set([Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)]);
    let fs4 = FuncSetValue::new(
        Value::Interval(Arc::new(IntervalValue::new(
            BigInt::from(1),
            BigInt::from(4),
        ))),
        codomain.clone(),
    );

    // Materialize via to_sorted_set (production path)
    let sorted_set = fs4.to_sorted_set().expect("fs4 should be enumerable");
    eprintln!("to_sorted_set produced {} elements", sorted_set.len());

    // Create the needle as a Tuple (what TLA <<1,1,1,1>> produces)
    let tuple_needle = Value::Tuple(
        vec![
            Value::SmallInt(1),
            Value::SmallInt(1),
            Value::SmallInt(1),
            Value::SmallInt(1),
        ]
        .into(),
    );

    // Cross-type membership: Tuple needle in set of Seq/IntFunc values
    let found = sorted_set.contains(&tuple_needle);

    assert!(
        found,
        "Tuple should be found in FuncSet containing equivalent Seq/IntFunc values (Bug #179 regression)"
    );
}

/// Bug #179: UNION of FuncSets should find tuple membership
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_179_union_funcset_membership() {
    // Create [1..n -> {1, 2, 3}] for n = 1, 2, 3, 4
    let codomain = Value::set([Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)]);

    let fs1 = Value::FuncSet(FuncSetValue::new(
        Value::Interval(Arc::new(IntervalValue::new(
            BigInt::from(1),
            BigInt::from(1),
        ))),
        codomain.clone(),
    ));
    let fs2 = Value::FuncSet(FuncSetValue::new(
        Value::Interval(Arc::new(IntervalValue::new(
            BigInt::from(1),
            BigInt::from(2),
        ))),
        codomain.clone(),
    ));
    let fs3 = Value::FuncSet(FuncSetValue::new(
        Value::Interval(Arc::new(IntervalValue::new(
            BigInt::from(1),
            BigInt::from(3),
        ))),
        codomain.clone(),
    ));
    let fs4 = Value::FuncSet(FuncSetValue::new(
        Value::Interval(Arc::new(IntervalValue::new(
            BigInt::from(1),
            BigInt::from(4),
        ))),
        codomain.clone(),
    ));

    // Create tuple <<1, 1, 1, 1>>
    let tuple = Value::Tuple(
        vec![
            Value::SmallInt(1),
            Value::SmallInt(1),
            Value::SmallInt(1),
            Value::SmallInt(1),
        ]
        .into(),
    );

    // Direct membership should work
    assert!(
        fs4.set_contains(&tuple).unwrap(),
        "Tuple should be in [1..4 -> S]"
    );
    assert!(
        !fs3.set_contains(&tuple).unwrap(),
        "Tuple should NOT be in [1..3 -> S]"
    );
    assert!(
        !fs2.set_contains(&tuple).unwrap(),
        "Tuple should NOT be in [1..2 -> S]"
    );
    assert!(
        !fs1.set_contains(&tuple).unwrap(),
        "Tuple should NOT be in [1..1 -> S]"
    );

    // Set with 2 funcsets
    let funcsets2 = Value::set([fs3.clone(), fs4.clone()]);
    let union2 = UnionValue::new(funcsets2);
    assert!(
        union2.contains(&tuple).unwrap(),
        "Tuple should be in UNION {{FS3, FS4}}"
    );

    // Set with 3 funcsets
    let funcsets3 = Value::set([fs2.clone(), fs3.clone(), fs4.clone()]);
    let union3 = UnionValue::new(funcsets3);
    assert!(
        union3.contains(&tuple).unwrap(),
        "Tuple should be in UNION {{FS2, FS3, FS4}}"
    );

    // Set with all 4 funcsets - this is the bug case!
    let funcsets4 = Value::set([fs1.clone(), fs2.clone(), fs3.clone(), fs4.clone()]);
    let union4 = UnionValue::new(funcsets4);
    assert!(
        union4.contains(&tuple).unwrap(),
        "Tuple should be in UNION {{FS1, FS2, FS3, FS4}}"
    );
}

/// Bug #179: Test the EAGER big_union path (this is what eval uses)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_179_eager_big_union() {
    use num_bigint::BigInt;

    // Create [1..n -> {1, 2, 3}] for n = 1, 2, 3, 4
    let codomain = Value::set([Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)]);

    let fs1 = Value::FuncSet(FuncSetValue::new(
        Value::Interval(Arc::new(IntervalValue::new(
            BigInt::from(1),
            BigInt::from(1),
        ))),
        codomain.clone(),
    ));
    let fs4 = Value::FuncSet(FuncSetValue::new(
        Value::Interval(Arc::new(IntervalValue::new(
            BigInt::from(1),
            BigInt::from(4),
        ))),
        codomain.clone(),
    ));

    // Create the outer set containing funcsets
    let funcsets = Value::set([fs1, fs4]);
    let outer_set = funcsets.to_sorted_set().unwrap();

    // Use big_union (the eager path that eval uses)
    let union_result = big_union(&outer_set).expect("big_union should succeed");

    // Now check if tuple is in this union
    let tuple = Value::Tuple(
        vec![
            Value::SmallInt(1),
            Value::SmallInt(1),
            Value::SmallInt(1),
            Value::SmallInt(1),
        ]
        .into(),
    );

    let contains = union_result.set_contains(&tuple).unwrap();
    assert!(
        contains,
        "Tuple <<1,1,1,1>> should be in big_union of FuncSets"
    );
}

/// Bug #179: Test Tuple vs Seq equality and SortedSet lookup
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_179_tuple_vs_seq_sorted_set() {
    // Create Seq (what FuncSetIterator produces)
    let seq = Value::Seq(Arc::new(
        vec![
            Value::SmallInt(1),
            Value::SmallInt(1),
            Value::SmallInt(1),
            Value::SmallInt(1),
        ]
        .into(),
    ));

    // Create Tuple (what <<1,1,1,1>> evaluates to)
    let tuple = Value::Tuple(
        vec![
            Value::SmallInt(1),
            Value::SmallInt(1),
            Value::SmallInt(1),
            Value::SmallInt(1),
        ]
        .into(),
    );

    // Direct comparison
    assert_eq!(
        tuple.cmp(&seq),
        std::cmp::Ordering::Equal,
        "Tuple and Seq with same elements should be Equal"
    );

    // SortedSet containing Seq should find Tuple
    let set_with_seq = SortedSet::from_iter(vec![seq.clone()]);
    assert!(
        set_with_seq.contains(&seq),
        "Set containing Seq should find Seq"
    );
    assert!(
        set_with_seq.contains(&tuple),
        "Set containing Seq should find equivalent Tuple"
    );

    // SortedSet containing Tuple should find Seq
    let set_with_tuple = SortedSet::from_iter(vec![tuple.clone()]);
    assert!(
        set_with_tuple.contains(&tuple),
        "Set containing Tuple should find Tuple"
    );
    assert!(
        set_with_tuple.contains(&seq),
        "Set containing Tuple should find equivalent Seq"
    );
}
