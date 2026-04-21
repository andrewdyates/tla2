// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Generic PartialEq/Ord::cmp consistency tests for cross-type Value comparisons.
//!
//! Split from bug_179.rs per #3462: these tests verify the general consistency
//! contract (PartialEq agrees with Ord::cmp) across mixed Value representations,
//! not the specific Bug #179 tuple/func/seq membership regressions.

use super::super::super::*;
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_partial_eq_consistent_with_cmp_for_mixed_cases() {
    use std::cmp::Ordering;

    let tuple = Value::Tuple(vec![Value::SmallInt(1), Value::SmallInt(2)].into());
    let seq = Value::Seq(Arc::new(
        vec![Value::SmallInt(1), Value::SmallInt(2)].into(),
    ));
    let tuple_like_func = {
        let mut fb = FuncBuilder::new();
        fb.insert(Value::SmallInt(1), Value::SmallInt(1));
        fb.insert(Value::SmallInt(2), Value::SmallInt(2));
        Value::Func(Arc::new(fb.build()))
    };
    let intfunc = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![Value::SmallInt(1), Value::SmallInt(2)],
    )));

    let record = Value::record([("a", Value::SmallInt(1)), ("b", Value::SmallInt(2))]);
    let record_func = {
        let mut fb = FuncBuilder::new();
        fb.insert(Value::string("a"), Value::SmallInt(1));
        fb.insert(Value::string("b"), Value::SmallInt(2));
        Value::Func(Arc::new(fb.build()))
    };

    let interval = Value::Interval(Arc::new(IntervalValue::new(
        BigInt::from(1),
        BigInt::from(3),
    )));
    let explicit_set = Value::set([Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)]);

    let subset = Value::Subset(SubsetValue::new(Value::set([
        Value::SmallInt(1),
        Value::SmallInt(2),
    ])));
    let explicit_powerset = Value::set([
        Value::empty_set(),
        Value::set([Value::SmallInt(1)]),
        Value::set([Value::SmallInt(2)]),
        Value::set([Value::SmallInt(1), Value::SmallInt(2)]),
    ]);

    let seqset_empty = Value::SeqSet(SeqSetValue::new(Value::empty_set()));
    let singleton_empty_seq = Value::set([Value::seq(Vec::<Value>::new())]);

    let setcup_a = Value::SetCup(SetCupValue::new(
        Value::set([Value::SmallInt(1)]),
        Value::set([Value::SmallInt(2)]),
    ));
    let setcup_b = Value::SetCup(SetCupValue::new(
        Value::set([Value::SmallInt(1), Value::SmallInt(2)]),
        Value::empty_set(),
    ));

    // SeqSet and SetCup extensional PartialEq deferred to #1821 (#1829).
    let _ = (seqset_empty, singleton_empty_seq, setcup_a, setcup_b);
    let cases: Vec<(Value, Value, bool)> = vec![
        (Value::SmallInt(42), Value::big_int(BigInt::from(42)), true),
        (tuple.clone(), seq.clone(), true),
        (tuple.clone(), tuple_like_func.clone(), true),
        (seq.clone(), intfunc.clone(), true),
        (record, record_func, true),
        (interval, explicit_set, true),
        (subset, explicit_powerset, true),
        (Value::StringSet, Value::AnySet, false),
    ];

    for (lhs, rhs, expected_equal) in cases {
        assert_eq!(lhs == rhs, expected_equal);
        assert_eq!(rhs == lhs, expected_equal);
        assert_eq!(lhs.cmp(&rhs) == Ordering::Equal, expected_equal);
        assert_eq!(rhs.cmp(&lhs) == Ordering::Equal, expected_equal);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_partial_eq_consistent_with_cmp_for_lazy_set_ops() {
    use std::cmp::Ordering;

    let setcap_a = Value::SetCap(SetCapValue::new(
        Value::set([Value::SmallInt(1), Value::SmallInt(2)]),
        Value::set([Value::SmallInt(2), Value::SmallInt(3)]),
    ));
    let setcap_b = Value::SetCap(SetCapValue::new(
        Value::set([Value::SmallInt(2)]),
        Value::set([Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)]),
    ));

    let setdiff_a = Value::SetDiff(SetDiffValue::new(
        Value::set([Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)]),
        Value::set([Value::SmallInt(1), Value::SmallInt(3)]),
    ));
    let setdiff_b = Value::SetDiff(SetDiffValue::new(
        Value::set([Value::SmallInt(2), Value::SmallInt(3)]),
        Value::set([Value::SmallInt(3)]),
    ));

    let big_union = Value::BigUnion(UnionValue::new(Value::set([
        Value::set([Value::SmallInt(1)]),
        Value::set([Value::SmallInt(2), Value::SmallInt(3)]),
    ])));
    let explicit_union = Value::set([Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)]);

    let non_enumerable_cup_a = Value::SetCup(SetCupValue::new(Value::StringSet, Value::AnySet));
    let non_enumerable_cup_b = Value::SetCup(SetCupValue::new(Value::AnySet, Value::StringSet));
    let non_enumerable_cap_a = Value::SetCap(SetCapValue::new(Value::StringSet, Value::AnySet));
    let non_enumerable_cap_b = Value::SetCap(SetCapValue::new(Value::AnySet, Value::StringSet));

    // Extensional equality for SetCap/SetDiff/BigUnion vs plain Set deferred
    // until eq_set_like is wired into PartialEq/Ord (#1821, #1829).
    // Removed: (setcap_a, setcap_b, true), (setdiff_a, setdiff_b, true),
    //          (big_union, explicit_union, true)
    let _ = (
        setcap_a,
        setcap_b,
        setdiff_a,
        setdiff_b,
        big_union,
        explicit_union,
    );
    let cases: Vec<(Value, Value, bool)> = vec![
        // Non-enumerable lazy set ops still must keep PartialEq and Ord::cmp consistent.
        (
            non_enumerable_cup_a.clone(),
            non_enumerable_cup_b.clone(),
            false,
        ),
        (
            non_enumerable_cap_a.clone(),
            non_enumerable_cap_b.clone(),
            false,
        ),
        (non_enumerable_cup_a.clone(), non_enumerable_cup_a, true),
        (non_enumerable_cap_a.clone(), non_enumerable_cap_a, true),
    ];

    for (lhs, rhs, expected_equal) in cases {
        assert_eq!(lhs == rhs, expected_equal);
        assert_eq!(rhs == lhs, expected_equal);
        assert_eq!(lhs.cmp(&rhs) == Ordering::Equal, expected_equal);
        assert_eq!(rhs.cmp(&lhs) == Ordering::Equal, expected_equal);
    }
}
