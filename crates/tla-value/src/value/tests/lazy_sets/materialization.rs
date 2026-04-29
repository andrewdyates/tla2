// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compound lazy set materialization tests (RecordSet, TupleSet, KSubset).

use super::super::super::*;
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_additional_lazy_sets_to_sorted_set_match_expected_contents() {
    let record_set = RecordSetValue::new([
        (Arc::from("a"), Value::set([Value::int(1), Value::int(2)])),
        (Arc::from("b"), Value::set([Value::string("x")])),
    ]);
    let record_expected = Value::set([
        Value::Record(RecordValue::from_sorted_str_entries(vec![
            (Arc::from("a"), Value::int(1)),
            (Arc::from("b"), Value::string("x")),
        ])),
        Value::Record(RecordValue::from_sorted_str_entries(vec![
            (Arc::from("a"), Value::int(2)),
            (Arc::from("b"), Value::string("x")),
        ])),
    ])
    .to_sorted_set()
    .expect("expected record set should materialize");
    assert_eq!(
        record_set
            .to_sorted_set()
            .expect("record set should materialize"),
        record_expected
    );

    let tuple_set = TupleSetValue::new([
        Value::set([Value::int(1), Value::int(2)]),
        Value::set([Value::string("x")]),
    ]);
    let tuple_expected = Value::set([
        Value::Tuple(vec![Value::int(1), Value::string("x")].into()),
        Value::Tuple(vec![Value::int(2), Value::string("x")].into()),
    ])
    .to_sorted_set()
    .expect("expected tuple set should materialize");
    assert_eq!(
        tuple_set
            .to_sorted_set()
            .expect("tuple set should materialize"),
        tuple_expected
    );

    let ksubset = KSubsetValue::new(Value::set([Value::int(1), Value::int(2), Value::int(3)]), 2);
    let ksubset_expected = Value::set([
        Value::set([Value::int(1), Value::int(2)]),
        Value::set([Value::int(1), Value::int(3)]),
        Value::set([Value::int(2), Value::int(3)]),
    ])
    .to_sorted_set()
    .expect("expected k-subset should materialize");
    assert_eq!(
        ksubset
            .to_sorted_set()
            .expect("k-subset should materialize"),
        ksubset_expected
    );
}
