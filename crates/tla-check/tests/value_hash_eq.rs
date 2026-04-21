// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use tla_check::{FuncSetValue, SubsetValue, Value};
use tla_value::{RecordSetValue, TupleSetValue};

fn hash64(v: &Value) -> u64 {
    let mut h = DefaultHasher::new();
    v.hash(&mut h);
    h.finish()
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn non_enumerable_set_like_hash_does_not_collapse_to_empty_set() {
    // Regression for #777: non-enumerable set-like values must contribute structural data to Hash,
    // otherwise they collapse to the same hash stream as {}.

    let empty = Value::empty_set();
    let empty_hash = hash64(&empty);

    let nat = Value::ModelValue(Arc::from("Nat"));

    let subset_nat = Value::Subset(SubsetValue::new(nat.clone()));
    assert_ne!(hash64(&subset_nat), empty_hash);

    let funcset_nat_nat = Value::FuncSet(FuncSetValue::new(nat.clone(), nat.clone()));
    assert_ne!(hash64(&funcset_nat_nat), empty_hash);

    let recordset_nat = Value::RecordSet(Arc::new(RecordSetValue::new([(
        Arc::from("a"),
        nat.clone(),
    )])));
    assert_ne!(hash64(&recordset_nat), empty_hash);

    let tupleset_nat_nat = Value::TupleSet(Arc::new(TupleSetValue::new([nat.clone(), nat])));
    assert_ne!(hash64(&tupleset_nat_nat), empty_hash);
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn empty_recordset_hash_matches_empty_set() {
    // Hash/Eq consistency: empty record sets compare equal to {} and must hash the same.
    let empty = Value::empty_set();
    let recordset_empty = Value::RecordSet(Arc::new(RecordSetValue::new([(
        Arc::from("a"),
        Value::empty_set(),
    )])));
    assert_eq!(hash64(&recordset_empty), hash64(&empty));
}
