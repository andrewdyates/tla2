// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Cross-type hash/equality equivalence tests.

use super::super::super::*;
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_func_hash_equivalence() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    fn hash_value(v: &Value) -> u64 {
        let mut hasher = DefaultHasher::new();
        v.hash(&mut hasher);
        hasher.finish()
    }

    // Record [a |-> 1, b |-> 2, c |-> 3]
    let rec = Value::record([
        ("a", Value::int(1)),
        ("b", Value::int(2)),
        ("c", Value::int(3)),
    ]);

    // Equivalent Func with domain {"a", "b", "c"}
    let mut fb = FuncBuilder::new();
    fb.insert(Value::string("a"), Value::int(1));
    fb.insert(Value::string("b"), Value::int(2));
    fb.insert(Value::string("c"), Value::int(3));
    let func = Value::Func(Arc::new(fb.build()));

    // They should be equal (same mathematical function)
    assert_eq!(rec, func, "Record and Func should be equal");

    // They should hash the same
    let rec_hash = hash_value(&rec);
    let func_hash = hash_value(&func);
    assert_eq!(rec_hash, func_hash, "Record and Func should hash the same");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_recordset_funcset_hash_equivalence() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    fn hash_value(v: &Value) -> u64 {
        let mut hasher = DefaultHasher::new();
        v.hash(&mut hasher);
        hasher.finish()
    }

    // RecordSet [a : {1,2}, b : {1,2}]
    let rsv = RecordSetValue::new([
        (Arc::from("a"), Value::set([Value::int(1), Value::int(2)])),
        (Arc::from("b"), Value::set([Value::int(1), Value::int(2)])),
    ]);
    let record_set = Value::RecordSet(rsv.clone().into());

    // Equivalent FuncSet [{"a","b"} -> {1,2}]
    let domain = Value::set([Value::string("a"), Value::string("b")]);
    let codomain = Value::set([Value::int(1), Value::int(2)]);
    let fsv = FuncSetValue::new(domain, codomain);
    let func_set = Value::FuncSet(fsv.clone());

    // They should be equal (same set of functions)
    assert_eq!(
        record_set, func_set,
        "RecordSet and FuncSet should be equal"
    );

    // They should hash the same
    let rsv_hash = hash_value(&record_set);
    let fsv_hash = hash_value(&func_set);
    assert_eq!(
        rsv_hash, fsv_hash,
        "RecordSet and FuncSet should hash the same"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_smallint_bigint_hash_equivalence() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    fn hash_value(v: &Value) -> u64 {
        let mut hasher = DefaultHasher::new();
        v.hash(&mut hasher);
        hasher.finish()
    }

    // Test that SmallInt and equivalent BigInt hash the same
    let test_values: &[i64] = &[
        0,
        1,
        -1,
        5,
        -5,
        127,
        128,
        255,
        256,
        1000,
        -1000,
        i64::MAX,
        i64::MIN,
    ];

    for &n in test_values {
        let small = Value::SmallInt(n);
        // Create a BigInt directly (bypassing normalization)
        let big = Value::Int(Arc::new(BigInt::from(n)));

        // They should be equal
        assert_eq!(small, big, "SmallInt({n}) should equal Int(BigInt({n}))",);

        // They should hash the same
        let small_hash = hash_value(&small);
        let big_hash = hash_value(&big);
        assert_eq!(
            small_hash, big_hash,
            "SmallInt({n}) and Int(BigInt({n})) should hash the same",
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_large_funcset_hash_uses_structural_guard() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    fn hash_value(v: &Value) -> u64 {
        let mut hasher = DefaultHasher::new();
        v.hash(&mut hasher);
        hasher.finish()
    }

    // |{0,1}|^25 = 33,554,432 (> 10k guard), so hashing must stay structural.
    let domain = Value::Interval(Arc::new(IntervalValue::new(
        BigInt::from(1),
        BigInt::from(25),
    )));
    let codomain = Value::set([Value::int(0), Value::int(1)]);
    let fs = Value::FuncSet(FuncSetValue::new(domain, codomain));

    // Regression: this should complete quickly and deterministically without eager expansion.
    let h1 = hash_value(&fs);
    let h2 = hash_value(&fs);
    assert_eq!(h1, h2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_large_funcset_cmp_uses_structural_guard() {
    let codomain = Value::set([Value::int(0), Value::int(1)]);
    let fs24 = Value::FuncSet(FuncSetValue::new(
        Value::Interval(Arc::new(IntervalValue::new(
            BigInt::from(1),
            BigInt::from(24),
        ))),
        codomain.clone(),
    ));
    let fs25 = Value::FuncSet(FuncSetValue::new(
        Value::Interval(Arc::new(IntervalValue::new(
            BigInt::from(1),
            BigInt::from(25),
        ))),
        codomain,
    ));

    // Regression: comparison should not force eager materialization for huge function sets.
    assert!(fs24 < fs25);
    assert_ne!(fs24, fs25);
}
