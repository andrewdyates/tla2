// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fingerprint parity tests for enumerable and non-enumerable lazy set variants.

use super::super::super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_extend_lazy_set_variants_match_materialized_set_when_enumerable() {
    let seed = 17_u64;
    let assert_matches_materialized = |v: Value| {
        let materialized = v
            .to_sorted_set()
            .expect("test setup must use enumerable lazy set variants");
        let eager = Value::Set(materialized.into());
        assert_eq!(
            v.fingerprint_extend(seed).unwrap(),
            eager.fingerprint_extend(seed).unwrap()
        );
    };

    assert_matches_materialized(Value::Subset(SubsetValue::new(Value::set([
        Value::int(1),
        Value::int(2),
    ]))));
    assert_matches_materialized(Value::SetCup(SetCupValue::new(
        Value::set([Value::int(1), Value::int(2)]),
        Value::set([Value::int(2), Value::int(3)]),
    )));
    assert_matches_materialized(Value::SetCap(SetCapValue::new(
        Value::set([Value::int(1), Value::int(2)]),
        Value::set([Value::int(2), Value::int(3)]),
    )));
    assert_matches_materialized(Value::SetDiff(SetDiffValue::new(
        Value::set([Value::int(1), Value::int(2)]),
        Value::set([Value::int(2)]),
    )));
    assert_matches_materialized(Value::KSubset(KSubsetValue::new(
        Value::set([Value::int(1), Value::int(2), Value::int(3)]),
        2,
    )));
    assert_matches_materialized(Value::BigUnion(UnionValue::new(Value::set([
        Value::set([Value::int(1)]),
        Value::set([Value::int(2), Value::int(3)]),
    ]))));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_extend_lazy_set_variants_use_structural_fallback_when_not_enumerable() {
    use crate::fingerprint::{fp64_extend_i32, fp64_extend_i64, value_tags::*};

    let seed = 29_u64;

    let subset = Value::Subset(SubsetValue::new(Value::StringSet));
    let subset_expected = {
        let fp = fp64_extend_i64(seed, SUBSETVALUE);
        Value::StringSet.fingerprint_extend(fp).unwrap()
    };
    assert_eq!(subset.fingerprint_extend(seed).unwrap(), subset_expected);

    let set1 = Value::StringSet;
    let set2 = Value::AnySet;
    let cup = Value::SetCup(SetCupValue::new(set1.clone(), set2.clone()));
    let cup_expected = {
        let fp = fp64_extend_i64(seed, SETCUPVALUE);
        let fp = set1.fingerprint_extend(fp).unwrap();
        set2.fingerprint_extend(fp).unwrap()
    };
    assert_eq!(cup.fingerprint_extend(seed).unwrap(), cup_expected);

    let set1 = Value::StringSet;
    let set2 = Value::AnySet;
    let cap = Value::SetCap(SetCapValue::new(set1.clone(), set2.clone()));
    let cap_expected = {
        let fp = fp64_extend_i64(seed, SETCAPVALUE);
        let fp = set1.fingerprint_extend(fp).unwrap();
        set2.fingerprint_extend(fp).unwrap()
    };
    assert_eq!(cap.fingerprint_extend(seed).unwrap(), cap_expected);

    let set1 = Value::StringSet;
    let set2 = Value::set([Value::int(1), Value::int(2)]);
    let diff = Value::SetDiff(SetDiffValue::new(set1.clone(), set2.clone()));
    let diff_expected = {
        let fp = fp64_extend_i64(seed, SETDIFFVALUE);
        let fp = set1.fingerprint_extend(fp).unwrap();
        set2.fingerprint_extend(fp).unwrap()
    };
    assert_eq!(diff.fingerprint_extend(seed).unwrap(), diff_expected);

    let base = Value::StringSet;
    let ksubset = Value::KSubset(KSubsetValue::new(base.clone(), 2));
    let ksubset_expected = {
        let fp = fp64_extend_i64(seed, SUBSETVALUE);
        let fp = base.fingerprint_extend(fp).unwrap();
        fp64_extend_i32(fp, 2)
    };
    assert_eq!(ksubset.fingerprint_extend(seed).unwrap(), ksubset_expected);

    let union_set = Value::StringSet;
    let big_union = Value::BigUnion(UnionValue::new(union_set.clone()));
    let big_union_expected = {
        let fp = fp64_extend_i64(seed, UNIONVALUE);
        union_set.fingerprint_extend(fp).unwrap()
    };
    assert_eq!(
        big_union.fingerprint_extend(seed).unwrap(),
        big_union_expected
    );
}
