// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::helpers::fnv_hash;
use super::*;
use crate::value::RecordValue;
use std::collections::hash_map::DefaultHasher;
use std::sync::Arc;
use tla_core::ast::{BoundVar, Expr};
use tla_core::kani_types::HashMap;
use tla_core::Spanned;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_array_state_hash_with_fp_cache() {
    let registry = VarRegistry::from_names(["x", "y"]);
    let mut state = ArrayState::new(2);
    state.set(VarIndex(0), Value::int(1));
    state.set(VarIndex(1), Value::int(2));

    let _fp = state.fingerprint(&registry);

    let mut hasher = DefaultHasher::new();
    state.hash(&mut hasher);
    let h1 = hasher.finish();

    let mut hasher2 = DefaultHasher::new();
    state.hash(&mut hasher2);
    assert_eq!(h1, hasher2.finish(), "Hash should be deterministic");

    let mut state2 = ArrayState::new(2);
    state2.set(VarIndex(0), Value::int(99));
    state2.set(VarIndex(1), Value::int(99));
    let _fp2 = state2.fingerprint(&registry);

    let mut hasher3 = DefaultHasher::new();
    state2.hash(&mut hasher3);
    let h2 = hasher3.finish();

    assert_ne!(
        h1, h2,
        "States with same-type but different values must hash differently"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
#[should_panic(expected = "fp_cache populated")]
fn test_array_state_hash_without_fp_cache_panics() {
    let mut state = ArrayState::new(2);
    state.set(VarIndex(0), Value::int(1));
    state.set(VarIndex(1), Value::int(2));

    let mut hasher = DefaultHasher::new();
    state.hash(&mut hasher);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_identity_consistent_across_fnv_hash_std_hash_and_fp64() {
    let bound = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: None,
        pattern: None,
    };

    let v1 = Value::SetPred(Box::new(SetPredValue::new(
        Value::StringSet,
        bound.clone(),
        Spanned::new(Expr::Bool(true), Default::default()),
        HashMap::new(),
        None,
        None,
    )));
    let v2 = Value::SetPred(Box::new(SetPredValue::new(
        Value::StringSet,
        bound.clone(),
        Spanned::new(Expr::Bool(true), Default::default()),
        HashMap::new(),
        None,
        None,
    )));
    let v3 = Value::SetPred(Box::new(SetPredValue::new(
        Value::StringSet,
        bound,
        Spanned::new(Expr::Bool(false), Default::default()),
        HashMap::new(),
        None,
        None,
    )));

    assert_eq!(fnv_hash(&v1), fnv_hash(&v2));
    assert_ne!(fnv_hash(&v1), fnv_hash(&v3));

    let mut h1 = DefaultHasher::new();
    let mut h2 = DefaultHasher::new();
    let mut h3 = DefaultHasher::new();
    v1.hash(&mut h1);
    v2.hash(&mut h2);
    v3.hash(&mut h3);
    assert_eq!(h1.finish(), h2.finish());
    assert_ne!(h1.finish(), h3.finish());

    let seed = 42;
    assert_eq!(
        v1.fingerprint_extend(seed).unwrap(),
        v2.fingerprint_extend(seed).unwrap(),
    );
    assert_ne!(
        v1.fingerprint_extend(seed).unwrap(),
        v3.fingerprint_extend(seed).unwrap(),
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nonenumerable_subset_different_bases_different_hashes() {
    let subset_string = Value::Subset(SubsetValue::new(Value::StringSet));
    let subset_finite = Value::Subset(SubsetValue::new(Value::set([
        Value::int(1),
        Value::int(2),
        Value::int(3),
    ])));

    let h1 = fnv_hash(&subset_string);
    let h2 = fnv_hash(&subset_finite);

    assert_ne!(
        h1, h2,
        "SUBSET(STRING) and SUBSET({{1,2,3}}) must hash differently"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nonenumerable_subset_structural_hash_is_deterministic() {
    let subset = Value::Subset(SubsetValue::new(Value::StringSet));
    assert_eq!(fnv_hash(&subset), fnv_hash(&subset));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nonenumerable_subset_different_infinite_bases() {
    let subset_string = Value::Subset(SubsetValue::new(Value::StringSet));
    let subset_any = Value::Subset(SubsetValue::new(Value::AnySet));

    let h1 = fnv_hash(&subset_string);
    let h2 = fnv_hash(&subset_any);
    assert_ne!(
        h1, h2,
        "SUBSET(STRING) and SUBSET(ANY) must hash differently"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nonenumerable_funcset_different_domains_different_hashes() {
    let fs1 = Value::FuncSet(FuncSetValue::new(
        Value::StringSet,
        Value::set([Value::int(1)]),
    ));
    let fs2 = Value::FuncSet(FuncSetValue::new(
        Value::set([Value::int(1)]),
        Value::set([Value::int(1)]),
    ));

    let h1 = fnv_hash(&fs1);
    let h2 = fnv_hash(&fs2);
    assert_ne!(
        h1, h2,
        "[STRING -> {{1}}] and [{{1}} -> {{1}}] must hash differently"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nonenumerable_funcset_different_codomains_different_hashes() {
    let fs1 = Value::FuncSet(FuncSetValue::new(
        Value::StringSet,
        Value::set([Value::int(1)]),
    ));
    let fs2 = Value::FuncSet(FuncSetValue::new(
        Value::StringSet,
        Value::set([Value::int(2)]),
    ));

    let h1 = fnv_hash(&fs1);
    let h2 = fnv_hash(&fs2);
    assert_ne!(
        h1, h2,
        "[STRING -> {{1}}] and [STRING -> {{2}}] must hash differently"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerable_lazy_sets_hash_like_equivalent_materialized_sets() {
    let funcset = Value::FuncSet(FuncSetValue::new(
        Value::Interval(Arc::new(IntervalValue::new(1.into(), 2.into()))),
        Value::set([Value::string("a"), Value::string("b")]),
    ));
    let funcset_expected = Value::set([
        Value::seq([Value::string("a"), Value::string("a")]),
        Value::seq([Value::string("a"), Value::string("b")]),
        Value::seq([Value::string("b"), Value::string("a")]),
        Value::seq([Value::string("b"), Value::string("b")]),
    ]);
    assert_eq!(fnv_hash(&funcset), fnv_hash(&funcset_expected));

    let recordset = Value::RecordSet(Arc::new(RecordSetValue::new([
        (Arc::from("a"), Value::set([Value::int(1), Value::int(2)])),
        (Arc::from("b"), Value::set([Value::string("x")])),
    ])));
    let recordset_expected = Value::set([
        Value::Record(RecordValue::from_sorted_str_entries(vec![
            (Arc::from("a"), Value::int(1)),
            (Arc::from("b"), Value::string("x")),
        ])),
        Value::Record(RecordValue::from_sorted_str_entries(vec![
            (Arc::from("a"), Value::int(2)),
            (Arc::from("b"), Value::string("x")),
        ])),
    ]);
    assert_eq!(fnv_hash(&recordset), fnv_hash(&recordset_expected));

    let tupleset = Value::TupleSet(Arc::new(TupleSetValue::new([
        Value::set([Value::int(1), Value::int(2)]),
        Value::set([Value::string("x")]),
    ])));
    let tupleset_expected = Value::set([
        Value::Tuple(vec![Value::int(1), Value::string("x")].into()),
        Value::Tuple(vec![Value::int(2), Value::string("x")].into()),
    ]);
    assert_eq!(fnv_hash(&tupleset), fnv_hash(&tupleset_expected));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nonenumerable_recordset_different_fields_different_hashes() {
    let rs1 = RecordSetValue::new([(Arc::from("a"), Value::StringSet)]);
    let rs2 = RecordSetValue::new([(Arc::from("b"), Value::StringSet)]);

    let h1 = fnv_hash(&Value::RecordSet(Arc::new(rs1)));
    let h2 = fnv_hash(&Value::RecordSet(Arc::new(rs2)));
    assert_ne!(h1, h2, "[a: STRING] and [b: STRING] must hash differently");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nonenumerable_recordset_different_domains_different_hashes() {
    let rs1 = RecordSetValue::new([(Arc::from("a"), Value::StringSet)]);
    let rs2 = RecordSetValue::new([(Arc::from("a"), Value::set([Value::int(1), Value::int(2)]))]);

    let h1 = fnv_hash(&Value::RecordSet(Arc::new(rs1)));
    let h2 = fnv_hash(&Value::RecordSet(Arc::new(rs2)));
    assert_ne!(h1, h2, "[a: STRING] and [a: {{1,2}}] must hash differently");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nonenumerable_tupleset_different_components_different_hashes() {
    let ts1 = TupleSetValue::new([Value::StringSet, Value::set([Value::int(1)])]);
    let ts2 = TupleSetValue::new([Value::set([Value::int(1)]), Value::StringSet]);

    let h1 = fnv_hash(&Value::TupleSet(Arc::new(ts1)));
    let h2 = fnv_hash(&Value::TupleSet(Arc::new(ts2)));
    assert_ne!(
        h1, h2,
        "STRING \\X {{1}} and {{1}} \\X STRING must hash differently"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nonenumerable_tupleset_different_arity_different_hashes() {
    let ts1 = TupleSetValue::new([Value::StringSet, Value::StringSet]);
    let ts2 = TupleSetValue::new([Value::StringSet, Value::StringSet, Value::StringSet]);

    let h1 = fnv_hash(&Value::TupleSet(Arc::new(ts1)));
    let h2 = fnv_hash(&Value::TupleSet(Arc::new(ts2)));
    assert_ne!(
        h1, h2,
        "STRING \\X STRING and STRING \\X STRING \\X STRING must hash differently"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interval_hash_bigint_bounds_small_length() {
    let big_low = BigInt::from(i64::MAX) + BigInt::from(1);
    let big_high_a = &big_low + BigInt::from(2);
    let big_high_b = &big_low + BigInt::from(5);

    let iv_a = IntervalValue::new(big_low.clone(), big_high_a);
    let iv_b = IntervalValue::new(big_low, big_high_b);

    let val_a = Value::Interval(Arc::new(iv_a));
    let val_b = Value::Interval(Arc::new(iv_b));

    let h_a = fnv_hash(&val_a);
    let h_b = fnv_hash(&val_b);

    assert_ne!(
        h_a, h_b,
        "BigInt-bounded intervals with different lengths must hash differently"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interval_length_bigint_byte_hash_distinct() {
    let len_a = BigInt::from(1u128 << 65) + BigInt::from(1);
    let len_b = BigInt::from(1u128 << 66) + BigInt::from(1);

    let hash_bigint_bytes = |len: &BigInt| -> u64 {
        let mut hash = FNV_OFFSET;
        for byte in len.to_signed_bytes_le() {
            hash ^= byte as u64;
            hash = hash.wrapping_mul(FNV_PRIME);
        }
        hash
    };

    let h_a = hash_bigint_bytes(&len_a);
    let h_b = hash_bigint_bytes(&len_b);

    assert_ne!(
        h_a, h_b,
        "BigInt lengths exceeding u64 must hash differently"
    );

    let truncated_a = len_a.to_u64().unwrap_or(0);
    let truncated_b = len_b.to_u64().unwrap_or(0);
    assert_eq!(
        truncated_a, truncated_b,
        "Sanity: both lengths should truncate to 0 via unwrap_or(0)"
    );
    assert_eq!(truncated_a, 0, "Sanity: truncated length should be 0");
}
