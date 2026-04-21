// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lazy-set Hash/Eq contract coverage from #2065 and special-set hashing checks.
//!
//! Regression: eq_set_like_extensional must respect should_materialize_extensionally
//! budget gate, matching Hash. Without the gate, PartialEq could find two large
//! lazy sets equal extensionally while Hash falls back to structural hashing,
//! violating a == b => hash(a) == hash(b).

use super::super::super::*;
use super::hash_value;

// === Hash/Eq contract for lazy sets (#2065) ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_eq_contract_subset_within_budget() {
    // SUBSET({1,2,3}) has 2^3 = 8 elements, well within MAX_SET_MATERIALIZE
    let base = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
    let subset = Value::Subset(SubsetValue::new(base));

    // Materialize to a concrete Set for comparison
    let concrete: Vec<Value> = subset.iter_set().unwrap().collect();
    let concrete_set = Value::set(concrete);

    // Both should be equal (extensional)
    assert_eq!(
        subset, concrete_set,
        "small Subset should equal its materialization"
    );
    // Hash/Eq contract: equal values must have equal hashes
    assert_eq!(
        hash_value(&subset),
        hash_value(&concrete_set),
        "Hash/Eq violation: SUBSET({{1,2,3}}) and its materialization have different hashes"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_eq_contract_subset_above_budget_consistent() {
    // SUBSET({1..14}) has 2^14 = 16384 elements, above MAX_SET_MATERIALIZE (10000).
    // Both Hash and PartialEq should use structural comparison for this variant,
    // so the same Subset must always hash consistently with itself.
    let base = Value::set((1..=14).map(Value::int));
    let subset = Value::Subset(SubsetValue::new(base));

    // Self-equality must hold
    assert_eq!(subset, subset.clone(), "Subset must equal its clone");
    // Hash consistency
    assert_eq!(
        hash_value(&subset),
        hash_value(&subset.clone()),
        "large Subset hash must be stable across clones"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_eq_contract_small_setcup_matches_materialized_set() {
    let cup = Value::SetCup(SetCupValue::new(
        Value::set([Value::int(1)]),
        Value::set([Value::int(2)]),
    ));
    let concrete = Value::set([Value::int(1), Value::int(2)]);

    assert_eq!(
        cup, concrete,
        "small SetCup should equal its materialization"
    );
    assert_eq!(
        hash_value(&cup),
        hash_value(&concrete),
        "Hash/Eq violation: small SetCup and its materialization hash differently"
    );
}

// === StringSet and AnySet hashing ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_stringset_anyset_distinct() {
    let h_string = hash_value(&Value::StringSet);
    let h_any = hash_value(&Value::AnySet);
    assert_ne!(
        h_string, h_any,
        "StringSet and AnySet should have different hashes"
    );
    // Stability
    assert_eq!(hash_value(&Value::StringSet), h_string);
    assert_eq!(hash_value(&Value::AnySet), h_any);
}
