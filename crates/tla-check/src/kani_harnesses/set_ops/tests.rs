// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::kani_harnesses::test_helpers::{choose, make_set};
use crate::value::Value;
use num_bigint::BigInt;
use std::collections::BTreeSet;
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_union_commutative() {
    let set_a = BTreeSet::from([Value::int(1), Value::int(2)]);
    let set_b = BTreeSet::from([Value::int(2), Value::int(3)]);
    let union_ab: BTreeSet<Value> = set_a.union(&set_b).cloned().collect();
    let union_ba: BTreeSet<Value> = set_b.union(&set_a).cloned().collect();
    assert_eq!(union_ab, union_ba, "Set union must be commutative");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_intersection_commutative() {
    let set_a = BTreeSet::from([Value::int(1), Value::int(2)]);
    let set_b = BTreeSet::from([Value::int(2), Value::int(3)]);
    let inter_ab: BTreeSet<Value> = set_a.intersection(&set_b).cloned().collect();
    let inter_ba: BTreeSet<Value> = set_b.intersection(&set_a).cloned().collect();
    assert_eq!(inter_ab, inter_ba, "Set intersection must be commutative");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_operations_identity() {
    let set_a = BTreeSet::from([Value::int(1), Value::int(2)]);
    let empty: BTreeSet<Value> = BTreeSet::new();
    let union: BTreeSet<Value> = set_a.union(&empty).cloned().collect();
    assert_eq!(union, set_a, "A ∪ {{}} = A");
    let inter: BTreeSet<Value> = set_a.intersection(&empty).cloned().collect();
    assert!(inter.is_empty(), "A ∩ {{}} = {{}}");
    let diff: BTreeSet<Value> = set_a.difference(&set_a).cloned().collect();
    assert!(diff.is_empty(), "A \\ A = {{}}");
    let diff2: BTreeSet<Value> = set_a.difference(&empty).cloned().collect();
    assert_eq!(diff2, set_a, "A \\ {{}} = A");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_membership() {
    let v1 = Value::int(1);
    let v2 = Value::int(2);
    let s = make_set(vec![v1.clone()]);
    assert!(
        s.set_contains(&v1).unwrap_or(false),
        "Inserted element must be in set"
    );
    assert!(
        !s.set_contains(&v2).unwrap_or(true),
        "Non-inserted element must not be in set"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subset_relations() {
    let set_a = BTreeSet::from([Value::int(1)]);
    let set_b = BTreeSet::from([Value::int(1), Value::int(2)]);
    let empty: BTreeSet<Value> = BTreeSet::new();
    assert!(set_a.is_subset(&set_a), "A ⊆ A");
    assert!(set_b.is_subset(&set_b), "B ⊆ B");
    assert!(empty.is_subset(&set_a), "{{}} ⊆ A");
    assert!(empty.is_subset(&set_b), "{{}} ⊆ B");
    assert!(set_a.is_subset(&set_b), "{{1}} ⊆ {{1,2}}");
    assert!(!set_b.is_subset(&set_a), "{{1,2}} ⊄ {{1}}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_union_membership() {
    let set_a = BTreeSet::from([Value::int(1), Value::int(2)]);
    let set_b = BTreeSet::from([Value::int(2), Value::int(3)]);
    let union: BTreeSet<Value> = set_a.union(&set_b).cloned().collect();
    for i in 0..5 {
        let x = Value::int(i);
        let x_in_union = union.contains(&x);
        let x_in_a = set_a.contains(&x);
        let x_in_b = set_b.contains(&x);
        assert_eq!(
            x_in_union,
            x_in_a || x_in_b,
            "x in (A ∪ B) iff (x in A) or (x in B)"
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_intersection_membership() {
    let set_a = BTreeSet::from([Value::int(1), Value::int(2)]);
    let set_b = BTreeSet::from([Value::int(2), Value::int(3)]);
    let inter: BTreeSet<Value> = set_a.intersection(&set_b).cloned().collect();
    for i in 0..5 {
        let x = Value::int(i);
        let x_in_inter = inter.contains(&x);
        let x_in_a = set_a.contains(&x);
        let x_in_b = set_b.contains(&x);
        assert_eq!(
            x_in_inter,
            x_in_a && x_in_b,
            "x in (A ∩ B) iff (x in A) and (x in B)"
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_difference_membership() {
    let set_a = BTreeSet::from([Value::int(1), Value::int(2)]);
    let set_b = BTreeSet::from([Value::int(2), Value::int(3)]);
    let diff: BTreeSet<Value> = set_a.difference(&set_b).cloned().collect();
    for i in 0..5 {
        let x = Value::int(i);
        let x_in_diff = diff.contains(&x);
        let x_in_a = set_a.contains(&x);
        let x_not_in_b = !set_b.contains(&x);
        assert_eq!(
            x_in_diff,
            x_in_a && x_not_in_b,
            "x in (A \\ B) iff (x in A) and (x not in B)"
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_subset_definition() {
    let set_a = BTreeSet::from([Value::int(1)]);
    let set_b = BTreeSet::from([Value::int(1), Value::int(2)]);
    assert!(set_a.is_subset(&set_b), "{{1}} ⊆ {{1,2}}");
    assert!(!set_b.is_subset(&set_a), "{{1,2}} ⊄ {{1}}");
    let empty: BTreeSet<Value> = BTreeSet::new();
    assert!(empty.is_subset(&set_a), "∅ ⊆ A for all A");
    assert!(set_a.is_subset(&set_a), "A ⊆ A (reflexivity)");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_empty_is_true() {
    let empty: BTreeSet<Value> = BTreeSet::new();
    let result = empty.iter().all(|_x| false);
    assert!(result, "∀x ∈ {{}} : P(x) must be TRUE (vacuously)");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_empty_is_false() {
    let empty: BTreeSet<Value> = BTreeSet::new();
    let result = empty.iter().any(|_x| true);
    assert!(!result, "∃x ∈ {{}} : P(x) must be FALSE (no witnesses)");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_singleton() {
    let elem = Value::int(42);
    let set = BTreeSet::from([elem.clone()]);
    let forall_result = set.iter().all(|x| *x == elem);
    let direct_result = elem == elem;
    assert_eq!(
        forall_result, direct_result,
        "∀x ∈ {{a}} : P(x) must equal P(a)"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_singleton() {
    let elem = Value::int(42);
    let set = BTreeSet::from([elem.clone()]);
    let exists_result = set.iter().any(|x| *x == elem);
    let direct_result = elem == elem;
    assert_eq!(
        exists_result, direct_result,
        "∃x ∈ {{a}} : P(x) must equal P(a)"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_true_predicate() {
    let set = BTreeSet::from([Value::int(1), Value::int(2)]);
    let result = set.iter().all(|_x| true);
    assert!(result, "∀x ∈ S : TRUE must be TRUE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_true_predicate_nonempty() {
    let set = BTreeSet::from([Value::int(1)]);
    let result = set.iter().any(|_x| true);
    assert!(result, "∃x ∈ S : TRUE must be TRUE for non-empty S");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_false_predicate_nonempty() {
    let set = BTreeSet::from([Value::int(1)]);
    let result = set.iter().all(|_x| false);
    assert!(!result, "∀x ∈ S : FALSE must be FALSE for non-empty S");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_false_predicate() {
    let set = BTreeSet::from([Value::int(1), Value::int(2)]);
    let result = set.iter().any(|_x| false);
    assert!(!result, "∃x ∈ S : FALSE must be FALSE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_quantifier_duality_forall() {
    let set = BTreeSet::from([Value::Bool(true), Value::int(1), Value::string("x")]);
    let predicate = |x: &Value| matches!(x, Value::Bool(_));
    let not_forall = !set.iter().all(predicate);
    let exists_not = set.iter().any(|x| !predicate(x));
    assert_eq!(not_forall, exists_not, "¬(∀x : P(x)) must equal ∃x : ¬P(x)");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_quantifier_duality_exists() {
    let set = BTreeSet::from([Value::Bool(true), Value::int(1), Value::string("x")]);
    let predicate = |x: &Value| matches!(x, Value::Bool(_));
    let not_exists = !set.iter().any(predicate);
    let forall_not = set.iter().all(|x| !predicate(x));
    assert_eq!(not_exists, forall_not, "¬(∃x : P(x)) must equal ∀x : ¬P(x)");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_true_predicate_returns_first() {
    let set = BTreeSet::from([Value::int(1), Value::int(2), Value::int(3)]);
    let result = choose(&set, |_| true);
    assert!(
        result.is_some(),
        "CHOOSE TRUE on non-empty set must succeed"
    );
    let first = set.iter().next().unwrap().clone();
    assert_eq!(
        result.unwrap(),
        first,
        "CHOOSE TRUE must return first element"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_singleton_returns_element() {
    let elem = Value::int(42);
    let set = BTreeSet::from([elem.clone()]);
    let result = choose(&set, |_| true);
    assert!(result.is_some(), "CHOOSE on singleton must succeed");
    assert_eq!(
        result.unwrap(),
        elem,
        "CHOOSE on singleton must return that element"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_empty_set_fails() {
    let empty: BTreeSet<Value> = BTreeSet::new();
    let result = choose(&empty, |_| true);
    assert!(result.is_none(), "CHOOSE on empty set must fail");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_deterministic() {
    let set = BTreeSet::from([Value::int(1), Value::int(2)]);
    let predicate = |x: &Value| match x {
        Value::Int(n) => **n > BigInt::from(0),
        Value::SmallInt(n) => *n > 0,
        _ => false,
    };
    let result1 = choose(&set, predicate);
    let result2 = choose(&set, predicate);
    assert_eq!(result1, result2, "CHOOSE must be deterministic");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_returns_satisfying_element() {
    let set = BTreeSet::from([Value::int(1), Value::int(2), Value::int(3)]);
    let predicate = |x: &Value| match x {
        Value::Int(n) => **n > BigInt::from(1),
        Value::SmallInt(n) => *n > 1,
        _ => false,
    };
    let result = choose(&set, predicate);
    assert!(
        result.is_some(),
        "CHOOSE with satisfiable predicate must succeed"
    );
    let chosen = result.unwrap();
    match &chosen {
        Value::Int(n) => assert!(
            **n > BigInt::from(1),
            "CHOOSE result must satisfy predicate"
        ),
        Value::SmallInt(n) => assert!(*n > 1, "CHOOSE result must satisfy predicate"),
        _ => panic!("CHOOSE result should be an Int"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_unsatisfiable_predicate_fails() {
    let set = BTreeSet::from([Value::int(1), Value::int(2)]);
    let predicate = |x: &Value| match x {
        Value::Int(n) => **n > BigInt::from(100),
        Value::SmallInt(n) => *n > 100,
        _ => false,
    };
    let result = choose(&set, predicate);
    assert!(
        result.is_none(),
        "CHOOSE with unsatisfiable predicate must fail"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_cardinality() {
    let empty: BTreeSet<Value> = BTreeSet::new();
    assert_eq!(empty.len(), 0);
    let s1 = BTreeSet::from([Value::int(1)]);
    assert_eq!(s1.len(), 1);
    let s2 = BTreeSet::from([Value::int(1), Value::int(2), Value::int(3)]);
    assert_eq!(s2.len(), 3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_empty_set_has_no_elements() {
    let empty: BTreeSet<Value> = BTreeSet::new();
    let test_values = [
        Value::Bool(true),
        Value::int(42),
        Value::String(Arc::from("test")),
    ];
    for v in test_values {
        assert!(
            !empty.contains(&v),
            "Empty set must not contain any element"
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_empty_set_subset_of_all() {
    let empty: BTreeSet<Value> = BTreeSet::new();
    let other = BTreeSet::from([Value::int(1), Value::int(2)]);
    assert!(
        empty.is_subset(&other),
        "Empty set must be subset of all sets"
    );
    assert!(
        empty.is_subset(&empty),
        "Empty set must be subset of itself"
    );
}
