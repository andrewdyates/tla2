// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::kani_harnesses::kani_generators::*;
use crate::value::Value;
use num_bigint::BigInt;
use std::collections::BTreeSet;
use std::sync::Arc;

// P9: Set Operations

#[kani::proof]
fn verify_set_union_commutative() {
    let a = any_small_set();
    let b = any_small_set();
    if let (Value::Set(set_a), Value::Set(set_b)) = (&a, &b) {
        let union_ab = Value::Set(Arc::new(set_a.union(set_b)));
        let union_ba = Value::Set(Arc::new(set_b.union(set_a)));
        assert!(union_ab == union_ba, "Set union must be commutative");
    }
}

#[kani::proof]
fn verify_set_intersection_commutative() {
    let a = any_small_set();
    let b = any_small_set();
    if let (Value::Set(set_a), Value::Set(set_b)) = (&a, &b) {
        let inter_ab = set_a.intersection(set_b);
        let inter_ba = set_b.intersection(set_a);
        assert!(inter_ab == inter_ba, "Set intersection must be commutative");
    }
}

#[kani::proof]
fn verify_set_union_identity() {
    use crate::value::SortedSet;
    let a = any_small_set();
    let empty = SortedSet::new();
    if let Value::Set(set_a) = &a {
        let union = set_a.union(&empty);
        assert!(union == **set_a, "Empty set is union identity");
    }
}

#[kani::proof]
fn verify_set_intersection_empty() {
    use crate::value::SortedSet;
    let a = any_small_set();
    let empty = SortedSet::new();
    if let Value::Set(set_a) = &a {
        let inter = set_a.intersection(&empty);
        assert!(inter.is_empty(), "Intersection with empty is empty");
    }
}

#[kani::proof]
fn verify_set_difference_self() {
    let a = any_small_set();
    if let Value::Set(set_a) = &a {
        let diff = set_a.difference(set_a);
        assert!(diff.is_empty(), "A \\ A must be empty");
    }
}

#[kani::proof]
fn verify_set_difference_empty() {
    use crate::value::SortedSet;
    let a = any_small_set();
    let empty = SortedSet::new();
    if let Value::Set(set_a) = &a {
        let diff = set_a.difference(&empty);
        assert!(diff == **set_a, "A \\ {} = A");
    }
}

#[kani::proof]
fn verify_set_membership_insert() {
    let v = any_primitive_value();
    let s = make_set(vec![v.clone()]);
    assert!(
        s.set_contains(&v).unwrap_or(false),
        "Inserted element must be in set"
    );
}

#[kani::proof]
fn verify_subset_reflexive() {
    let a = any_small_set();
    if let Value::Set(set_a) = &a {
        assert!(set_a.is_subset(set_a), "A must be subset of itself");
    }
}

#[kani::proof]
fn verify_empty_subset_all() {
    use crate::value::SortedSet;
    let a = any_small_set();
    let empty = SortedSet::new();
    if let Value::Set(set_a) = &a {
        assert!(empty.is_subset(set_a), "Empty set is subset of all sets");
    }
}

// P41: Set Operator Semantics

#[kani::proof]
fn verify_set_union_membership() {
    let a = any_small_set();
    let b = any_small_set();
    let x = any_small_int_value();
    if let (Value::Set(set_a), Value::Set(set_b)) = (&a, &b) {
        let union = set_a.union(set_b);
        let x_in_union = union.contains(&x);
        let x_in_a = set_a.contains(&x);
        let x_in_b = set_b.contains(&x);
        assert!(
            x_in_union == (x_in_a || x_in_b),
            "x in (A ∪ B) iff (x in A) or (x in B)"
        );
    }
}

#[kani::proof]
fn verify_set_intersection_membership() {
    let a = any_small_set();
    let b = any_small_set();
    let x = any_small_int_value();
    if let (Value::Set(set_a), Value::Set(set_b)) = (&a, &b) {
        let inter = set_a.intersection(set_b);
        let x_in_inter = inter.contains(&x);
        let x_in_a = set_a.contains(&x);
        let x_in_b = set_b.contains(&x);
        assert!(
            x_in_inter == (x_in_a && x_in_b),
            "x in (A ∩ B) iff (x in A) and (x in B)"
        );
    }
}

#[kani::proof]
fn verify_set_difference_membership() {
    let a = any_small_set();
    let b = any_small_set();
    let x = any_small_int_value();
    if let (Value::Set(set_a), Value::Set(set_b)) = (&a, &b) {
        let diff = set_a.difference(set_b);
        let x_in_diff = diff.contains(&x);
        let x_in_a = set_a.contains(&x);
        let x_not_in_b = !set_b.contains(&x);
        assert!(
            x_in_diff == (x_in_a && x_not_in_b),
            "x in (A \\ B) iff (x in A) and (x not in B)"
        );
    }
}

#[kani::proof]
fn verify_set_subset_definition() {
    let a = any_small_set();
    let b = any_small_set();
    if let (Value::Set(set_a), Value::Set(set_b)) = (&a, &b) {
        let is_subset = set_a.is_subset(set_b);
        let all_in_b = set_a.iter().all(|x| set_b.contains(x));
        assert!(
            is_subset == all_in_b,
            "A ⊆ B iff all elements of A are in B"
        );
    }
}

// P45: Quantifier Semantics - Empty Domain

#[kani::proof]
fn verify_forall_empty_is_true() {
    let empty: BTreeSet<Value> = BTreeSet::new();
    let result = empty.iter().all(|_x| false);
    assert!(result, "∀x ∈ {} : P(x) must be TRUE (vacuously)");
}

#[kani::proof]
fn verify_exists_empty_is_false() {
    let empty: BTreeSet<Value> = BTreeSet::new();
    let result = empty.iter().any(|_x| true);
    assert!(!result, "∃x ∈ {} : P(x) must be FALSE (no witnesses)");
}

// P46: Quantifier Semantics - Singleton Domain

#[kani::proof]
fn verify_forall_singleton() {
    let elem = any_small_int_value();
    let set = BTreeSet::from([elem.clone()]);
    let forall_result = set.iter().all(|x| x == &elem);
    let direct_result = elem == elem;
    assert!(
        forall_result == direct_result,
        "∀x ∈ {{a}} : P(x) must equal P(a)"
    );
}

#[kani::proof]
fn verify_exists_singleton() {
    let elem = any_small_int_value();
    let set = BTreeSet::from([elem.clone()]);
    let exists_result = set.iter().any(|x| x == &elem);
    let direct_result = elem == elem;
    assert!(
        exists_result == direct_result,
        "∃x ∈ {{a}} : P(x) must equal P(a)"
    );
}

// P47: Quantifier Semantics - TRUE/FALSE predicates

#[kani::proof]
fn verify_forall_true_predicate() {
    let s = any_small_set();
    if let Value::Set(set) = s {
        let result = set.iter().all(|_x| true);
        assert!(result, "∀x ∈ S : TRUE must be TRUE");
    }
}

#[kani::proof]
fn verify_exists_true_predicate_nonempty() {
    let set = BTreeSet::from([Value::int(1)]);
    let result = set.iter().any(|_x| true);
    assert!(result, "∃x ∈ S : TRUE must be TRUE for non-empty S");
}

#[kani::proof]
fn verify_forall_false_predicate_nonempty() {
    let set = BTreeSet::from([Value::int(1)]);
    let result = set.iter().all(|_x| false);
    assert!(!result, "∀x ∈ S : FALSE must be FALSE for non-empty S");
}

#[kani::proof]
fn verify_exists_false_predicate() {
    let s = any_small_set();
    if let Value::Set(set) = s {
        let result = set.iter().any(|_x| false);
        assert!(!result, "∃x ∈ S : FALSE must be FALSE");
    }
}

// P48: Quantifier Duality

#[kani::proof]
fn verify_quantifier_duality_forall() {
    let s = any_small_set();
    if let Value::Set(set) = s {
        let predicate = |x: &Value| matches!(x, Value::Bool(_));
        let not_forall = !set.iter().all(predicate);
        let exists_not = set.iter().any(|x| !predicate(x));
        assert!(
            not_forall == exists_not,
            "¬(∀x : P(x)) must equal ∃x : ¬P(x)"
        );
    }
}

#[kani::proof]
fn verify_quantifier_duality_exists() {
    let s = any_small_set();
    if let Value::Set(set) = s {
        let predicate = |x: &Value| matches!(x, Value::Bool(_));
        let not_exists = !set.iter().any(predicate);
        let forall_not = set.iter().all(|x| !predicate(x));
        assert!(
            not_exists == forall_not,
            "¬(∃x : P(x)) must equal ∀x : ¬P(x)"
        );
    }
}

// P51: CHOOSE Operator Semantics

#[kani::proof]
fn verify_choose_true_predicate_returns_first() {
    let set = BTreeSet::from([Value::int(1), Value::int(2), Value::int(3)]);
    let result = choose(&set, |_| true);
    assert!(
        result.is_some(),
        "CHOOSE TRUE on non-empty set must succeed"
    );
    let first = set.iter().next().unwrap().clone();
    assert!(
        result.unwrap() == first,
        "CHOOSE TRUE must return first element"
    );
}

#[kani::proof]
fn verify_choose_singleton_returns_element() {
    let elem = any_small_int_value();
    let set = BTreeSet::from([elem.clone()]);
    let result = choose(&set, |_| true);
    assert!(result.is_some(), "CHOOSE on singleton must succeed");
    assert!(
        result.unwrap() == elem,
        "CHOOSE on singleton must return that element"
    );
}

#[kani::proof]
fn verify_choose_empty_set_fails() {
    let empty: BTreeSet<Value> = BTreeSet::new();
    let result = choose(&empty, |_| true);
    assert!(result.is_none(), "CHOOSE on empty set must fail");
}

#[kani::proof]
fn verify_choose_deterministic() {
    let set = BTreeSet::from([Value::int(1), Value::int(2)]);
    let predicate = |x: &Value| match x {
        Value::Int(n) => **n > BigInt::from(0),
        Value::SmallInt(n) => *n > 0,
        _ => false,
    };
    let result1 = choose(&set, predicate);
    let result2 = choose(&set, predicate);
    assert!(result1 == result2, "CHOOSE must be deterministic");
}

#[kani::proof]
fn verify_choose_returns_satisfying_element() {
    let set = BTreeSet::from([Value::int(1), Value::int(2), Value::int(3)]);
    let predicate = |x: &Value| match x {
        Value::Int(n) => **n > BigInt::from(1),
        Value::SmallInt(n) => *n > 1,
        _ => false,
    };
    let result = choose(&set, &predicate);
    assert!(
        result.is_some(),
        "CHOOSE with satisfiable predicate must succeed"
    );
    let chosen = result.unwrap();
    assert!(predicate(&chosen), "CHOOSE result must satisfy predicate");
}

#[kani::proof]
fn verify_choose_unsatisfiable_predicate_fails() {
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

// P56: Set Cardinality

#[kani::proof]
fn verify_set_cardinality() {
    let choice: u8 = kani::any();
    kani::assume(choice < 4);
    let set: BTreeSet<Value> = match choice {
        0 => BTreeSet::new(),
        1 => BTreeSet::from([Value::int(1)]),
        2 => BTreeSet::from([Value::int(1), Value::int(2)]),
        _ => BTreeSet::from([Value::int(1), Value::int(2), Value::int(3)]),
    };
    assert!(
        set.len() == choice as usize,
        "Set cardinality must equal element count"
    );
}

// P57: Empty Set

#[kani::proof]
fn verify_empty_set_has_no_elements() {
    let empty: BTreeSet<Value> = BTreeSet::new();
    let v = any_primitive_value();
    assert!(
        !empty.contains(&v),
        "Empty set must not contain any element"
    );
}

#[kani::proof]
fn verify_empty_set_subset_of_all() {
    let empty: BTreeSet<Value> = BTreeSet::new();
    let other = BTreeSet::from([any_primitive_value()]);
    assert!(
        empty.is_subset(&other),
        "Empty set must be subset of all sets"
    );
    assert!(
        empty.is_subset(&empty),
        "Empty set must be subset of itself"
    );
}

// P-BoolOnly set operations

#[kani::proof]
fn verify_set_union_commutative_boolonly() {
    let a = any_small_set_boolonly();
    let b = any_small_set_boolonly();
    if let (Value::Set(set_a), Value::Set(set_b)) = (&a, &b) {
        let union_ab = Value::Set(Arc::new(set_a.union(set_b)));
        let union_ba = Value::Set(Arc::new(set_b.union(set_a)));
        assert!(union_ab == union_ba, "Set union must be commutative");
    }
}

#[kani::proof]
fn verify_set_intersection_commutative_boolonly() {
    let a = any_small_set_boolonly();
    let b = any_small_set_boolonly();
    if let (Value::Set(set_a), Value::Set(set_b)) = (&a, &b) {
        let inter_ab = set_a.intersection(set_b);
        let inter_ba = set_b.intersection(set_a);
        assert!(inter_ab == inter_ba, "Set intersection must be commutative");
    }
}

#[kani::proof]
fn verify_set_union_identity_boolonly() {
    use crate::value::SortedSet;
    let a = any_small_set_boolonly();
    let empty = SortedSet::new();
    if let Value::Set(set_a) = &a {
        let union = set_a.union(&empty);
        assert!(union == **set_a, "Empty set is union identity");
    }
}

#[kani::proof]
fn verify_set_intersection_empty_boolonly() {
    use crate::value::SortedSet;
    let a = any_small_set_boolonly();
    let empty = SortedSet::new();
    if let Value::Set(set_a) = &a {
        let inter = set_a.intersection(&empty);
        assert!(inter.is_empty(), "Intersection with empty is empty");
    }
}

#[kani::proof]
fn verify_set_difference_self_boolonly() {
    let a = any_small_set_boolonly();
    if let Value::Set(set_a) = &a {
        let diff = set_a.difference(set_a);
        assert!(diff.is_empty(), "Set difference with self must be empty");
    }
}
