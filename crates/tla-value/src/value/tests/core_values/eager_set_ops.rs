// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Eager set-operation tests: powerset, big_union, cartesian_product.
//!
//! Includes duplicate-storage regression tests added after SortedSet normalization.

use super::super::super::*;
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_powerset() {
    let s = SortedSet::from_iter(vec![Value::int(1), Value::int(2)]);
    let ps = powerset(&s).unwrap();
    let ps_set = ps.as_set().unwrap();
    assert_eq!(ps_set.len(), 4); // 2^2 = 4

    // Contains empty set
    assert!(ps_set.contains(&Value::empty_set()));
    // Contains singleton subsets
    assert!(ps_set.contains(&Value::set([Value::int(1)])));
    assert!(ps_set.contains(&Value::set([Value::int(2)])));
    // Contains full set
    assert!(ps_set.contains(&Value::set([Value::int(1), Value::int(2)])));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_powerset_too_large() {
    // 21 elements would produce 2^21 > 2M subsets
    let s = SortedSet::from_iter((0..21).map(Value::int));
    let result = powerset(&s);
    assert!(matches!(
        result,
        Err(crate::error::EvalError::SetTooLarge { .. })
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_big_union() {
    let s = SortedSet::from_iter(vec![
        Value::set([Value::int(1), Value::int(2)]),
        Value::set([Value::int(2), Value::int(3)]),
    ]);

    let u = big_union(&s).unwrap();
    let u_set = u.as_set().unwrap();
    assert_eq!(u_set.len(), 3);
    assert!(u_set.contains(&Value::int(1)));
    assert!(u_set.contains(&Value::int(2)));
    assert!(u_set.contains(&Value::int(3)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_big_union_with_unnormalized_duplicate_storage() {
    let left = Value::Set(Arc::new(SortedSet::from_iter(vec![
        Value::int(2),
        Value::int(1),
        Value::int(1),
    ])));
    let right = Value::Set(Arc::new(SortedSet::from_iter(vec![
        Value::int(3),
        Value::int(2),
        Value::int(3),
    ])));
    let outer = SortedSet::from_iter(vec![left, right, Value::set([Value::int(2)])]);

    let union = big_union(&outer).expect("big union should succeed");
    let union_set = union.as_set().expect("result should be a set");

    assert_eq!(union_set.len(), 3);
    assert!(union_set.contains(&Value::int(1)));
    assert!(union_set.contains(&Value::int(2)));
    assert!(union_set.contains(&Value::int(3)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cartesian_product() {
    let s1 = Value::set([Value::int(1), Value::int(2)])
        .to_sorted_set()
        .expect("set literal should materialize");
    let s2 = Value::set([Value::string("a"), Value::string("b")])
        .to_sorted_set()
        .expect("set literal should materialize");

    let cp = cartesian_product(&[&s1, &s2]);
    let cp_set = cp.as_set().unwrap();
    assert_eq!(cp_set.len(), 4); // 2 * 2

    assert!(cp_set.contains(&Value::tuple([Value::int(1), Value::string("a")])));
    assert!(cp_set.contains(&Value::tuple([Value::int(1), Value::string("b")])));
    assert!(cp_set.contains(&Value::tuple([Value::int(2), Value::string("a")])));
    assert!(cp_set.contains(&Value::tuple([Value::int(2), Value::string("b")])));
    assert!(!cp_set.contains(&Value::tuple([Value::int(3), Value::string("a")])));

    // Single input set maps each element into a 1-tuple.
    let singleton = Value::set([Value::int(7)])
        .to_sorted_set()
        .expect("singleton should materialize");
    let singleton_product = cartesian_product(&[&singleton]);
    let singleton_set = singleton_product.as_set().unwrap();
    assert_eq!(singleton_set.len(), 1);
    assert!(singleton_set.contains(&Value::tuple([Value::int(7)])));

    // Self-product should include all ordered pairs.
    let self_product = cartesian_product(&[&s1, &s1]);
    let self_product_set = self_product.as_set().unwrap();
    assert_eq!(self_product_set.len(), 4);
    assert!(self_product_set.contains(&Value::tuple([Value::int(1), Value::int(1)])));
    assert!(self_product_set.contains(&Value::tuple([Value::int(1), Value::int(2)])));
    assert!(self_product_set.contains(&Value::tuple([Value::int(2), Value::int(1)])));
    assert!(self_product_set.contains(&Value::tuple([Value::int(2), Value::int(2)])));

    // Empty product is a singleton set containing the empty tuple.
    let empty_product = cartesian_product(&[]);
    let empty_product_set = empty_product.as_set().unwrap();
    assert_eq!(empty_product_set.len(), 1);
    assert!(empty_product_set.contains(&Value::tuple([])));
}

/// Part of #3364: Verify SubsetIterator yields subsets in TLC cardinality-first
/// order and stores each result in the Normalized storage lane directly (not the
/// lazy Unnormalized lane that would trigger a second allocation later).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subset_iterator_produces_normalized_sets() {
    let base = SortedSet::from_sorted_vec(vec![Value::int(1), Value::int(2)]);
    let subsets: Vec<Value> = crate::value::SubsetIterator::new(base).collect();

    // TLC cardinality-first order: {}, {1}, {2}, {1, 2}
    assert_eq!(subsets.len(), 4);
    assert_eq!(subsets[0], Value::empty_set());
    assert_eq!(subsets[1], Value::set([Value::int(1)]));
    assert_eq!(subsets[2], Value::set([Value::int(2)]));
    assert_eq!(subsets[3], Value::set([Value::int(1), Value::int(2)]));

    // Non-empty subsets must be in the Normalized storage lane immediately —
    // this is the #3364 fix that avoids the double allocation through
    // from_unnormalized_vec → normalized_elements_from_raw.
    for (i, v) in subsets.iter().enumerate().skip(1) {
        let ss = v
            .as_set()
            .unwrap_or_else(|| panic!("subset[{i}] should be a set"));
        assert!(
            ss.is_normalized(),
            "subset[{i}] should be in Normalized storage lane, not Unnormalized"
        );
    }
}

/// Part of #3364: Mirror of test_subset_iterator_produces_normalized_sets for
/// KSubsetIterator — both iterators must use the same from_sorted_vec path.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_iterator_produces_normalized_sets() {
    let base = SortedSet::from_sorted_vec(vec![Value::int(1), Value::int(2), Value::int(3)]);
    let k2: Vec<Value> = crate::value::KSubsetIterator::new(base.clone(), 2).collect();

    // C(3,2) = 3 subsets: {1,2}, {1,3}, {2,3}
    assert_eq!(k2.len(), 3);
    assert_eq!(k2[0], Value::set([Value::int(1), Value::int(2)]));
    assert_eq!(k2[1], Value::set([Value::int(1), Value::int(3)]));
    assert_eq!(k2[2], Value::set([Value::int(2), Value::int(3)]));

    for (i, v) in k2.iter().enumerate() {
        let ss = v
            .as_set()
            .unwrap_or_else(|| panic!("k2[{i}] should be a set"));
        assert!(
            ss.is_normalized(),
            "k2[{i}] should be in Normalized storage lane"
        );
    }

    // k=0 yields one empty set, k=3 yields one full set
    let k0: Vec<Value> = crate::value::KSubsetIterator::new(base.clone(), 0).collect();
    assert_eq!(k0.len(), 1);
    assert_eq!(k0[0], Value::empty_set());

    let k3: Vec<Value> = crate::value::KSubsetIterator::new(base, 3).collect();
    assert_eq!(k3.len(), 1);
    assert_eq!(
        k3[0],
        Value::set([Value::int(1), Value::int(2), Value::int(3)])
    );
    let ss = k3[0].as_set().expect("k3[0] should be a set");
    assert!(
        ss.is_normalized(),
        "k3[0] should be in Normalized storage lane"
    );
}

/// Part of #3364: `iter_set_tlc_normalized()` feeds `SubsetIterator::from_elements`
/// with TLC order, which can differ from `Value::cmp` order for strings. The
/// subset iterator must re-sort each subset before `from_sorted_vec` so the
/// stored set stays normalized.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subset_tlc_normalized_iteration_produces_value_cmp_sorted_sets() {
    let _guard = crate::value::lock_intern_state();
    crate::value::clear_tlc_string_tokens();

    let s_zulu: Arc<str> = Arc::from("__subset_iter_tlc_zulu");
    let s_alpha: Arc<str> = Arc::from("__subset_iter_tlc_alpha");
    let s_mike: Arc<str> = Arc::from("__subset_iter_tlc_mike");

    let tok_zulu = crate::value::tlc_string_token(&s_zulu);
    let tok_alpha = crate::value::tlc_string_token(&s_alpha);
    let tok_mike = crate::value::tlc_string_token(&s_mike);
    assert!(tok_zulu < tok_alpha);
    assert!(tok_alpha < tok_mike);

    let base = Value::set([
        Value::String(s_alpha.clone()),
        Value::String(s_mike.clone()),
        Value::String(s_zulu.clone()),
    ]);
    let subsets: Vec<Value> = Value::Subset(SubsetValue::new(base))
        .iter_set_tlc_normalized()
        .expect("SUBSET over strings should be enumerable")
        .collect();

    assert_eq!(subsets.len(), 8);
    assert_eq!(subsets[0], Value::empty_set());
    assert_eq!(subsets[1], Value::set([Value::String(s_zulu.clone())]));
    assert_eq!(subsets[2], Value::set([Value::String(s_alpha.clone())]));
    assert_eq!(subsets[3], Value::set([Value::String(s_mike.clone())]));
    assert_eq!(
        subsets[4],
        Value::set([
            Value::String(s_zulu.clone()),
            Value::String(s_alpha.clone())
        ])
    );

    for (i, subset) in subsets.iter().enumerate().skip(1) {
        let ss = subset
            .as_set()
            .unwrap_or_else(|| panic!("subset[{i}] should be a set"));
        assert!(ss.is_normalized(), "subset[{i}] should be normalized");
    }

    let first_pair = subsets[4].as_set().expect("subsets[4] should be a set");
    assert_eq!(
        first_pair.iter().cloned().collect::<Vec<_>>(),
        vec![Value::String(s_alpha), Value::String(s_zulu)],
        "stored subset elements must be re-sorted into Value::cmp order"
    );

    crate::value::clear_tlc_string_tokens();
}

/// Part of #3364: Mirror the TLC-normalized regression for `KSubsetIterator`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_tlc_normalized_iteration_produces_value_cmp_sorted_sets() {
    let _guard = crate::value::lock_intern_state();
    crate::value::clear_tlc_string_tokens();

    let s_zulu: Arc<str> = Arc::from("__ksubset_iter_tlc_zulu");
    let s_alpha: Arc<str> = Arc::from("__ksubset_iter_tlc_alpha");
    let s_mike: Arc<str> = Arc::from("__ksubset_iter_tlc_mike");

    let tok_zulu = crate::value::tlc_string_token(&s_zulu);
    let tok_alpha = crate::value::tlc_string_token(&s_alpha);
    let tok_mike = crate::value::tlc_string_token(&s_mike);
    assert!(tok_zulu < tok_alpha);
    assert!(tok_alpha < tok_mike);

    let base = Value::set([
        Value::String(s_alpha.clone()),
        Value::String(s_mike.clone()),
        Value::String(s_zulu.clone()),
    ]);
    let subsets: Vec<Value> = Value::KSubset(KSubsetValue::new(base, 2))
        .iter_set_tlc_normalized()
        .expect("KSubset over strings should be enumerable")
        .collect();

    assert_eq!(subsets.len(), 3);
    assert_eq!(
        subsets[0],
        Value::set([
            Value::String(s_zulu.clone()),
            Value::String(s_alpha.clone())
        ])
    );

    for (i, subset) in subsets.iter().enumerate() {
        let ss = subset
            .as_set()
            .unwrap_or_else(|| panic!("subset[{i}] should be a set"));
        assert!(ss.is_normalized(), "subset[{i}] should be normalized");
    }

    let first_pair = subsets[0].as_set().expect("subsets[0] should be a set");
    assert_eq!(
        first_pair.iter().cloned().collect::<Vec<_>>(),
        vec![Value::String(s_alpha), Value::String(s_zulu)],
        "stored k-subset elements must be re-sorted into Value::cmp order"
    );

    crate::value::clear_tlc_string_tokens();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cartesian_product_with_unnormalized_duplicate_storage() {
    let s1 = SortedSet::from_iter(vec![Value::int(2), Value::int(1), Value::int(1)]);
    let s2 = SortedSet::from_iter(vec![
        Value::string("b"),
        Value::string("a"),
        Value::string("b"),
    ]);

    let product = cartesian_product(&[&s1, &s2]);
    let product_set = product.as_set().expect("result should be a set");

    assert_eq!(product_set.len(), 4);
    assert!(product_set.contains(&Value::tuple([Value::int(1), Value::string("a")])));
    assert!(product_set.contains(&Value::tuple([Value::int(1), Value::string("b")])));
    assert!(product_set.contains(&Value::tuple([Value::int(2), Value::string("a")])));
    assert!(product_set.contains(&Value::tuple([Value::int(2), Value::string("b")])));
}
