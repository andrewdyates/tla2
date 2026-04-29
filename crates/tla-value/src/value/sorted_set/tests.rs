// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lazy normalization tests for `SortedSet`.
//!
//! Extracted from `sorted_set.rs` per #3326. Kept as a child module
//! of `sorted_set` to preserve access to private internals (`storage`,
//! `SetStorage::Unnormalized`, etc.) without widening visibility.

use super::*;
use crate::value::clear_set_intern_table;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

fn hash_sorted_set(set: &SortedSet) -> u64 {
    let mut hasher = DefaultHasher::new();
    set.hash(&mut hasher);
    hasher.finish()
}

#[test]
fn from_iter_defers_normalization_until_ordered_observation() {
    let set = SortedSet::from_iter(vec![
        Value::int(3),
        Value::int(1),
        Value::int(3),
        Value::int(2),
    ]);

    match &set.storage {
        SetStorage::Unnormalized { normalized, .. } => {
            assert!(normalized.get().is_none(), "from_iter should stay lazy");
        }
        SetStorage::Normalized(_) => panic!("from_iter should not eagerly normalize"),
    }

    assert!(set.contains(&Value::int(2)));

    match &set.storage {
        SetStorage::Unnormalized { normalized, .. } => {
            assert!(
                normalized.get().is_none(),
                "membership-only checks should not populate normalized cache"
            );
        }
        SetStorage::Normalized(_) => panic!("from_iter should still be lazy after contains"),
    }

    // len() should NOT force normalization — it uses FxHashSet dedup counting.
    assert_eq!(set.len(), 3);

    match &set.storage {
        SetStorage::Unnormalized { normalized, .. } => {
            assert!(
                normalized.get().is_none(),
                "len() should not force normalization"
            );
        }
        SetStorage::Normalized(_) => panic!("from_iter should still be lazy after len()"),
    }

    let elements: Vec<_> = set.iter().cloned().collect();
    assert_eq!(elements, vec![Value::int(1), Value::int(2), Value::int(3)]);
    // After iter(), len() should still return the correct value.
    assert_eq!(set.len(), 3);

    match &set.storage {
        SetStorage::Unnormalized { normalized, .. } => {
            assert!(
                normalized.get().is_some(),
                "ordered observation should populate normalized cache"
            );
        }
        SetStorage::Normalized(_) => panic!("from_iter should keep raw storage variant"),
    }
}

#[test]
fn equality_and_hash_use_normalized_view() {
    let lazy = SortedSet::from_iter(vec![Value::int(2), Value::int(1), Value::int(2)]);
    let eager = SortedSet::from_sorted_vec(vec![Value::int(1), Value::int(2)]);

    assert_eq!(lazy, eager);
    assert_eq!(hash_sorted_set(&lazy), hash_sorted_set(&eager));
    assert_eq!(lazy.as_slice(), eager.as_slice());
}

#[test]
fn canonical_sorted_operations_reuse_small_set_interning() {
    clear_set_intern_table();

    let base = SortedSet::from_sorted_vec(vec![Value::int(1), Value::int(2)]);
    let inserted = base.insert(Value::int(3));
    let eager = SortedSet::from_sorted_vec(vec![Value::int(1), Value::int(2), Value::int(3)]);
    assert!(
        inserted.ptr_eq(&eager),
        "normalized insert results should reuse interned small-set storage"
    );

    let union = base.union(&SortedSet::from_sorted_vec(vec![
        Value::int(2),
        Value::int(3),
    ]));
    assert!(
        union.ptr_eq(&eager),
        "normalized union results should reuse interned small-set storage"
    );

    clear_set_intern_table();
}

#[test]
fn len_does_not_force_normalization_on_unnormalized_set() {
    // Construct an unnormalized set with duplicates.
    let set = SortedSet::from_iter(vec![
        Value::int(5),
        Value::int(3),
        Value::int(5),
        Value::int(1),
        Value::int(3),
    ]);

    // Verify storage is unnormalized.
    assert!(
        !matches!(set.storage, SetStorage::Normalized(_)),
        "from_iter should produce Unnormalized storage"
    );

    // len() should return the deduplicated count.
    assert_eq!(set.len(), 3, "len() should count unique elements");

    // Verify normalization was NOT triggered.
    match &set.storage {
        SetStorage::Unnormalized { normalized, .. } => {
            assert!(
                normalized.get().is_none(),
                "len() must not force normalization"
            );
        }
        SetStorage::Normalized(_) => panic!("len() should not have caused normalization"),
    }

    // Calling len() again should return the cached value.
    assert_eq!(set.len(), 3, "cached len should be stable");
}

#[test]
fn len_after_normalization_returns_correct_count() {
    let set = SortedSet::from_iter(vec![Value::int(2), Value::int(2), Value::int(1)]);

    // Force normalization by iterating.
    let _: Vec<_> = set.iter().cloned().collect();

    // len() should still return the correct deduplicated count.
    assert_eq!(set.len(), 2);
}

#[test]
fn equality_fast_exit_on_different_cardinality() {
    // Two sets with different cardinalities should fail equality quickly
    // via the len() check without needing full normalization of both.
    let small = SortedSet::from_iter(vec![Value::int(1), Value::int(2)]);
    let large = SortedSet::from_iter(vec![Value::int(1), Value::int(2), Value::int(3)]);

    assert_ne!(small, large);

    // At most one of them should have been normalized — the one whose len()
    // was computed first might trigger normalization on the other, but ideally
    // the cardinality mismatch is caught before any normalization.
    // We can at least verify the answer is correct.
}

#[test]
fn compute_dedup_len_small_set_quadratic_path() {
    // 2-8 elements use quadratic scan instead of HashSet.
    let elements = vec![Value::int(1), Value::int(2), Value::int(1), Value::int(3)];
    assert_eq!(SortedSet::compute_dedup_len(&elements), 3);
}

#[test]
fn compute_dedup_len_large_set_hashset_path() {
    // >8 elements use FxHashSet path.
    let elements: Vec<Value> = (0..20)
        .map(|i| Value::int(i % 7)) // 20 elements, 7 unique
        .collect();
    assert_eq!(SortedSet::compute_dedup_len(&elements), 7);
}

#[test]
fn normalized_set_has_dedup_len_set_eagerly() {
    let set = SortedSet::from_sorted_vec(vec![Value::int(1), Value::int(2), Value::int(3)]);

    // Normalized sets should have cached_dedup_len set eagerly.
    assert_eq!(
        set.cached_dedup_len.load(AtomicOrdering::Relaxed),
        3,
        "from_sorted_vec should eagerly set cached_dedup_len"
    );
    assert_eq!(set.len(), 3);
}
