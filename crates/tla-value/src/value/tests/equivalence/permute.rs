// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Value::permute tests for symmetry reduction.

use super::super::super::*;
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_permute_model_value() {
    // Create a permutation: @a |-> @b, @b |-> @a
    let a = Value::try_model_value("a").unwrap();
    let b = Value::try_model_value("b").unwrap();

    let mut fb = FuncBuilder::new();
    fb.insert(a.clone(), b.clone()); // a |-> b
    fb.insert(b.clone(), a.clone()); // b |-> a
    let perm = fb.build();

    // Permuting model values
    assert_eq!(a.permute(&perm), b);
    assert_eq!(b.permute(&perm), a);

    // Model value not in permutation domain - unchanged
    let c = Value::try_model_value("c").unwrap();
    assert_eq!(c.permute(&perm), c);

    // Primitive values - unchanged
    assert_eq!(Value::int(42).permute(&perm), Value::int(42));
    assert_eq!(Value::bool(true).permute(&perm), Value::bool(true));
    assert_eq!(
        Value::string("hello").permute(&perm),
        Value::string("hello")
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_permute_set() {
    let a = Value::try_model_value("a").unwrap();
    let b = Value::try_model_value("b").unwrap();

    let mut fb = FuncBuilder::new();
    fb.insert(a.clone(), b.clone());
    fb.insert(b.clone(), a.clone());
    let perm = fb.build();

    // Set {@a, @b, 1} permuted -> {@b, @a, 1}
    let set = Value::set([a.clone(), b.clone(), Value::int(1)]);
    let permuted = set.permute(&perm);

    // Should have same elements (different order won't matter for set equality)
    let permuted_set = permuted.as_set().unwrap();
    assert_eq!(permuted_set.len(), 3);
    assert!(permuted_set.contains(&a)); // @b permuted is @a
    assert!(permuted_set.contains(&b)); // @a permuted is @b
    assert!(permuted_set.contains(&Value::int(1)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_permute_seq() {
    let a = Value::try_model_value("a").unwrap();
    let b = Value::try_model_value("b").unwrap();

    let mut fb = FuncBuilder::new();
    fb.insert(a.clone(), b.clone());
    fb.insert(b.clone(), a.clone());
    let perm = fb.build();

    // Sequence <<@a, @b, 1>> permuted -> <<@b, @a, 1>>
    let seq = Value::seq([a.clone(), b.clone(), Value::int(1)]);
    let permuted = seq.permute(&perm);

    let permuted_seq = permuted.as_seq().unwrap();
    assert_eq!(permuted_seq.len(), 3);
    assert_eq!(permuted_seq[0], b); // @a -> @b
    assert_eq!(permuted_seq[1], a); // @b -> @a
    assert_eq!(permuted_seq[2], Value::int(1)); // unchanged
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_permute_record() {
    let a = Value::try_model_value("a").unwrap();
    let b = Value::try_model_value("b").unwrap();

    let mut fb = FuncBuilder::new();
    fb.insert(a.clone(), b.clone());
    fb.insert(b.clone(), a.clone());
    let perm = fb.build();

    // Record [x |-> @a, y |-> @b] permuted -> [x |-> @b, y |-> @a]
    let rec = Value::record([("x", a.clone()), ("y", b.clone())]);
    let permuted = rec.permute(&perm);

    let permuted_rec = permuted.as_record().unwrap();
    assert_eq!(permuted_rec.get(&Arc::from("x")), Some(&b));
    assert_eq!(permuted_rec.get(&Arc::from("y")), Some(&a));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_permute_function() {
    let a = Value::try_model_value("a").unwrap();
    let b = Value::try_model_value("b").unwrap();

    let mut fb = FuncBuilder::new();
    fb.insert(a.clone(), b.clone());
    fb.insert(b.clone(), a.clone());
    let perm = fb.build();

    // Function [@a |-> 1, @b |-> 2] permuted -> [@b |-> 1, @a |-> 2]
    let mut fb2 = FuncBuilder::new();
    fb2.insert(a.clone(), Value::int(1));
    fb2.insert(b.clone(), Value::int(2));
    let func = Value::Func(Arc::new(fb2.build()));
    let permuted = func.permute(&perm);

    let permuted_func = permuted.as_func().unwrap();
    // Domain permuted: @a -> @b, @b -> @a
    assert!(permuted_func.domain_contains(&a));
    assert!(permuted_func.domain_contains(&b));
    // [@a |-> 1, @b |-> 2] with permutation (a<->b) gives [@b |-> 1, @a |-> 2]
    assert_eq!(permuted_func.mapping_get(&b), Some(&Value::int(1)));
    assert_eq!(permuted_func.mapping_get(&a), Some(&Value::int(2)));
}

/// Test permuting a function where only values change (keys are integers).
/// Exercises the `key_changed=false, any_changed=true` fast path in
/// `permute_impl` that skips the O(n log n) sort.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_permute_function_value_only_change() {
    let a = Value::try_model_value("a").unwrap();
    let b = Value::try_model_value("b").unwrap();
    let c = Value::try_model_value("c").unwrap();
    let d = Value::try_model_value("d").unwrap();

    // Use a 4-cycle so every value changes while the integer-key order stays
    // the same. Two keys are not enough here because binary search can still
    // succeed accidentally on a length-2 unsorted slice.
    let mut fb = FuncBuilder::new();
    fb.insert(a.clone(), b.clone());
    fb.insert(b.clone(), c.clone());
    fb.insert(c.clone(), d.clone());
    fb.insert(d.clone(), a.clone());
    let perm = fb.build();

    // Function [1 |-> @a, 2 |-> @b, 3 |-> @c, 4 |-> @d] — integer keys,
    // model value values.
    let mut fb2 = FuncBuilder::new();
    fb2.insert(Value::int(1), a.clone());
    fb2.insert(Value::int(2), b.clone());
    fb2.insert(Value::int(3), c.clone());
    fb2.insert(Value::int(4), d.clone());
    let func = Value::Func(Arc::new(fb2.build()));
    let permuted = func.permute(&perm);

    // Keys unchanged, values permuted: @a -> @b -> @c -> @d -> @a.
    let permuted_func = permuted.as_func().unwrap();
    assert_eq!(permuted_func.mapping_get(&Value::int(1)), Some(&b));
    assert_eq!(permuted_func.mapping_get(&Value::int(2)), Some(&c));
    assert_eq!(permuted_func.mapping_get(&Value::int(3)), Some(&d));
    assert_eq!(permuted_func.mapping_get(&Value::int(4)), Some(&a));

    // The fast path is only sound if the original sorted key order is preserved.
    let actual_keys: Vec<Value> = permuted_func
        .mapping_iter()
        .map(|(key, _)| key.clone())
        .collect();
    assert_eq!(
        actual_keys,
        vec![Value::int(1), Value::int(2), Value::int(3), Value::int(4)]
    );

    assert_eq!(permuted_func.domain_len(), 4);
}

/// `permute_fast()` shares the same no-sort function branch as `permute()`,
/// but uses `MVPerm` lookup instead of `FuncValue` lookup.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_permute_fast_function_value_only_change() {
    let a = Value::try_model_value("fast_a").unwrap();
    let b = Value::try_model_value("fast_b").unwrap();
    let c = Value::try_model_value("fast_c").unwrap();
    let d = Value::try_model_value("fast_d").unwrap();

    let mut fb = FuncBuilder::new();
    fb.insert(a.clone(), b.clone());
    fb.insert(b.clone(), c.clone());
    fb.insert(c.clone(), d.clone());
    fb.insert(d.clone(), a.clone());
    let perm = fb.build();
    let fast_perm = MVPerm::from_func_value(&perm).unwrap();

    let mut fb2 = FuncBuilder::new();
    fb2.insert(Value::int(1), a.clone());
    fb2.insert(Value::int(2), b.clone());
    fb2.insert(Value::int(3), c.clone());
    fb2.insert(Value::int(4), d.clone());
    let func = Value::Func(Arc::new(fb2.build()));
    let permuted = func.permute_fast(&fast_perm);

    let permuted_func = permuted.as_func().unwrap();
    assert_eq!(permuted_func.mapping_get(&Value::int(1)), Some(&b));
    assert_eq!(permuted_func.mapping_get(&Value::int(2)), Some(&c));
    assert_eq!(permuted_func.mapping_get(&Value::int(3)), Some(&d));
    assert_eq!(permuted_func.mapping_get(&Value::int(4)), Some(&a));

    let actual_keys: Vec<Value> = permuted_func
        .mapping_iter()
        .map(|(key, _)| key.clone())
        .collect();
    assert_eq!(
        actual_keys,
        vec![Value::int(1), Value::int(2), Value::int(3), Value::int(4)]
    );

    assert_eq!(permuted_func.domain_len(), 4);
}
