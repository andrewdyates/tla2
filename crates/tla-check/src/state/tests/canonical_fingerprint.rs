// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::helpers::create_swap_permutation;
use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compute_canonical_fingerprint_from_array_symmetry_invariant() {
    let registry = VarRegistry::from_names(["x", "y"]);
    let val_a1 = Value::try_model_value("a1").unwrap();
    let val_a2 = Value::try_model_value("a2").unwrap();

    let perm = create_swap_permutation("a1", "a2");
    let mvperm = MVPerm::from_func_value(&perm).unwrap();
    let mvperms = vec![mvperm];

    let values1 = vec![val_a1.clone(), val_a2.clone()];
    let values2 = vec![val_a2, val_a1];

    let fp1 = compute_canonical_fingerprint_from_array(&values1, &registry, &mvperms);
    let fp2 = compute_canonical_fingerprint_from_array(&values2, &registry, &mvperms);

    assert_eq!(
        fp1, fp2,
        "Symmetric value arrays must produce same canonical fingerprint"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compute_canonical_fingerprint_from_array_matches_state_method() {
    let registry = VarRegistry::from_names(["x", "y"]);
    let val_a1 = Value::try_model_value("a1").unwrap();
    let val_a2 = Value::try_model_value("a2").unwrap();

    let perm = create_swap_permutation("a1", "a2");
    let mvperm = MVPerm::from_func_value(&perm).unwrap();
    let mvperms = vec![mvperm];

    let values = vec![val_a1.clone(), val_a2.clone()];
    let fp_array = compute_canonical_fingerprint_from_array(&values, &registry, &mvperms);

    let state = State::from_pairs([("x", val_a1), ("y", val_a2)]);
    let fp_state = state.fingerprint_with_symmetry_fast(&mvperms);

    assert_eq!(
        fp_array, fp_state,
        "Array-based and State-based canonical fingerprints must agree"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_early_exit_finds_true_minimum() {
    let perm = create_swap_permutation("a1", "a2");
    let mvperm = MVPerm::from_func_value(&perm).unwrap();
    let mvperms = vec![mvperm];

    let s1 = State::from_pairs([
        ("x", Value::try_model_value("a2").unwrap()),
        ("y", Value::try_model_value("a1").unwrap()),
        ("z", Value::try_model_value("a1").unwrap()),
    ]);
    let s2 = State::from_pairs([
        ("x", Value::try_model_value("a1").unwrap()),
        ("y", Value::try_model_value("a2").unwrap()),
        ("z", Value::try_model_value("a2").unwrap()),
    ]);

    let fp1 = s1.fingerprint_with_symmetry_fast(&mvperms);
    let fp2 = s2.fingerprint_with_symmetry_fast(&mvperms);

    assert_eq!(
        fp1, fp2,
        "Orbit members must share canonical fingerprint (3-var early-exit test)"
    );

    let registry = VarRegistry::from_names(["x", "y", "z"]);
    let vals1 = vec![
        Value::try_model_value("a2").unwrap(),
        Value::try_model_value("a1").unwrap(),
        Value::try_model_value("a1").unwrap(),
    ];
    let vals2 = vec![
        Value::try_model_value("a1").unwrap(),
        Value::try_model_value("a2").unwrap(),
        Value::try_model_value("a2").unwrap(),
    ];
    let fp_arr1 = compute_canonical_fingerprint_from_array(&vals1, &registry, &mvperms);
    let fp_arr2 = compute_canonical_fingerprint_from_array(&vals2, &registry, &mvperms);
    assert_eq!(
        fp_arr1, fp_arr2,
        "Array path: orbit members must share canonical fp"
    );
    assert_eq!(fp1, fp_arr1, "State and array paths must agree");
}
