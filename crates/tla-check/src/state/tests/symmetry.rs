// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::helpers::{create_cycle_permutation, create_swap_permutation};
use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_canonical_fingerprint_invariant() {
    let perm = create_swap_permutation("a1", "a2");

    let s1 = State::from_pairs([
        ("x", Value::try_model_value("a1").unwrap()),
        ("y", Value::try_model_value("a2").unwrap()),
    ]);
    let s2 = State::from_pairs([
        ("x", Value::try_model_value("a2").unwrap()),
        ("y", Value::try_model_value("a1").unwrap()),
    ]);

    let s1_permuted = s1.permute(&perm);
    assert_eq!(s1_permuted.vars, s2.vars, "S2 should equal permute(S1, P)");

    let s2_permuted = s2.permute(&perm);
    assert_eq!(s2_permuted.vars, s1.vars, "S1 should equal permute(S2, P)");

    let perms = vec![perm];
    let fp1 = s1.fingerprint_with_symmetry(&perms);
    let fp2 = s2.fingerprint_with_symmetry(&perms);

    assert_eq!(
        fp1, fp2,
        "Symmetric states must have same canonical fingerprint!\n\
         S1 = {{x: a1, y: a2}}, fp = {:?}\n\
         S2 = {{x: a2, y: a1}}, fp = {:?}\n\
         These states are in the same orbit under the swap permutation.",
        fp1, fp2
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_array_state_symmetry_canonical_fingerprint_invariant_mvperm() {
    let registry = VarRegistry::from_names(["x", "y"]);
    let val_a1 = Value::try_model_value("a1").unwrap();
    let val_a2 = Value::try_model_value("a2").unwrap();

    let perm = create_swap_permutation("a1", "a2");
    let mvperm = MVPerm::from_func_value(&perm).unwrap();
    let mvperms = vec![mvperm];

    let mut arr1 = ArrayState::new(2);
    arr1.set(VarIndex(0), val_a1.clone());
    arr1.set(VarIndex(1), val_a2.clone());

    let mut arr2 = ArrayState::new(2);
    arr2.set(VarIndex(0), val_a2.clone());
    arr2.set(VarIndex(1), val_a1.clone());

    let s1 = arr1.to_state(&registry);
    let s2 = arr2.to_state(&registry);

    assert_eq!(s1.permute(&perm).vars, s2.vars);
    assert_eq!(s2.permute(&perm).vars, s1.vars);

    assert_eq!(
        s1.fingerprint_with_symmetry_fast(&mvperms),
        s2.fingerprint_with_symmetry_fast(&mvperms)
    );

    let s_slow = State::from_pairs([("x", val_a1.clone()), ("y", val_a2.clone())]);
    let s_fast = State::from_pairs([("x", val_a1), ("y", val_a2)]);
    assert_eq!(
        s_slow.fingerprint_with_symmetry(&[perm]),
        s_fast.fingerprint_with_symmetry_fast(&mvperms)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_three_element_orbit() {
    let perm_cycle = create_cycle_permutation("a1", "a2", "a3");
    let perm_cycle2 = create_cycle_permutation("a1", "a3", "a2");

    let s1 = State::from_pairs([
        ("x", Value::try_model_value("a1").unwrap()),
        ("y", Value::try_model_value("a2").unwrap()),
        ("z", Value::try_model_value("a3").unwrap()),
    ]);
    let s2 = State::from_pairs([
        ("x", Value::try_model_value("a2").unwrap()),
        ("y", Value::try_model_value("a3").unwrap()),
        ("z", Value::try_model_value("a1").unwrap()),
    ]);
    let s3 = State::from_pairs([
        ("x", Value::try_model_value("a3").unwrap()),
        ("y", Value::try_model_value("a1").unwrap()),
        ("z", Value::try_model_value("a2").unwrap()),
    ]);

    assert_eq!(s1.permute(&perm_cycle).vars, s2.vars);
    assert_eq!(s2.permute(&perm_cycle).vars, s3.vars);
    assert_eq!(s3.permute(&perm_cycle).vars, s1.vars);

    assert_eq!(s1.permute(&perm_cycle2).vars, s3.vars);
    assert_eq!(s2.permute(&perm_cycle2).vars, s1.vars);
    assert_eq!(s3.permute(&perm_cycle2).vars, s2.vars);

    let perms = vec![perm_cycle.clone(), perm_cycle2.clone()];

    let fp1 = s1.fingerprint_with_symmetry(&perms);
    let fp2 = s2.fingerprint_with_symmetry(&perms);
    let fp3 = s3.fingerprint_with_symmetry(&perms);

    assert_eq!(
        fp1, fp2,
        "States in same orbit must have same canonical fingerprint (S1 vs S2)"
    );
    assert_eq!(
        fp2, fp3,
        "States in same orbit must have same canonical fingerprint (S2 vs S3)"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_different_orbits_different_fingerprints() {
    let perm = create_swap_permutation("a1", "a2");

    let s1 = State::from_pairs([
        ("x", Value::try_model_value("a1").unwrap()),
        ("y", Value::try_model_value("a2").unwrap()),
    ]);
    let s2 = State::from_pairs([
        ("x", Value::try_model_value("a2").unwrap()),
        ("y", Value::try_model_value("a1").unwrap()),
    ]);
    let s3 = State::from_pairs([
        ("x", Value::try_model_value("a1").unwrap()),
        ("y", Value::try_model_value("a1").unwrap()),
    ]);

    let perms = vec![perm];

    let fp1 = s1.fingerprint_with_symmetry(&perms);
    let fp2 = s2.fingerprint_with_symmetry(&perms);
    let fp3 = s3.fingerprint_with_symmetry(&perms);

    assert_eq!(fp1, fp2, "Same orbit must have same fingerprint");
    assert_ne!(
        fp1, fp3,
        "Different orbits should have different fingerprints"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_empty_permutations() {
    let s = State::from_pairs([("x", Value::int(42))]);

    let fp_regular = s.fingerprint();
    let fp_symmetry = s.fingerprint_with_symmetry(&[]);

    assert_eq!(fp_regular, fp_symmetry);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_nested_structures() {
    let perm = create_swap_permutation("a1", "a2");

    let set1 = Value::set(vec![Value::try_model_value("a1").unwrap()]);
    let set2 = Value::set(vec![Value::try_model_value("a2").unwrap()]);

    let s1 = State::from_pairs([("votes", set1.clone()), ("decided", set2.clone())]);
    let s2 = State::from_pairs([("votes", set2), ("decided", set1)]);

    let perms = vec![perm];

    let s1_permuted = s1.permute(&perms[0]);
    assert_eq!(s1_permuted.vars, s2.vars, "S2 = permute(S1)");

    let fp1 = s1.fingerprint_with_symmetry(&perms);
    let fp2 = s2.fingerprint_with_symmetry(&perms);

    assert_eq!(
        fp1, fp2,
        "Symmetric states with nested structures must have same canonical fingerprint"
    );
}
