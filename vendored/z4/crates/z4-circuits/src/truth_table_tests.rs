// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_constant() {
    let t = TruthTable::constant(2, true);
    assert!(t.evaluate(&[false, false]));
    assert!(t.evaluate(&[true, true]));
    assert!(t.is_constant());
    assert!(t.is_true());

    let f = TruthTable::constant(2, false);
    assert!(!f.evaluate(&[false, false]));
    assert!(f.is_constant());
    assert!(f.is_false());
}

#[test]
fn test_variable() {
    let x0 = TruthTable::variable(2, 0);
    assert!(!x0.evaluate(&[false, false]));
    assert!(x0.evaluate(&[true, false]));
    assert!(!x0.evaluate(&[false, true]));
    assert!(x0.evaluate(&[true, true]));

    let x1 = TruthTable::variable(2, 1);
    assert!(!x1.evaluate(&[false, false]));
    assert!(!x1.evaluate(&[true, false]));
    assert!(x1.evaluate(&[false, true]));
    assert!(x1.evaluate(&[true, true]));
}

#[test]
fn test_and_all() {
    let and = TruthTable::and_all(3);
    assert!(!and.evaluate(&[false, false, false]));
    assert!(!and.evaluate(&[true, true, false]));
    assert!(and.evaluate(&[true, true, true]));
}

#[test]
fn test_or_all() {
    let or = TruthTable::or_all(3);
    assert!(!or.evaluate(&[false, false, false]));
    assert!(or.evaluate(&[true, false, false]));
    assert!(or.evaluate(&[true, true, true]));
}

#[test]
fn test_parity() {
    let xor = TruthTable::parity(3);
    assert!(!xor.evaluate(&[false, false, false])); // 0
    assert!(xor.evaluate(&[true, false, false])); // 1
    assert!(xor.evaluate(&[false, true, false])); // 1
    assert!(!xor.evaluate(&[true, true, false])); // 0
    assert!(xor.evaluate(&[false, false, true])); // 1
    assert!(!xor.evaluate(&[true, false, true])); // 0
    assert!(!xor.evaluate(&[false, true, true])); // 0
    assert!(xor.evaluate(&[true, true, true])); // 1
}

#[test]
fn test_majority() {
    let maj = TruthTable::majority(3);
    assert!(!maj.evaluate(&[false, false, false]));
    assert!(!maj.evaluate(&[true, false, false]));
    assert!(maj.evaluate(&[true, true, false]));
    assert!(maj.evaluate(&[true, true, true]));
}

#[test]
fn test_depends_on() {
    let x0 = TruthTable::variable(3, 0);
    assert!(x0.depends_on(0));
    assert!(!x0.depends_on(1));
    assert!(!x0.depends_on(2));

    let and = TruthTable::and_all(3);
    assert!(and.depends_on(0));
    assert!(and.depends_on(1));
    assert!(and.depends_on(2));

    let c = TruthTable::constant(3, true);
    assert!(!c.depends_on(0));
    assert!(!c.depends_on(1));
    assert!(!c.depends_on(2));
}

#[test]
fn test_essential_variables() {
    let x0 = TruthTable::variable(3, 0);
    assert_eq!(x0.essential_variables(), vec![0]);

    let and = TruthTable::and_all(3);
    assert_eq!(and.essential_variables(), vec![0, 1, 2]);
}

#[test]
fn test_operations() {
    let x0 = TruthTable::variable(2, 0);
    let x1 = TruthTable::variable(2, 1);

    // x0 AND x1
    let and = x0.and(&x1);
    assert!(!and.evaluate(&[false, false]));
    assert!(!and.evaluate(&[true, false]));
    assert!(!and.evaluate(&[false, true]));
    assert!(and.evaluate(&[true, true]));

    // x0 OR x1
    let or = x0.or(&x1);
    assert!(!or.evaluate(&[false, false]));
    assert!(or.evaluate(&[true, false]));
    assert!(or.evaluate(&[false, true]));
    assert!(or.evaluate(&[true, true]));

    // x0 XOR x1
    let xor = x0.xor(&x1);
    assert!(!xor.evaluate(&[false, false]));
    assert!(xor.evaluate(&[true, false]));
    assert!(xor.evaluate(&[false, true]));
    assert!(!xor.evaluate(&[true, true]));
}

#[test]
fn test_negate() {
    let x0 = TruthTable::variable(2, 0);
    let not_x0 = x0.negate();
    assert!(not_x0.evaluate(&[false, false]));
    assert!(!not_x0.evaluate(&[true, false]));
}

#[test]
fn test_weight() {
    let x0 = TruthTable::variable(2, 0);
    assert_eq!(x0.weight(), 2); // True for 2 of 4 inputs

    let and = TruthTable::and_all(2);
    assert_eq!(and.weight(), 1); // True only for (1,1)

    let or = TruthTable::or_all(2);
    assert_eq!(or.weight(), 3); // True for all except (0,0)
}
