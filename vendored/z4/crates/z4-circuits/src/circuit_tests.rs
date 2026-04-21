// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_constant_circuit() {
    let c = Circuit::constant(2, true);
    assert!(c.evaluate_single(&[false, false]));
    assert!(c.evaluate_single(&[true, true]));

    let c = Circuit::constant(2, false);
    assert!(!c.evaluate_single(&[false, false]));
    assert!(!c.evaluate_single(&[true, true]));
}

#[test]
fn test_identity_circuit() {
    let c = Circuit::identity(2, 0);
    assert!(!c.evaluate_single(&[false, true]));
    assert!(c.evaluate_single(&[true, false]));
}

#[test]
fn test_not_circuit() {
    let c = Circuit::not_input(2, 0);
    assert!(c.evaluate_single(&[false, true]));
    assert!(!c.evaluate_single(&[true, false]));
}

#[test]
fn test_and_circuit() {
    let c = Circuit::and2(2, 0, 1);
    assert!(!c.evaluate_single(&[false, false]));
    assert!(!c.evaluate_single(&[true, false]));
    assert!(!c.evaluate_single(&[false, true]));
    assert!(c.evaluate_single(&[true, true]));
}

#[test]
fn test_or_circuit() {
    let c = Circuit::or2(2, 0, 1);
    assert!(!c.evaluate_single(&[false, false]));
    assert!(c.evaluate_single(&[true, false]));
    assert!(c.evaluate_single(&[false, true]));
    assert!(c.evaluate_single(&[true, true]));
}

#[test]
fn test_xor_circuit() {
    let c = Circuit::xor2(2, 0, 1);
    assert!(!c.evaluate_single(&[false, false]));
    assert!(c.evaluate_single(&[true, false]));
    assert!(c.evaluate_single(&[false, true]));
    assert!(!c.evaluate_single(&[true, true]));
}

#[test]
fn test_complex_circuit() {
    // Build (x AND y) OR (NOT x AND NOT y) = XNOR
    let mut c = Circuit::new(2);
    let x = c.input(0);
    let y = c.input(1);
    let not_x = c.add_gate(Gate::Not(x));
    let not_y = c.add_gate(Gate::Not(y));
    let x_and_y = c.add_gate(Gate::And(x, y));
    let not_x_and_not_y = c.add_gate(Gate::And(not_x, not_y));
    let xnor = c.add_gate(Gate::Or(x_and_y, not_x_and_not_y));
    c.set_output(xnor);

    assert!(c.evaluate_single(&[false, false])); // XNOR(0,0) = 1
    assert!(!c.evaluate_single(&[true, false])); // XNOR(1,0) = 0
    assert!(!c.evaluate_single(&[false, true])); // XNOR(0,1) = 0
    assert!(c.evaluate_single(&[true, true])); // XNOR(1,1) = 1
}

#[test]
fn test_threshold_gate() {
    // Majority function: at least 2 of 3 inputs must be true
    let mut c = Circuit::new(3);
    let inputs = vec![c.input(0), c.input(1), c.input(2)];
    let maj = c.add_gate(Gate::Threshold {
        inputs,
        threshold: 2,
    });
    c.set_output(maj);

    assert!(!c.evaluate_single(&[false, false, false])); // 0
    assert!(!c.evaluate_single(&[true, false, false])); // 1
    assert!(!c.evaluate_single(&[false, true, false])); // 1
    assert!(c.evaluate_single(&[true, true, false])); // 2
    assert!(!c.evaluate_single(&[false, false, true])); // 1
    assert!(c.evaluate_single(&[true, false, true])); // 2
    assert!(c.evaluate_single(&[false, true, true])); // 2
    assert!(c.evaluate_single(&[true, true, true])); // 3
}

#[test]
fn test_mod_gate() {
    // MOD3: true iff number of 1s is divisible by 3
    let mut c = Circuit::new(3);
    let inputs = vec![c.input(0), c.input(1), c.input(2)];
    let mod3 = c.add_gate(Gate::Mod { inputs, modulus: 3 });
    c.set_output(mod3);

    assert!(c.evaluate_single(&[false, false, false])); // 0 mod 3 = 0
    assert!(!c.evaluate_single(&[true, false, false])); // 1 mod 3 = 1
    assert!(!c.evaluate_single(&[true, true, false])); // 2 mod 3 = 2
    assert!(c.evaluate_single(&[true, true, true])); // 3 mod 3 = 0
}

#[test]
fn test_nary_and() {
    let mut c = Circuit::new(3);
    let inputs = vec![c.input(0), c.input(1), c.input(2)];
    let and3 = c.add_gate(Gate::NaryAnd(inputs));
    c.set_output(and3);

    assert!(!c.evaluate_single(&[false, false, false]));
    assert!(!c.evaluate_single(&[true, true, false]));
    assert!(c.evaluate_single(&[true, true, true]));
}

#[test]
fn test_nary_or() {
    let mut c = Circuit::new(3);
    let inputs = vec![c.input(0), c.input(1), c.input(2)];
    let or3 = c.add_gate(Gate::NaryOr(inputs));
    c.set_output(or3);

    assert!(!c.evaluate_single(&[false, false, false]));
    assert!(c.evaluate_single(&[true, false, false]));
    assert!(c.evaluate_single(&[true, true, true]));
}

#[test]
#[should_panic(expected = "Mod gate modulus must be positive")]
fn test_mod_gate_rejects_zero_modulus() {
    let mut c = Circuit::new(1);
    let inputs = vec![c.input(0)];
    c.add_gate(Gate::Mod { inputs, modulus: 0 });
}
