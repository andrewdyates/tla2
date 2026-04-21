// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_size() {
    let c = Circuit::and2(2, 0, 1);
    assert_eq!(CircuitAnalyzer::size(&c), 1);

    // XOR using AND, OR, NOT
    let mut c = Circuit::new(2);
    let x = c.input(0);
    let y = c.input(1);
    let not_x = c.add_gate(Gate::Not(x));
    let not_y = c.add_gate(Gate::Not(y));
    let x_and_not_y = c.add_gate(Gate::And(x, not_y));
    let not_x_and_y = c.add_gate(Gate::And(not_x, y));
    let xor = c.add_gate(Gate::Or(x_and_not_y, not_x_and_y));
    c.set_output(xor);
    assert_eq!(CircuitAnalyzer::size(&c), 5);
}

#[test]
fn test_depth() {
    // Single AND gate: depth 1
    let c = Circuit::and2(2, 0, 1);
    assert_eq!(CircuitAnalyzer::depth(&c), 1);

    // Identity: depth 0
    let c = Circuit::identity(2, 0);
    assert_eq!(CircuitAnalyzer::depth(&c), 0);

    // Chain: NOT(NOT(NOT(x)))
    let mut c = Circuit::new(1);
    let x = c.input(0);
    let not1 = c.add_gate(Gate::Not(x));
    let not2 = c.add_gate(Gate::Not(not1));
    let not3 = c.add_gate(Gate::Not(not2));
    c.set_output(not3);
    assert_eq!(CircuitAnalyzer::depth(&c), 3);
}

#[test]
fn test_computes() {
    let c = Circuit::and2(2, 0, 1);
    let and_tt = TruthTable::and_all(2);
    assert!(CircuitAnalyzer::computes(&c, &and_tt));

    let or_tt = TruthTable::or_all(2);
    assert!(!CircuitAnalyzer::computes(&c, &or_tt));
}

#[test]
fn test_truth_table() {
    let c = Circuit::xor2(2, 0, 1);
    let tt = CircuitAnalyzer::truth_table(&c);
    let expected = TruthTable::from_fn(2, |inputs| inputs[0] ^ inputs[1]);
    assert_eq!(tt, expected);
}

#[test]
fn test_equivalent() {
    // Two different XOR implementations
    let c1 = Circuit::xor2(2, 0, 1);

    // XOR using AND, OR, NOT: (x AND NOT y) OR (NOT x AND y)
    let mut c2 = Circuit::new(2);
    let x = c2.input(0);
    let y = c2.input(1);
    let not_x = c2.add_gate(Gate::Not(x));
    let not_y = c2.add_gate(Gate::Not(y));
    let x_and_not_y = c2.add_gate(Gate::And(x, not_y));
    let not_x_and_y = c2.add_gate(Gate::And(not_x, y));
    let xor = c2.add_gate(Gate::Or(x_and_not_y, not_x_and_y));
    c2.set_output(xor);

    assert!(CircuitAnalyzer::equivalent(&c1, &c2));
}

#[test]
fn test_is_in_class_ac0() {
    // Simple AND/OR circuit is AC0
    let c = Circuit::and2(2, 0, 1);
    assert!(CircuitAnalyzer::is_in_class(&c, CircuitClass::AC0));
    assert!(CircuitAnalyzer::is_in_class(&c, CircuitClass::ACC0));
    assert!(CircuitAnalyzer::is_in_class(&c, CircuitClass::TC0));
    assert!(CircuitAnalyzer::is_in_class(&c, CircuitClass::PPoly));
}

#[test]
fn test_is_in_class_tc0() {
    // Circuit with threshold gate
    let mut c = Circuit::new(3);
    let inputs = vec![c.input(0), c.input(1), c.input(2)];
    let maj = c.add_gate(Gate::Threshold {
        inputs,
        threshold: 2,
    });
    c.set_output(maj);

    assert!(!CircuitAnalyzer::is_in_class(&c, CircuitClass::AC0));
    assert!(!CircuitAnalyzer::is_in_class(&c, CircuitClass::ACC0));
    assert!(CircuitAnalyzer::is_in_class(&c, CircuitClass::TC0));
    assert!(CircuitAnalyzer::is_in_class(&c, CircuitClass::PPoly));
}

#[test]
fn test_is_in_class_acc0() {
    // Circuit with mod gate
    let mut c = Circuit::new(3);
    let inputs = vec![c.input(0), c.input(1), c.input(2)];
    let mod3 = c.add_gate(Gate::Mod { inputs, modulus: 3 });
    c.set_output(mod3);

    assert!(!CircuitAnalyzer::is_in_class(&c, CircuitClass::AC0));
    assert!(CircuitAnalyzer::is_in_class(&c, CircuitClass::ACC0));
    // Note: ACC0 ⊆ TC0, but we don't implement that implication in is_in_class
    assert!(CircuitAnalyzer::is_in_class(&c, CircuitClass::PPoly));
}

#[test]
fn test_gate_counts() {
    let mut c = Circuit::new(2);
    let x = c.input(0);
    let y = c.input(1);
    let not_x = c.add_gate(Gate::Not(x));
    let and = c.add_gate(Gate::And(x, y));
    let or = c.add_gate(Gate::Or(not_x, and));
    c.set_output(or);

    let counts = CircuitAnalyzer::gate_counts(&c);
    assert_eq!(counts.inputs, 2);
    assert_eq!(counts.not, 1);
    assert_eq!(counts.and2, 1);
    assert_eq!(counts.or2, 1);
    assert_eq!(counts.total_gates(), 3);
}

#[test]
fn test_max_fan_in() {
    // Binary gates have fan-in 2
    let c = Circuit::and2(2, 0, 1);
    assert_eq!(CircuitAnalyzer::max_fan_in(&c), 2);

    // N-ary gate
    let mut c = Circuit::new(4);
    let inputs = vec![c.input(0), c.input(1), c.input(2), c.input(3)];
    let and4 = c.add_gate(Gate::NaryAnd(inputs));
    c.set_output(and4);
    assert_eq!(CircuitAnalyzer::max_fan_in(&c), 4);
}
