// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_synthesize_constant() {
    let tt = TruthTable::constant(2, true);
    let circuit = CircuitSynthesizer::synthesize_minimum(&tt, 5).unwrap();
    assert!(CircuitAnalyzer::computes(&circuit, &tt));
    assert_eq!(CircuitAnalyzer::size(&circuit), 0); // Constant needs no gates
}

#[test]
fn test_synthesize_identity() {
    let tt = TruthTable::variable(2, 0);
    let circuit = CircuitSynthesizer::synthesize_minimum(&tt, 5).unwrap();
    assert!(CircuitAnalyzer::computes(&circuit, &tt));
    assert_eq!(CircuitAnalyzer::size(&circuit), 0); // Identity needs no gates
}

#[test]
fn test_synthesize_not() {
    let tt = TruthTable::variable(2, 0).negate();
    let circuit = CircuitSynthesizer::synthesize_minimum(&tt, 5).unwrap();
    assert!(CircuitAnalyzer::computes(&circuit, &tt));
    assert_eq!(CircuitAnalyzer::size(&circuit), 1); // NOT needs 1 gate
}

#[test]
fn test_synthesize_and() {
    let tt = TruthTable::and_all(2);
    let circuit = CircuitSynthesizer::synthesize_minimum(&tt, 5).unwrap();
    assert!(CircuitAnalyzer::computes(&circuit, &tt));
    assert_eq!(CircuitAnalyzer::size(&circuit), 1); // AND needs 1 gate
}

#[test]
fn test_synthesize_or() {
    let tt = TruthTable::or_all(2);
    let circuit = CircuitSynthesizer::synthesize_minimum(&tt, 5).unwrap();
    assert!(CircuitAnalyzer::computes(&circuit, &tt));
    assert_eq!(CircuitAnalyzer::size(&circuit), 1); // OR needs 1 gate
}

#[test]
fn test_synthesize_xor() {
    let tt = TruthTable::from_fn(2, |inputs| inputs[0] ^ inputs[1]);
    let circuit = CircuitSynthesizer::synthesize_minimum(&tt, 5).unwrap();
    assert!(CircuitAnalyzer::computes(&circuit, &tt));
    // XOR can be done with 1 XOR gate
    assert!(CircuitAnalyzer::size(&circuit) <= 1);
}

#[test]
fn test_enumerate_circuits() {
    // Enumerate circuits with 1 input and 1 gate
    let circuits: Vec<_> = CircuitSynthesizer::enumerate_circuits(1, 1).collect();
    // 4 gate types, 1 possible input for each = 4 circuits
    assert_eq!(circuits.len(), 4);

    // Verify each circuit is valid
    for circuit in &circuits {
        assert_eq!(circuit.num_inputs(), 1);
        assert_eq!(CircuitAnalyzer::size(circuit), 1);
    }
}

#[test]
fn test_enumerate_circuits_2_inputs_1_gate() {
    // NOT: 2 inputs = 2 choices
    // AND/OR/XOR: 2 inputs each, 2*2 = 4 choices each, 3*4 = 12
    // Total: 2 + 12 = 14
    assert_eq!(CircuitSynthesizer::enumerate_circuits(2, 1).count(), 14);
}

#[test]
fn test_sat_synthesize_simple() {
    let tt = TruthTable::and_all(2);
    let gate_types = vec![SimpleGateType::Not, SimpleGateType::And, SimpleGateType::Or];
    let circuit = CircuitSynthesizer::sat_synthesize(&tt, 1, &gate_types).unwrap();
    assert!(CircuitAnalyzer::computes(&circuit, &tt));
}
