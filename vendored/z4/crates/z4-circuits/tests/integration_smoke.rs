// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use z4_circuits::{Circuit, CircuitAnalyzer, TruthTable};

#[test]
fn xor2_circuit_matches_parity_truth_table() {
    let circuit = Circuit::xor2(2, 0, 1);
    let parity = TruthTable::parity(2);

    assert!(CircuitAnalyzer::computes(&circuit, &parity));
    assert_eq!(CircuitAnalyzer::truth_table(&circuit), parity);
    assert_eq!(CircuitAnalyzer::size(&circuit), 1);
}

#[test]
fn identity_circuit_tracks_selected_input() {
    let circuit = Circuit::identity(3, 1);
    let table = TruthTable::variable(3, 1);

    assert!(CircuitAnalyzer::computes(&circuit, &table));
}
