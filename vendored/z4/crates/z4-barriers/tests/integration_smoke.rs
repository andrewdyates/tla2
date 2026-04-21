// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use z4_barriers::{BarrierChecker, ComplexityClass, FunctionProperty, ProofSketch, ProofTechnique};

#[test]
fn detects_relativization_for_p_vs_np_relativizing_proof() {
    let checker = BarrierChecker::new();
    let sketch = ProofSketch::new(ComplexityClass::P, ComplexityClass::NP)
        .with_technique(ProofTechnique::Diagonalization)
        .with_technique(ProofTechnique::Simulation);

    let barriers = checker.check_all(&sketch);
    assert!(barriers.iter().any(z4_barriers::Barrier::is_relativization));
}

#[test]
fn detects_natural_proof_barrier_for_circuit_bound_attempt() {
    let checker = BarrierChecker::new();
    let sketch = ProofSketch::new(ComplexityClass::P, ComplexityClass::PPoly)
        .with_technique(ProofTechnique::RandomRestriction)
        .with_property(FunctionProperty::HighCircuitComplexity)
        .with_circuit_bound();

    let barriers = checker.check_all(&sketch);
    assert!(barriers.iter().any(z4_barriers::Barrier::is_natural_proof));
}
