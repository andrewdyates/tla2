// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_proof_sketch_builder() {
    let proof = ProofSketch::new(ComplexityClass::P, ComplexityClass::NP)
        .with_technique(ProofTechnique::Diagonalization)
        .with_technique(ProofTechnique::Simulation)
        .with_property(FunctionProperty::HighCircuitComplexity)
        .with_description("Attempt to separate P from NP");

    assert!(proof.techniques.contains(&ProofTechnique::Diagonalization));
    assert!(proof.techniques.contains(&ProofTechnique::Simulation));
    assert!(proof
        .function_properties
        .contains(&FunctionProperty::HighCircuitComplexity));
}

#[test]
fn test_relativizing_techniques() {
    let proof = ProofSketch::new(ComplexityClass::P, ComplexityClass::NP)
        .with_technique(ProofTechnique::Diagonalization)
        .with_technique(ProofTechnique::Simulation);

    assert!(proof.uses_relativizing_techniques());
    assert!(!proof.uses_non_relativizing_techniques());

    let proof2 = ProofSketch::new(ComplexityClass::P, ComplexityClass::PSPACE)
        .with_technique(ProofTechnique::InteractiveProof)
        .with_technique(ProofTechnique::Arithmetization);

    assert!(proof2.uses_non_relativizing_techniques());
}

#[test]
fn test_natural_properties() {
    let proof = ProofSketch::new(ComplexityClass::AC0, ComplexityClass::P)
        .with_property(FunctionProperty::HighCircuitComplexity)
        .with_property(FunctionProperty::LowCorrelation);

    assert!(proof.uses_natural_properties());

    let proof2 = ProofSketch::new(ComplexityClass::P, ComplexityClass::NP)
        .with_property(FunctionProperty::Specific("PARITY".into()));

    assert!(!proof2.uses_natural_properties());
}

#[test]
fn test_complexity_class_containment() {
    assert!(ComplexityClass::P.contained_in(&ComplexityClass::NP));
    assert!(ComplexityClass::P.contained_in(&ComplexityClass::PSPACE));
    assert!(ComplexityClass::NP.contained_in(&ComplexityClass::PH));
    assert!(ComplexityClass::AC0.contained_in(&ComplexityClass::TC0));
    assert!(ComplexityClass::TC0.contained_in(&ComplexityClass::NC));
    assert!(!ComplexityClass::NP.contained_in(&ComplexityClass::P));
}

#[test]
fn test_technique_relativizes() {
    assert!(ProofTechnique::Diagonalization.relativizes());
    assert!(ProofTechnique::Simulation.relativizes());
    assert!(!ProofTechnique::InteractiveProof.relativizes());
    assert!(!ProofTechnique::Arithmetization.relativizes());
}
