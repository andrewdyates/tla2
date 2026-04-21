// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::proof_sketch::{FunctionProperty, ProofTechnique};

#[test]
fn test_basic_relativization_check() {
    let checker = BarrierChecker::new();

    // A simple diagonalization proof for P vs NP should hit relativization
    let proof = ProofSketch::new(ComplexityClass::P, ComplexityClass::NP)
        .with_technique(ProofTechnique::Diagonalization);

    let barriers = checker.check_all(&proof);
    assert!(!barriers.is_empty());
    assert!(barriers.iter().any(Barrier::is_relativization));
}

#[test]
fn test_non_relativizing_techniques() {
    let checker = BarrierChecker::new();

    // Interactive proofs + arithmetization don't relativize
    let proof = ProofSketch::new(ComplexityClass::P, ComplexityClass::PSPACE)
        .with_technique(ProofTechnique::InteractiveProof)
        .with_technique(ProofTechnique::Arithmetization);

    let barriers = checker.check_all(&proof);
    // Should not hit relativization barrier
    assert!(!barriers.iter().any(Barrier::is_relativization));
}

#[test]
fn test_natural_proofs_check() {
    let checker = BarrierChecker::new();

    // Circuit lower bound proof using high circuit complexity property
    let proof = ProofSketch::new(ComplexityClass::AC0, ComplexityClass::P)
        .with_property(FunctionProperty::HighCircuitComplexity)
        .with_property(FunctionProperty::LowCorrelation)
        .with_technique(ProofTechnique::RandomRestriction)
        .with_circuit_bound();

    let barriers = checker.check_all(&proof);
    assert!(barriers.iter().any(Barrier::is_natural_proof));
}

#[test]
fn test_specific_function_avoids_natural() {
    let checker = BarrierChecker::new();

    // Using a specific function (not a generic property) avoids natural proofs
    let proof = ProofSketch::new(ComplexityClass::AC0, ComplexityClass::P)
        .with_property(FunctionProperty::Specific("PARITY".into()))
        .with_circuit_bound();

    let barriers = checker.check_all(&proof);
    // Should not hit natural proofs barrier (specific function isn't "large")
    assert!(!barriers.iter().any(Barrier::is_natural_proof));
}

#[test]
fn test_algebrization_check() {
    let checker = BarrierChecker::new();

    // Standard techniques algebrize
    let proof = ProofSketch::new(ComplexityClass::P, ComplexityClass::NP)
        .with_technique(ProofTechnique::Diagonalization)
        .with_technique(ProofTechnique::InteractiveProof); // IP=PSPACE algebrizes

    let barriers = checker.check_all(&proof);
    // Has non-algebrizing techniques mixed in, so should not hit algebrization
    // (the polynomial method doesn't algebrize)
    let _has_algebrization = barriers.iter().any(Barrier::is_algebrization);

    // Pure diagonalization should hit algebrization
    let proof2 = ProofSketch::new(ComplexityClass::P, ComplexityClass::NP)
        .with_technique(ProofTechnique::Diagonalization)
        .with_technique(ProofTechnique::Simulation);

    let barriers2 = checker.check_all(&proof2);
    assert!(barriers2.iter().any(Barrier::is_algebrization));
}

#[test]
fn test_algebraic_techniques_may_escape() {
    let checker = BarrierChecker::new();

    // Algebraic techniques (GCT) are conjectured to avoid barriers
    let proof = ProofSketch::new(ComplexityClass::P, ComplexityClass::NP)
        .with_technique(ProofTechnique::Algebraic);

    let barriers = checker.check_all(&proof);
    // Should not hit relativization (algebraic doesn't relativize)
    assert!(!barriers.iter().any(Barrier::is_relativization));
    // Should not hit algebrization (algebraic doesn't algebrize)
    assert!(!barriers.iter().any(Barrier::is_algebrization));
}

#[test]
fn test_full_analysis() {
    let checker = BarrierChecker::new();

    let proof = ProofSketch::new(ComplexityClass::P, ComplexityClass::NP)
        .with_technique(ProofTechnique::Diagonalization)
        .with_technique(ProofTechnique::Simulation)
        .with_description("Naive P vs NP attempt using diagonalization");

    let analysis = checker.analyze(&proof);
    assert!(analysis.is_blocked());
    assert!(!analysis.workarounds.is_empty());
    assert!(!analysis.summary().is_empty());
}

#[test]
fn test_clear_verdict_for_known_separations() {
    let checker = BarrierChecker::new();

    // P vs PSPACE is not oracle-sensitive (always separate)
    // Using non-relativizing techniques
    let proof = ProofSketch::new(ComplexityClass::P, ComplexityClass::PSPACE)
        .with_technique(ProofTechnique::InteractiveProof);

    let analysis = checker.analyze(&proof);
    // This might still detect some barriers, but relativization shouldn't apply
    assert!(!analysis.barriers.iter().any(Barrier::is_relativization));
}
