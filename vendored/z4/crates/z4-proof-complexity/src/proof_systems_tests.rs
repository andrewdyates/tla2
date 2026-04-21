// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_resolution_proof() {
    // Prove (A OR B) AND (NOT A OR B) AND (NOT B) is UNSAT
    // Resolution:
    // 1. A OR B (axiom)
    // 2. NOT A OR B (axiom)
    // 3. B (resolve 1,2 on A)
    // 4. NOT B (axiom)
    // 5. empty (resolve 3,4 on B)

    let a = Var::new(0);
    let b = Var::new(1);

    let mut proof = ResolutionProof::new();
    let s1 = proof.add_axiom(vec![Lit::positive(a), Lit::positive(b)]);
    let s2 = proof.add_axiom(vec![Lit::negative(a), Lit::positive(b)]);
    let s3 = proof.add_resolution(vec![Lit::positive(b)], s1, s2, a);
    let s4 = proof.add_axiom(vec![Lit::negative(b)]);
    let _s5 = proof.add_resolution(vec![], s3, s4, b);

    assert!(proof.is_refutation());
    assert!(proof.verify().is_ok());
    assert!(proof.is_tree());
    assert!(proof.is_regular());
    assert_eq!(proof.width(), 2);
}

#[test]
fn test_non_tree_proof() {
    // Reuse a clause: (A) AND (NOT A OR B) AND (NOT A OR NOT B)
    // 1. A (axiom)
    // 2. NOT A OR B (axiom)
    // 3. B (resolve 1,2 on A)
    // 4. NOT A OR NOT B (axiom)
    // 5. NOT B (resolve 1,4 on A) -- reuses clause 1
    // 6. empty (resolve 3,5 on B)

    let a = Var::new(0);
    let b = Var::new(1);

    let mut proof = ResolutionProof::new();
    let s1 = proof.add_axiom(vec![Lit::positive(a)]);
    let s2 = proof.add_axiom(vec![Lit::negative(a), Lit::positive(b)]);
    let s3 = proof.add_resolution(vec![Lit::positive(b)], s1, s2, a);
    let s4 = proof.add_axiom(vec![Lit::negative(a), Lit::negative(b)]);
    let s5 = proof.add_resolution(vec![Lit::negative(b)], s1, s4, a);
    let _s6 = proof.add_resolution(vec![], s3, s5, b);

    assert!(proof.is_refutation());
    assert!(proof.verify().is_ok());
    assert!(!proof.is_tree()); // Clause 1 is used twice
}

#[test]
fn test_proof_system_simulation() {
    use ProofSystem::*;

    // Resolution simulates tree resolution
    assert!(Resolution.p_simulates(&TreeResolution));
    // But tree resolution doesn't simulate resolution
    assert!(!TreeResolution.p_simulates(&Resolution));
    // Extended resolution simulates resolution
    assert!(ExtendedResolution.p_simulates(&Resolution));
}
