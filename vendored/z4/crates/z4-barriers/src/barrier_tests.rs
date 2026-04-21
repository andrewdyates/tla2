// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::oracle::OracleType;

#[test]
fn test_barrier_type_checks() {
    let rel = Barrier::Relativization(RelativizationBarrier::new(
        Oracle::new(OracleType::PSPACE),
        Oracle::new(OracleType::TallyNP),
        vec!["diagonalization".into()],
    ));
    assert!(rel.is_relativization());
    assert!(!rel.is_natural_proof());
    assert!(!rel.is_algebrization());

    let nat = Barrier::NaturalProof(NaturalProofBarrier::new(
        true,
        true,
        "random restriction".into(),
    ));
    assert!(!nat.is_relativization());
    assert!(nat.is_natural_proof());
    assert!(!nat.is_algebrization());
}

#[test]
fn test_natural_proof_fully_natural() {
    let np1 = NaturalProofBarrier::new(true, true, "test".into());
    assert!(np1.is_fully_natural());

    let np2 = NaturalProofBarrier::new(true, false, "test".into());
    assert!(!np2.is_fully_natural());

    let np3 = NaturalProofBarrier::new(false, true, "test".into());
    assert!(!np3.is_fully_natural());
}
