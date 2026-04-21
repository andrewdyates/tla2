// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_oracle_properties() {
    let pspace = Oracle::new(OracleType::PSPACE);
    assert!(pspace.separates_p_np());
    assert!(!pspace.collapses_p_np());

    let tally = Oracle::new(OracleType::TallyNP);
    assert!(!tally.separates_p_np());
    assert!(tally.collapses_p_np());

    let random = Oracle::new(OracleType::Random);
    assert!(random.separates_p_np());
    assert!(!random.collapses_p_np());
}

#[test]
fn test_finite_field() {
    let f2 = FiniteField::prime(2);
    assert_eq!(f2.size(), 2);

    let f16 = FiniteField {
        characteristic: 2,
        extension_degree: 4,
    };
    assert_eq!(f16.size(), 16);

    let f125 = FiniteField {
        characteristic: 5,
        extension_degree: 3,
    };
    assert_eq!(f125.size(), 125);
}

#[test]
fn test_algebraic_oracle() {
    let ao = AlgebraicOracle::standard();
    assert_eq!(ao.degree_bound, 1);
    assert_eq!(ao.field.characteristic, 2);
}
