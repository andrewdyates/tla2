// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Oracle types for relativization and algebrization barriers.
//!
//! An oracle is a "black box" that a Turing machine can query in one step.
//! Different oracles can make complexity class separations true or false.

/// An oracle for complexity theory.
///
/// Oracles are used to study which proof techniques relativize.
/// Baker-Gill-Solovay showed that there exist oracles A and B such that:
/// - P^A = NP^A (classes collapse relative to A)
/// - P^B ≠ NP^B (classes separate relative to B)
#[derive(Debug, Clone)]
pub struct Oracle {
    /// The type of oracle.
    pub oracle_type: OracleType,
    /// Description of the oracle's behavior.
    pub description: String,
}

impl Oracle {
    /// Create a new oracle of the given type.
    pub fn new(oracle_type: OracleType) -> Self {
        let description = oracle_type.description().to_string();
        Self {
            oracle_type,
            description,
        }
    }

    /// Check if this oracle makes P = NP.
    pub fn collapses_p_np(&self) -> bool {
        matches!(self.oracle_type, OracleType::TallyNP | OracleType::SAT)
    }

    /// Check if this oracle separates P from NP.
    pub fn separates_p_np(&self) -> bool {
        matches!(self.oracle_type, OracleType::PSPACE | OracleType::Random)
    }
}

/// Types of oracles used in relativization arguments.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OracleType {
    /// A PSPACE-complete oracle (separates P from NP).
    PSPACE,
    /// A random oracle (separates P from NP with probability 1).
    Random,
    /// A "tally" oracle that makes SAT easy (collapses P = NP).
    TallyNP,
    /// The SAT oracle (collapses P = NP).
    SAT,
}

impl OracleType {
    /// Get a description of this oracle type.
    pub fn description(&self) -> &'static str {
        match self {
            Self::PSPACE => "PSPACE-complete language (QBF). P^PSPACE ≠ NP^PSPACE.",
            Self::Random => "Random oracle. P^R ≠ NP^R with probability 1.",
            Self::TallyNP => "Tally encoding of SAT. P^A = NP^A.",
            Self::SAT => "SAT oracle. P^SAT = NP^SAT = Sigma_2^p.",
        }
    }
}

/// An algebraic oracle for algebrization barriers.
///
/// Aaronson-Wigderson (2009) introduced algebrization as an extension of
/// relativization. Instead of arbitrary oracles, algebraic oracles are
/// low-degree polynomial extensions of Boolean functions.
#[derive(Debug, Clone)]
pub struct AlgebraicOracle {
    /// The finite field over which the oracle is defined.
    pub field: FiniteField,
    /// The degree bound of the polynomial extension.
    pub degree_bound: usize,
    /// Description of the algebraic oracle.
    pub description: String,
}

impl AlgebraicOracle {
    /// Create a new algebraic oracle.
    pub fn new(field: FiniteField, degree_bound: usize) -> Self {
        Self {
            field,
            degree_bound,
            description: format!(
                "Degree-{} extension over F_{}",
                degree_bound, field.characteristic
            ),
        }
    }

    /// Create the standard algebraic oracle used in algebrization results.
    pub fn standard() -> Self {
        Self {
            field: FiniteField::prime(2),
            degree_bound: 1,
            description: "Standard low-degree extension".into(),
        }
    }
}

/// A finite field specification.
#[derive(Debug, Clone, Copy)]
pub struct FiniteField {
    /// The characteristic of the field (a prime number).
    pub characteristic: u64,
    /// The extension degree (field has p^k elements).
    pub extension_degree: u32,
}

impl FiniteField {
    /// Create a prime field F_p.
    pub fn prime(p: u64) -> Self {
        Self {
            characteristic: p,
            extension_degree: 1,
        }
    }

    /// Get the size of the field.
    pub fn size(&self) -> u128 {
        u128::from(self.characteristic).pow(self.extension_degree)
    }
}

#[cfg(test)]
#[path = "oracle_tests.rs"]
mod tests;
