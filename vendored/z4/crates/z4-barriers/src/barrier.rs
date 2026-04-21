// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Barrier types representing the three known obstacles to P vs NP separation.

use crate::oracle::{AlgebraicOracle, Oracle};

/// The three main barriers to complexity class separations.
///
/// These barriers explain why certain proof techniques fundamentally cannot
/// separate P from NP (or other pairs of complexity classes).
#[derive(Debug, Clone)]
pub enum Barrier {
    /// The proof technique relativizes.
    ///
    /// A proof technique "relativizes" if it would still work when all machines
    /// have access to an oracle. Baker-Gill-Solovay (1975) showed:
    /// - There exists oracle A such that P^A = NP^A
    /// - There exists oracle B such that P^B ≠ NP^B
    ///
    /// Therefore, any proof that relativizes cannot separate P from NP.
    Relativization(RelativizationBarrier),

    /// The proof uses "natural" properties in the sense of Razborov-Rudich.
    ///
    /// A lower bound proof is "natural" if it uses a property that is:
    /// 1. **Large**: Holds for at least 1/poly(n) fraction of n-input Boolean functions
    /// 2. **Constructive**: Can be tested in poly(2^n) time
    ///
    /// Razborov-Rudich (1997) showed: If secure pseudorandom generators exist,
    /// natural proofs cannot prove super-polynomial lower bounds against P/poly.
    NaturalProof(NaturalProofBarrier),

    /// The proof algebrizes.
    ///
    /// Aaronson-Wigderson (2009) extended relativization to algebraic settings.
    /// A proof "algebrizes" if it still works when the oracle is replaced by
    /// a low-degree polynomial extension over a finite field.
    ///
    /// Known algebrizing results: IP = PSPACE, MIP = NEXP, etc.
    /// No known technique avoids both relativization and algebrization.
    Algebrization(AlgebrizationBarrier),
}

impl Barrier {
    /// Check if this is a relativization barrier.
    pub fn is_relativization(&self) -> bool {
        matches!(self, Self::Relativization(_))
    }

    /// Check if this is a natural proof barrier.
    pub fn is_natural_proof(&self) -> bool {
        matches!(self, Self::NaturalProof(_))
    }

    /// Check if this is an algebrization barrier.
    pub fn is_algebrization(&self) -> bool {
        matches!(self, Self::Algebrization(_))
    }

    /// Get a reference to recommended techniques that avoid this barrier.
    pub fn workarounds(&self) -> &'static [&'static str] {
        match self {
            Self::Relativization(_) => &[
                "Interactive proofs (IP=PSPACE is non-relativizing)",
                "Arithmetization",
                "Algebraic techniques",
                "Circuit lower bounds (may still hit natural proofs)",
            ],
            Self::NaturalProof(_) => &[
                "Use non-constructive properties",
                "Use properties not large over random functions",
                "Focus on specific hard functions (not generic separations)",
                "Ryan Williams's approach (algorithmic -> lower bounds)",
            ],
            Self::Algebrization(_) => &[
                "No known general technique avoids algebrization",
                "May need fundamentally new ideas",
                "Geometric Complexity Theory (GCT) is conjectured non-algebrizing",
            ],
        }
    }
}

/// Detailed information about a relativization barrier.
#[derive(Debug, Clone)]
pub struct RelativizationBarrier {
    /// Oracle that makes the separation true (e.g., PSPACE-complete oracle for P≠NP).
    pub separating_oracle: Oracle,
    /// Oracle that makes the classes collapse (e.g., oracle where P=NP).
    pub collapsing_oracle: Oracle,
    /// Which techniques in the proof are oracle-independent.
    pub relativizing_techniques: Vec<String>,
}

impl RelativizationBarrier {
    /// Create a new relativization barrier.
    pub fn new(
        separating_oracle: Oracle,
        collapsing_oracle: Oracle,
        relativizing_techniques: Vec<String>,
    ) -> Self {
        Self {
            separating_oracle,
            collapsing_oracle,
            relativizing_techniques,
        }
    }
}

/// Detailed information about a natural proof barrier.
#[derive(Debug, Clone)]
pub struct NaturalProofBarrier {
    /// Whether the proof uses a "large" property.
    pub uses_largeness: bool,
    /// Whether the property is efficiently constructive.
    pub uses_constructivity: bool,
    /// Description of the natural property being used.
    pub property_description: String,
    /// The fraction of functions satisfying the property (if known).
    pub largeness_fraction: Option<f64>,
}

impl NaturalProofBarrier {
    /// Create a new natural proof barrier.
    pub fn new(
        uses_largeness: bool,
        uses_constructivity: bool,
        property_description: String,
    ) -> Self {
        Self {
            uses_largeness,
            uses_constructivity,
            property_description,
            largeness_fraction: None,
        }
    }

    /// Set the largeness fraction.
    pub fn with_largeness_fraction(mut self, fraction: f64) -> Self {
        self.largeness_fraction = Some(fraction);
        self
    }

    /// Check if this is a "fully natural" proof (both large and constructive).
    pub fn is_fully_natural(&self) -> bool {
        self.uses_largeness && self.uses_constructivity
    }
}

/// Detailed information about an algebrization barrier.
#[derive(Debug, Clone)]
pub struct AlgebrizationBarrier {
    /// The algebraic oracle that breaks the separation.
    pub algebraic_oracle: AlgebraicOracle,
    /// Which techniques in the proof algebrize.
    pub algebrizing_techniques: Vec<String>,
}

impl AlgebrizationBarrier {
    /// Create a new algebrization barrier.
    pub fn new(algebraic_oracle: AlgebraicOracle, algebrizing_techniques: Vec<String>) -> Self {
        Self {
            algebraic_oracle,
            algebrizing_techniques,
        }
    }
}

#[cfg(test)]
#[path = "barrier_tests.rs"]
mod tests;
