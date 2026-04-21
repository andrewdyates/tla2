// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Barrier checking implementation.
//!
//! The BarrierChecker analyzes proof sketches to detect which barriers
//! the proof attempt hits.

use crate::barrier::{AlgebrizationBarrier, Barrier, NaturalProofBarrier, RelativizationBarrier};
use crate::oracle::{AlgebraicOracle, Oracle, OracleType};
use crate::proof_sketch::{ComplexityClass, ProofSketch};

/// Checker for P vs NP barriers.
///
/// This analyzes proof sketches and detects which barriers they hit.
#[derive(Debug, Clone, Default)]
pub struct BarrierChecker {
    /// Configuration options.
    config: BarrierCheckerConfig,
}

/// Configuration for barrier checking.
#[derive(Debug, Clone)]
pub struct BarrierCheckerConfig {
    /// Whether to check relativization.
    pub check_relativization: bool,
    /// Whether to check natural proofs.
    pub check_natural_proofs: bool,
    /// Whether to check algebrization.
    pub check_algebrization: bool,
}

impl Default for BarrierCheckerConfig {
    fn default() -> Self {
        Self {
            check_relativization: true,
            check_natural_proofs: true,
            check_algebrization: true,
        }
    }
}

impl BarrierChecker {
    /// Create a new barrier checker with default configuration.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a barrier checker with custom configuration.
    pub fn with_config(config: BarrierCheckerConfig) -> Self {
        Self { config }
    }

    /// Run all barrier checks on a proof sketch.
    pub fn check_all(&self, proof: &ProofSketch) -> Vec<Barrier> {
        let mut barriers = Vec::new();

        if self.config.check_relativization {
            if let Some(b) = self.check_relativization(proof) {
                barriers.push(b);
            }
        }

        if self.config.check_natural_proofs {
            if let Some(b) = self.check_natural_proof(proof) {
                barriers.push(b);
            }
        }

        if self.config.check_algebrization {
            if let Some(b) = self.check_algebrization(proof) {
                barriers.push(b);
            }
        }

        barriers
    }

    /// Check if the proof technique relativizes.
    ///
    /// Returns a Relativization barrier if the proof uses only oracle-independent
    /// techniques for a separation that is oracle-dependent.
    pub fn check_relativization(&self, proof: &ProofSketch) -> Option<Barrier> {
        // Check if the proof uses only relativizing techniques
        if !proof.uses_relativizing_techniques() {
            return None;
        }

        // If there are also non-relativizing techniques, it might escape
        if proof.uses_non_relativizing_techniques() {
            return None;
        }

        // Check if the separation is oracle-sensitive
        if !Self::is_oracle_sensitive_separation(&proof.lower_class, &proof.upper_class) {
            return None;
        }

        // Find appropriate oracles for the separation
        let (separating, collapsing) =
            Self::find_oracles_for_separation(&proof.lower_class, &proof.upper_class);

        let relativizing_techniques = proof
            .relativizing_techniques()
            .iter()
            .map(|t| format!("{t:?}"))
            .collect();

        Some(Barrier::Relativization(RelativizationBarrier::new(
            separating,
            collapsing,
            relativizing_techniques,
        )))
    }

    /// Check if the proof uses natural properties.
    ///
    /// Returns a NaturalProof barrier if the proof uses properties that are
    /// both large (hold for many functions) and constructive (efficiently testable).
    pub fn check_natural_proof(&self, proof: &ProofSketch) -> Option<Barrier> {
        // Only relevant if proving circuit lower bounds
        if !proof.proves_circuit_bound {
            return None;
        }

        // Only relevant if separating from P/poly
        if !matches!(
            proof.upper_class,
            ComplexityClass::PPoly | ComplexityClass::P | ComplexityClass::NP
        ) {
            return None;
        }

        // Check for natural properties
        let natural_props = proof.natural_properties();
        if natural_props.is_empty() {
            return None;
        }

        // Build the barrier description
        let property_description = natural_props
            .iter()
            .map(|p| p.name())
            .collect::<Vec<_>>()
            .join(", ");

        let mut barrier =
            NaturalProofBarrier::new(true, true, format!("Uses: {property_description}"));

        // Estimate largeness (rough heuristic)
        barrier = barrier.with_largeness_fraction(0.5); // Most random functions have these properties

        Some(Barrier::NaturalProof(barrier))
    }

    /// Check if the proof algebrizes.
    ///
    /// Returns an Algebrization barrier if the proof techniques would still
    /// work with algebraic oracle extensions.
    pub fn check_algebrization(&self, proof: &ProofSketch) -> Option<Barrier> {
        // Check if the separation is algebrization-sensitive
        if !Self::is_algebrization_sensitive_separation(&proof.lower_class, &proof.upper_class) {
            return None;
        }

        // Check if techniques algebrize
        // Currently, most techniques that relativize also algebrize
        let algebrizing_techniques: Vec<_> =
            proof.techniques.iter().filter(|t| t.algebrizes()).collect();

        if algebrizing_techniques.is_empty() {
            return None;
        }

        // Check if there are non-algebrizing techniques
        let has_non_algebrizing = proof.techniques.iter().any(|t| !t.algebrizes());

        if has_non_algebrizing {
            // Has some non-algebrizing techniques, might escape
            return None;
        }

        let technique_names = algebrizing_techniques
            .iter()
            .map(|t| format!("{t:?}"))
            .collect();

        Some(Barrier::Algebrization(AlgebrizationBarrier::new(
            AlgebraicOracle::standard(),
            technique_names,
        )))
    }

    /// Check if a separation is oracle-sensitive (different oracles give different answers).
    fn is_oracle_sensitive_separation(lower: &ComplexityClass, upper: &ComplexityClass) -> bool {
        use ComplexityClass::{CoNP, BPP, NP, P, PH, PSPACE};

        match (lower, upper) {
            // P vs NP: Baker-Gill-Solovay showed oracle sensitivity
            (P, NP) | (NP, P) => true,
            // NP vs coNP
            (NP, CoNP) | (CoNP, NP) => true,
            // P vs PSPACE: separable relative to all oracles (P^A ≠ PSPACE^A)
            (P, PSPACE) => false,
            // BPP vs NP: oracle sensitive
            (P, BPP) | (BPP, NP) => true,
            // Most separations involving NP are oracle-sensitive
            (_, NP) | (NP, _) => true,
            // PH containments (note: NP, PH already covered above)
            (P | CoNP, PH) => true,
            // Default: assume oracle-sensitive
            _ => true,
        }
    }

    /// Check if a separation is algebrization-sensitive.
    fn is_algebrization_sensitive_separation(
        lower: &ComplexityClass,
        upper: &ComplexityClass,
    ) -> bool {
        use ComplexityClass::{CoNP, PPoly, NEXP, NP, P};

        match (lower, upper) {
            // P vs NP: algebrization-sensitive
            (P, NP) | (NP, P) => true,
            // NP vs coNP: algebrization-sensitive
            (NP, CoNP) | (CoNP, NP) => true,
            // NEXP vs P/poly: IP=PSPACE algebrizes, but separation is unknown
            (NEXP, PPoly) => true,
            // Most are algebrization-sensitive
            _ => true,
        }
    }

    /// Find appropriate oracles for demonstrating relativization sensitivity.
    fn find_oracles_for_separation(
        lower: &ComplexityClass,
        upper: &ComplexityClass,
    ) -> (Oracle, Oracle) {
        use ComplexityClass::{NP, P};

        match (lower, upper) {
            // P vs NP: use PSPACE (separates) and tally (collapses)
            (P, NP) => (
                Oracle::new(OracleType::PSPACE),
                Oracle::new(OracleType::TallyNP),
            ),
            // For other separations, use reasonable defaults
            _ => (
                Oracle::new(OracleType::Random),
                Oracle::new(OracleType::SAT),
            ),
        }
    }

    /// Analyze a proof sketch and provide detailed feedback.
    pub fn analyze(&self, proof: &ProofSketch) -> BarrierAnalysis {
        let barriers = self.check_all(proof);

        let hits_relativization = barriers.iter().any(Barrier::is_relativization);
        let hits_natural_proofs = barriers.iter().any(Barrier::is_natural_proof);
        let hits_algebrization = barriers.iter().any(Barrier::is_algebrization);

        // Determine if the proof has any chance
        let verdict = if barriers.is_empty() {
            BarrierVerdict::Clear
        } else if hits_relativization && hits_natural_proofs && hits_algebrization {
            BarrierVerdict::BlockedByAll
        } else if hits_relativization || hits_algebrization {
            BarrierVerdict::BlockedByOracleBarrier
        } else if hits_natural_proofs {
            BarrierVerdict::BlockedByNaturalProofs
        } else {
            BarrierVerdict::PartiallyBlocked
        };

        // Collect workarounds
        let mut workarounds = Vec::new();
        for barrier in &barriers {
            workarounds.extend(barrier.workarounds().iter().map(ToString::to_string));
        }
        workarounds.sort();
        workarounds.dedup();

        BarrierAnalysis {
            proof_description: proof.description.clone(),
            separation: format!(
                "{} vs {}",
                proof.lower_class.name(),
                proof.upper_class.name()
            ),
            barriers,
            verdict,
            workarounds,
        }
    }
}

/// Result of barrier analysis.
#[derive(Debug, Clone)]
pub struct BarrierAnalysis {
    /// Description of the proof being analyzed.
    pub proof_description: String,
    /// The separation being attempted.
    pub separation: String,
    /// Barriers detected.
    pub barriers: Vec<Barrier>,
    /// Overall verdict.
    pub verdict: BarrierVerdict,
    /// Suggested workarounds.
    pub workarounds: Vec<String>,
}

impl BarrierAnalysis {
    /// Check if the proof is blocked by any barrier.
    pub fn is_blocked(&self) -> bool {
        !matches!(self.verdict, BarrierVerdict::Clear)
    }

    /// Get a summary of the analysis.
    pub fn summary(&self) -> String {
        let status = match &self.verdict {
            BarrierVerdict::Clear => "NO BARRIERS DETECTED",
            BarrierVerdict::BlockedByOracleBarrier => "BLOCKED: Relativization",
            BarrierVerdict::BlockedByNaturalProofs => "BLOCKED: Natural Proofs",
            BarrierVerdict::BlockedByAll => "BLOCKED: All three barriers",
            BarrierVerdict::PartiallyBlocked => "PARTIALLY BLOCKED",
        };

        format!(
            "Barrier Analysis for {}\nSeparation: {}\nVerdict: {}\nBarriers found: {}",
            if self.proof_description.is_empty() {
                "(no description)"
            } else {
                &self.proof_description
            },
            self.separation,
            status,
            self.barriers.len()
        )
    }
}

/// Overall verdict of barrier analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BarrierVerdict {
    /// No barriers detected (proof might work).
    Clear,
    /// Blocked by oracle-based barrier (relativization and/or algebrization).
    BlockedByOracleBarrier,
    /// Blocked by natural proofs barrier.
    BlockedByNaturalProofs,
    /// Blocked by all three barriers.
    BlockedByAll,
    /// Partially blocked (some barriers but might escape).
    PartiallyBlocked,
}

#[cfg(test)]
#[path = "checker_tests.rs"]
mod tests;
