// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof sketch representation for barrier analysis.
//!
//! A proof sketch captures the essential characteristics of a proof attempt
//! that are relevant for detecting barriers.

use std::collections::HashSet;

/// A sketch of a proof attempt for barrier analysis.
///
/// This captures the key characteristics of a proof strategy that determine
/// which barriers it might hit.
#[derive(Debug, Clone)]
pub struct ProofSketch {
    /// The lower complexity class being separated.
    pub lower_class: ComplexityClass,
    /// The upper complexity class being separated.
    pub upper_class: ComplexityClass,
    /// Techniques used in the proof.
    pub techniques: HashSet<ProofTechnique>,
    /// Properties of the hard function being used.
    pub function_properties: HashSet<FunctionProperty>,
    /// Whether the proof aims to show circuit lower bounds.
    pub proves_circuit_bound: bool,
    /// Description of the proof strategy.
    pub description: String,
}

impl ProofSketch {
    /// Create a new proof sketch attempting to separate two complexity classes.
    pub fn new(lower: ComplexityClass, upper: ComplexityClass) -> Self {
        Self {
            lower_class: lower,
            upper_class: upper,
            techniques: HashSet::new(),
            function_properties: HashSet::new(),
            proves_circuit_bound: false,
            description: String::new(),
        }
    }

    /// Add a proof technique.
    pub fn with_technique(mut self, technique: ProofTechnique) -> Self {
        self.techniques.insert(technique);
        self
    }

    /// Add a function property.
    pub fn with_property(mut self, property: FunctionProperty) -> Self {
        self.function_properties.insert(property);
        self
    }

    /// Mark that this proof shows a circuit lower bound.
    pub fn with_circuit_bound(mut self) -> Self {
        self.proves_circuit_bound = true;
        self
    }

    /// Set a description.
    pub fn with_description(mut self, desc: impl Into<String>) -> Self {
        self.description = desc.into();
        self
    }

    /// Check if the proof uses any relativizing techniques.
    pub fn uses_relativizing_techniques(&self) -> bool {
        self.techniques.iter().any(ProofTechnique::relativizes)
    }

    /// Check if the proof uses techniques known to not relativize.
    pub fn uses_non_relativizing_techniques(&self) -> bool {
        self.techniques.iter().any(|t| !t.relativizes())
    }

    /// Check if the proof uses natural properties.
    pub fn uses_natural_properties(&self) -> bool {
        self.function_properties
            .iter()
            .any(|p| p.is_large() && p.is_constructive())
    }

    /// Get the list of relativizing techniques used.
    pub fn relativizing_techniques(&self) -> Vec<&ProofTechnique> {
        self.techniques.iter().filter(|t| t.relativizes()).collect()
    }

    /// Get the list of natural properties used.
    pub fn natural_properties(&self) -> Vec<&FunctionProperty> {
        self.function_properties
            .iter()
            .filter(|p| p.is_large() && p.is_constructive())
            .collect()
    }
}

/// Complexity classes for separation results.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ComplexityClass {
    /// Polynomial time.
    P,
    /// Nondeterministic polynomial time.
    NP,
    /// co-NP.
    CoNP,
    /// Polynomial space.
    PSPACE,
    /// Exponential time.
    EXP,
    /// Nondeterministic exponential time.
    NEXP,
    /// Bounded-error probabilistic polynomial time.
    BPP,
    /// Polynomial hierarchy.
    PH,
    /// NC (efficient parallel computation).
    NC,
    /// L (logarithmic space).
    L,
    /// NL (nondeterministic logarithmic space).
    NL,
    /// AC0 (constant-depth circuits).
    AC0,
    /// TC0 (constant-depth circuits with threshold gates).
    TC0,
    /// P/poly (polynomial-size circuits).
    PPoly,
}

impl ComplexityClass {
    /// Check if this class is contained in another.
    pub fn contained_in(&self, other: &Self) -> bool {
        use ComplexityClass::{CoNP, PPoly, AC0, BPP, EXP, L, NC, NL, NP, P, PH, PSPACE, TC0};
        match (self, other) {
            // Same class
            (a, b) if a == b => true,
            // Everything is in PSPACE and EXP
            (_, PSPACE | EXP) => true,
            // P ⊆ NP, coNP, BPP, PH, P/poly
            (P, NP | CoNP | BPP | PH | PPoly) => true,
            // NP, coNP ⊆ PH
            (NP | CoNP, PH) => true,
            // L ⊆ NL ⊆ P
            (L, NL | P | NP | CoNP | BPP | PH | PPoly) => true,
            (NL, P | NP | CoNP | BPP | PH | PPoly) => true,
            // AC0 ⊆ TC0 ⊆ NC ⊆ P
            (AC0, TC0 | NC | P | NP | CoNP | BPP | PH | PPoly) => true,
            (TC0, NC | P | NP | CoNP | BPP | PH | PPoly) => true,
            (NC, P | NP | CoNP | BPP | PH | PPoly) => true,
            _ => false,
        }
    }

    /// Get the name of this class.
    pub fn name(&self) -> &'static str {
        match self {
            Self::P => "P",
            Self::NP => "NP",
            Self::CoNP => "coNP",
            Self::PSPACE => "PSPACE",
            Self::EXP => "EXP",
            Self::NEXP => "NEXP",
            Self::BPP => "BPP",
            Self::PH => "PH",
            Self::NC => "NC",
            Self::L => "L",
            Self::NL => "NL",
            Self::AC0 => "AC0",
            Self::TC0 => "TC0",
            Self::PPoly => "P/poly",
        }
    }
}

/// Proof techniques used in complexity separations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProofTechnique {
    /// Diagonalization (a la Cantor/Turing/Time hierarchy).
    Diagonalization,
    /// Simulation argument (showing one class can simulate another).
    Simulation,
    /// Padding argument (reducing from one problem to another by padding).
    Padding,
    /// Counting argument (pigeonhole, probabilistic method).
    Counting,
    /// Random restriction (Furst-Saxe-Sipser, Hastad).
    RandomRestriction,
    /// Switching lemma.
    SwitchingLemma,
    /// Polynomial method (e.g., for communication complexity).
    PolynomialMethod,
    /// Approximation method (Razborov).
    ApproximationMethod,
    /// Adversary argument (information-theoretic).
    AdversaryArgument,
    /// Interactive proof techniques.
    InteractiveProof,
    /// Arithmetization (used in IP=PSPACE).
    Arithmetization,
    /// Communication complexity reduction.
    CommunicationComplexity,
    /// Game-theoretic argument (prover-delayer games).
    GameTheoretic,
    /// Algebraic techniques (GCT, etc.).
    Algebraic,
}

impl ProofTechnique {
    /// Check if this technique relativizes.
    ///
    /// A technique relativizes if adding an oracle to all machines
    /// doesn't affect whether the proof works.
    pub fn relativizes(&self) -> bool {
        match self {
            // These techniques all relativize
            Self::Diagonalization => true,
            Self::Simulation => true,
            Self::Padding => true,
            Self::Counting => true,
            Self::AdversaryArgument => true,
            Self::GameTheoretic => true,
            // These techniques may not relativize
            Self::RandomRestriction => true, // Still relativizes (circuit lower bounds)
            Self::SwitchingLemma => true,
            Self::PolynomialMethod => false, // Can be non-relativizing
            Self::ApproximationMethod => true,
            Self::InteractiveProof => false, // IP=PSPACE doesn't relativize
            Self::Arithmetization => false,  // Core of IP=PSPACE
            Self::CommunicationComplexity => true,
            Self::Algebraic => false, // May avoid barriers
        }
    }

    /// Check if this technique algebrizes.
    ///
    /// A technique algebrizes if replacing the oracle with a low-degree
    /// polynomial extension over a finite field doesn't break the proof.
    /// Aaronson-Wigderson (2009).
    pub fn algebrizes(&self) -> bool {
        match self {
            // Techniques that relativize generally also algebrize
            Self::Diagonalization => true,
            Self::Simulation => true,
            Self::Padding => true,
            Self::Counting => true,
            Self::AdversaryArgument => true,
            // IP and arithmetization algebrize (but don't relativize)
            Self::InteractiveProof => true,
            Self::Arithmetization => true,
            // Circuit techniques
            Self::RandomRestriction => true,
            Self::SwitchingLemma => true,
            Self::ApproximationMethod => true,
            // Polynomial method may not algebrize in some settings
            Self::PolynomialMethod => false,
            Self::CommunicationComplexity => true,
            Self::GameTheoretic => true,
            // Algebraic techniques (GCT) are conjectured to not algebrize
            Self::Algebraic => false,
        }
    }
}

/// Properties of functions used in lower bound proofs.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FunctionProperty {
    /// Function has high circuit complexity.
    HighCircuitComplexity,
    /// Function has low correlation with small circuits.
    LowCorrelation,
    /// Function is hard for random restrictions.
    HardForRestrictions,
    /// Function has high sensitivity.
    HighSensitivity,
    /// Function has high block sensitivity.
    HighBlockSensitivity,
    /// Function has high degree (as polynomial).
    HighDegree,
    /// Function is a specific function (not generic).
    Specific(String),
    /// Custom property with description.
    Custom {
        /// Human-readable property name.
        name: String,
        /// Whether the property holds for many functions.
        large: bool,
        /// Whether the property is efficiently testable.
        constructive: bool,
    },
}

impl FunctionProperty {
    /// Check if this property is "large" (holds for many functions).
    ///
    /// A property is large if at least 1/poly(n) of all n-input Boolean
    /// functions satisfy it.
    pub fn is_large(&self) -> bool {
        match self {
            // Most generic hardness properties are large
            Self::HighCircuitComplexity => true,
            Self::LowCorrelation => true,
            Self::HardForRestrictions => true,
            Self::HighSensitivity => true,
            Self::HighBlockSensitivity => true,
            Self::HighDegree => true,
            // Specific functions are not large (only one function)
            Self::Specific(_) => false,
            Self::Custom { large, .. } => *large,
        }
    }

    /// Check if this property is constructive (efficiently testable).
    ///
    /// A property is constructive if it can be tested in poly(2^n) time.
    pub fn is_constructive(&self) -> bool {
        match self {
            // Circuit complexity is constructive (enumerate circuits)
            Self::HighCircuitComplexity => true,
            // Correlation can be computed
            Self::LowCorrelation => true,
            // Restriction hardness is constructive
            Self::HardForRestrictions => true,
            // Sensitivity is polynomial time
            Self::HighSensitivity => true,
            Self::HighBlockSensitivity => true,
            // Degree is polynomial time
            Self::HighDegree => true,
            // Specific functions: checking is efficient
            Self::Specific(_) => true,
            Self::Custom { constructive, .. } => *constructive,
        }
    }

    /// Get the name of this property.
    pub fn name(&self) -> String {
        match self {
            Self::HighCircuitComplexity => "high circuit complexity".into(),
            Self::LowCorrelation => "low correlation with small circuits".into(),
            Self::HardForRestrictions => "hardness under restrictions".into(),
            Self::HighSensitivity => "high sensitivity".into(),
            Self::HighBlockSensitivity => "high block sensitivity".into(),
            Self::HighDegree => "high polynomial degree".into(),
            Self::Specific(name) => format!("specific function: {name}"),
            Self::Custom { name, .. } => name.clone(),
        }
    }
}

#[cfg(test)]
#[path = "proof_sketch_tests.rs"]
mod tests;
