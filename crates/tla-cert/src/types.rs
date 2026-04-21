// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Type definitions for the TLA+ proof certificate system.

use serde::{Deserialize, Serialize};

/// A proof certificate that can be independently verified
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Certificate {
    /// Unique identifier for this proof
    pub id: String,
    /// The goal that was proven
    pub goal: Formula,
    /// Hypotheses assumed in the proof
    pub hypotheses: Vec<Formula>,
    /// The proof steps
    pub steps: Vec<CertificateStep>,
    /// Backend that generated this certificate
    pub backend: Backend,
}

/// A single step in a proof certificate
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertificateStep {
    /// Unique ID for this step
    pub id: StepId,
    /// The formula established by this step
    pub formula: Formula,
    /// Justification for this step
    pub justification: Justification,
}

/// Identifier for a proof step
pub type StepId = u32;

/// Justification for a proof step
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Justification {
    /// An axiom (built-in logical truth)
    Axiom(Axiom),
    /// Hypothesis (assumed true)
    Hypothesis(usize),
    /// Modus ponens: from P and P => Q, derive Q
    ModusPonens {
        premise: StepId,
        implication: StepId,
    },
    /// Universal instantiation: from ∀x. P(x), derive P(t)
    UniversalInstantiation { forall: StepId, term: Term },
    /// Existential introduction: from P(t), derive ∃x. P(x)
    ExistentialIntro { witness: StepId, variable: String },
    /// Definition expansion
    Definition { name: String },
    /// Conjunction introduction: from P and Q, derive P ∧ Q
    AndIntro { left: StepId, right: StepId },
    /// Conjunction elimination (left): from P ∧ Q, derive P
    AndElimLeft { conjunction: StepId },
    /// Conjunction elimination (right): from P ∧ Q, derive Q
    AndElimRight { conjunction: StepId },
    /// Disjunction introduction (left): from P, derive P ∨ Q
    OrIntroLeft { premise: StepId, right: Formula },
    /// Disjunction introduction (right): from Q, derive P ∨ Q
    OrIntroRight { left: Formula, premise: StepId },
    /// Double negation elimination: from ¬¬P, derive P
    DoubleNegElim { premise: StepId },
    /// Rewrite using equality: from a = b and P(a), derive P(b)
    Rewrite { equality: StepId, target: StepId },
    /// Tableau decomposition: a formula derived from a premise by a sound
    /// tableau rule (alpha/beta/gamma/delta). The prover guarantees soundness;
    /// the checker verifies that the premise step exists.
    TableauDecomposition { premise: StepId },
}

/// Built-in axioms
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Axiom {
    /// P ∨ ¬P (excluded middle)
    ExcludedMiddle(Formula),
    /// P → P (identity)
    Identity(Formula),
    /// P → (Q → P) (weakening)
    Weakening,
    /// a = a (reflexivity)
    EqualityRefl,
    /// a = b → b = a (symmetry)
    EqualitySym,
    /// a = b ∧ b = c → a = c (transitivity)
    EqualityTrans,
    /// Basic arithmetic axiom
    Arithmetic(ArithmeticAxiom),
    /// Set theory axiom
    SetTheory(SetAxiom),
}

/// Arithmetic axioms
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ArithmeticAxiom {
    /// 0 + a = a
    AddZero,
    /// a + b = b + a
    AddComm,
    /// (a + b) + c = a + (b + c)
    AddAssoc,
    /// a * 1 = a
    MulOne,
    /// a * 0 = 0
    MulZero,
}

/// Set theory axioms
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SetAxiom {
    /// x ∈ {} ↔ FALSE
    EmptySet,
    /// x ∈ {a} ↔ x = a
    Singleton,
    /// x ∈ S ∪ T ↔ x ∈ S ∨ x ∈ T
    Union,
    /// x ∈ S ∩ T ↔ x ∈ S ∧ x ∈ T
    Intersection,
}

/// First-order formula
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Formula {
    /// Propositional constant
    Bool(bool),
    /// Predicate application
    Predicate(String, Vec<Term>),
    /// Negation
    Not(Box<Formula>),
    /// Conjunction
    And(Box<Formula>, Box<Formula>),
    /// Disjunction
    Or(Box<Formula>, Box<Formula>),
    /// Implication
    Implies(Box<Formula>, Box<Formula>),
    /// Equivalence
    Equiv(Box<Formula>, Box<Formula>),
    /// Universal quantification
    Forall(String, Box<Formula>),
    /// Existential quantification
    Exists(String, Box<Formula>),
    /// Equality
    Eq(Term, Term),
}

/// First-order term
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Term {
    /// Variable
    Var(String),
    /// Constant
    Const(String),
    /// Integer literal
    Int(i64),
    /// Function application
    App(String, Vec<Term>),
}

/// Backend that generated the certificate
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Backend {
    Zenon,
    Z3,
    CVC5,
    Lean4,
}

/// Result of certificate verification
#[derive(Debug, Serialize, Deserialize)]
pub enum VerificationResult {
    /// Certificate is valid
    Valid,
    /// Certificate is invalid
    Invalid(VerificationError),
}

/// Errors during certificate verification
#[derive(Debug, Serialize, Deserialize)]
pub enum VerificationError {
    /// Referenced step doesn't exist
    UnknownStep(StepId),
    /// Justification doesn't match formula
    InvalidJustification { step: StepId, reason: String },
    /// Final step doesn't match goal
    GoalMismatch,
    /// Invalid axiom application
    InvalidAxiom(String),
}

// ============================================================================
// Serialization
// ============================================================================

/// Error type for certificate I/O operations
#[derive(Debug)]
pub enum CertificateIoError {
    /// JSON serialization/deserialization error
    Json(serde_json::Error),
    /// File I/O error
    Io(std::io::Error),
}

impl std::fmt::Display for CertificateIoError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Json(e) => write!(f, "JSON error: {}", e),
            Self::Io(e) => write!(f, "I/O error: {}", e),
        }
    }
}

impl std::error::Error for CertificateIoError {}

impl From<serde_json::Error> for CertificateIoError {
    fn from(e: serde_json::Error) -> Self {
        Self::Json(e)
    }
}

impl From<std::io::Error> for CertificateIoError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

impl Certificate {
    /// Serialize the certificate to JSON
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    /// Serialize the certificate to pretty-printed JSON
    pub fn to_json_pretty(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Deserialize a certificate from JSON
    pub fn from_json(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }

    /// Save the certificate to a file as JSON
    pub fn save_to_file(
        &self,
        path: impl AsRef<std::path::Path>,
    ) -> Result<(), CertificateIoError> {
        let json = self.to_json_pretty()?;
        std::fs::write(path, json)?;
        Ok(())
    }

    /// Load a certificate from a JSON file
    pub fn load_from_file(path: impl AsRef<std::path::Path>) -> Result<Self, CertificateIoError> {
        let json = std::fs::read_to_string(path)?;
        let cert = Self::from_json(&json)?;
        Ok(cert)
    }
}

impl VerificationResult {
    /// Returns true if the verification was successful
    pub fn is_valid(&self) -> bool {
        matches!(self, Self::Valid)
    }

    /// Returns the error if verification failed
    pub fn error(&self) -> Option<&VerificationError> {
        match self {
            Self::Valid => None,
            Self::Invalid(e) => Some(e),
        }
    }
}
