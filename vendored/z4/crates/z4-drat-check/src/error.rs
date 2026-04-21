// Copyright 2026 Andrew Yates
// Typed error enums for DRAT proof parsing and checking.
// Mirrors z4-lrat-check's LratParseError pattern.

use thiserror::Error;

/// Errors from parsing DRAT proof files (text or binary format).
#[derive(Debug, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum DratParseError {
    #[error("invalid DRAT literal: {detail}")]
    InvalidLiteral { detail: String },

    #[error("invalid binary DRAT encoding at offset {offset}: {detail}")]
    InvalidBinary { offset: usize, detail: String },

    #[error("invalid UTF-8 in text DRAT: {detail}")]
    InvalidUtf8 { detail: String },

    #[error("{0}")]
    Common(#[from] z4_proof_common::ParseError),
}

/// Errors from DRAT proof checking (forward or backward).
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum DratCheckError {
    /// A derived clause is neither RUP nor RAT implied.
    #[error("clause not {kind}implied: {clause} (step {step})")]
    NotImplied {
        clause: String,
        step: u64,
        kind: &'static str,
    },

    /// A step in full proof verification failed.
    #[error("step {step}: {source}")]
    StepFailed {
        step: usize,
        #[source]
        source: Box<Self>,
    },

    /// Proof conclusion failed (no empty clause, or step failures).
    #[error("{0}")]
    ConclusionFailed(#[from] super::checker::ConcludeFailure),
}
