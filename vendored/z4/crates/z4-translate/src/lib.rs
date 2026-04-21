// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! # z4-translate: Unified term translation for z4 consumers
//!
//! This crate provides a common translation layer for consumers of z4 (zani, tla2, lean5).
//! It reduces code duplication by extracting shared patterns:
//!
//! - `TranslationSession<V>`: Borrowed session combining solver ref + state (preferred)
//! - `TranslationState<V>`: Reusable variable/function caches (no solver dependency)
//! - `TranslationContext<V>`: Owning compatibility wrapper (deprecated — use Session + State)
//! - `TranslationHost<V>`: Shared host trait for owning and borrowed translation
//! - `SortTranslator` trait: Map consumer sort types to z4 sorts
//! - `TermTranslator` trait: Recursive term translation
//! - `ops` module: Pre-built operator builders (arith, bv, array, etc.)

mod context;
pub mod ops;
mod sort;
mod term;

pub use context::{
    TranslationContext, TranslationHost, TranslationSession, TranslationState, TranslationTermHost,
};
pub use sort::SortTranslator;
pub use term::TermTranslator;

// Re-export z4-dpll Solver API types for consumer convenience.
// Consumers should depend only on z4-translate; these re-exports provide
// the full Solver-level type surface without a direct z4-dpll dependency.
pub use z4_dpll::api::{
    ArraySort, BitVecSort, DatatypeConstructor, DatatypeField, DatatypeSort, FpSpecialKind,
    FuncDecl, Logic, Model, ModelValue, SolveDetails, SolveResult, Solver, SolverError, Sort, Term,
    TermKind, VerificationLevel, VerificationSummary, VerifiedModel, VerifiedSolveResult,
};

// Re-export executor-level types needed by SMT-LIB text consumers
pub use z4_dpll::{CounterexampleStyle, Executor, ExecutorError, Statistics, UnknownReason};
