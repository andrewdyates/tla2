// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! Z4 - A high-performance SMT solver in Rust
//!
//! This crate provides the public consumer API surface. Internal crates
//! (`z4_dpll`, `z4_core`, `z4_chc`, etc.) are implementation details and
//! should not be depended on directly by downstream consumers.
//!
//! # API Modules
//!
//! | Module | Stability | Purpose |
//! |--------|-----------|---------|
//! | Root (`z4::Solver`, etc.) | **Stable** | Core solver types, flat imports |
//! | [`api`] | **Stable** | Explicit single-module import path |
//! | [`prelude`] | **Stable** | Glob import for convenience |
//! | [`chc`] | **Stable** | CHC solver surface (zani, tla2) |
//! | [`executor`] | **Stable** | Text-driven SMT-LIB execution |
//! | [`allsat`] | **Stable** | Solution enumeration (ALL-SAT) |
//! | [`proof_internals`] | Unstable | Deep proof reconstruction types |
//! | [`translate`] | Unstable | Formula translation framework |
//!
//! # Quick Start
//!
//! Use the re-exported API types for the native Rust API:
//!
//! ```no_run
//! use z4::{Logic, SolveResult, Sort, Solver};
//!
//! let mut solver = Solver::try_new(Logic::QfLia).unwrap();
//! let x = solver.declare_const("x", Sort::Int);
//! let zero = solver.int_const(0);
//! let x_gt_zero = solver.gt(x, zero);
//! solver.assert_term(x_gt_zero);
//!
//! let details = solver.check_sat_with_details();
//! match details.accept_for_consumer() {
//!     Ok(SolveResult::Sat) => {
//!         let model = solver
//!             .model()
//!             .expect("accepted SAT result has model")
//!             .into_inner();
//!         println!("x = {:?}", model.int_val("x"));
//!     }
//!     Ok(SolveResult::Unsat) => println!("unsatisfiable"),
//!     Ok(SolveResult::Unknown) | Err(_) => {
//!         if let Some(reason) = details.unknown_reason {
//!             println!("unknown: {}", reason);
//!         }
//!     }
//!     Ok(_) => {}
//! }
//! ```

#![warn(missing_docs)]
#![warn(clippy::all)]

// Re-export the native API types as canonical
pub use z4_dpll::api::Solver;
pub use z4_dpll::api::{
    AssumptionSolveDetails, ConsumerAcceptanceError, FpSpecialKind, FuncDecl, Logic, Model,
    ModelValue, SolveDetails, SolveResult, SolverError, SolverScope, Sort, Term, TermKind,
    VerificationLevel, VerificationSummary, VerifiedModel, VerifiedSolveResult,
};
// Sort companion types — needed to construct Sort::BitVec, Sort::Array, Sort::Datatype
pub use z4_core::{ArraySort, BitVecSort, DatatypeConstructor, DatatypeField, DatatypeSort};
pub use z4_dpll::api::SortExt;
// Re-export structured types for API completeness
pub use z4_dpll::{CounterexampleStyle, StatValue, Statistics, UnknownReason};
// Re-export proof certificate types for UNSAT result consumers (#4521)
pub use z4_dpll::api::{
    FarkasCertificate, ProofAcceptanceError, ProofAcceptanceMode, ProofCheckError, ProofQuality,
    StrictProofVerdict, UnsatProofArtifact,
};
pub use z4_proof::PartialProofCheck;

// Re-export frontend parsing for the common parse+solve path (#3039)
pub use z4_frontend::{parse, Command, Context, ParseError};
// Re-export SExpr for consumers that manipulate SMT-LIB ASTs (zani, gamma-crown) (#5140)
pub use z4_frontend::SExpr;
// Re-export formula diagnostics for consumers that parse then analyze (#461)
pub use z4_frontend::{collect_formula_stats, FormulaStats};

/// Low-level s-expression parsing for consumers that manipulate SMT-LIB
/// output at the AST level (e.g., zani CHC proof rewriting).
pub mod sexp {
    pub use z4_frontend::sexp::{parse_sexp, parse_sexps};
    pub use z4_frontend::SExpr;
}

/// Z4 version string (from Cargo.toml).
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

// Shared panic-boundary helpers for downstream consumers (#5140).
// sunder uses `panic_payload_to_string`; other consumers use `catch_z4_panics`.
pub use z4_core::{catch_z4_panics, is_z4_panic_reason, panic_payload_to_string};

// Cached env-flag helper macro used by sunder (#5140).
pub use z4_core::cached_env_flag;

// Re-export numeric types used in Model API return values (#5140).
// Without these, consumers must independently add num-rational and num-bigint.
pub use num_bigint::BigInt;
pub use num_rational::BigRational;

/// Unified error type for parse + solve operations.
///
/// Consumers that both parse SMT-LIB input and solve can use `z4::Error` as
/// a single error type covering both phases via `?` conversion:
///
/// ```no_run
/// fn run(input: &str) -> z4::Result<()> {
///     let _commands = z4::parse(input)?;
///     let mut solver = z4::Solver::try_new(z4::Logic::QfLia).unwrap();
///     // ... process commands ...
///     let details = solver.try_check_sat_with_details()?;
///     match details.accept_for_consumer() {
///         Ok(z4::SolveResult::Sat) => {
///             let _model = solver
///                 .model()
///                 .expect("accepted SAT result has model");
///         }
///         Ok(z4::SolveResult::Unsat) => {}
///         Ok(z4::SolveResult::Unknown) | Err(_) => {}
///         Ok(_) => {}
///     }
///     Ok(())
/// }
/// ```
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum Error {
    /// An error during SMT-LIB parsing.
    #[error(transparent)]
    Parse(#[from] ParseError),
    /// An error during solving.
    #[error(transparent)]
    Solve(#[from] SolverError),
}

/// Convenience alias for `std::result::Result<T, z4::Error>`.
pub type Result<T> = std::result::Result<T, Error>;

/// Canonical explicit-import Rust API for downstream consumers.
///
/// This module provides a single import path for all stable consumer-facing
/// types. Downstream crates should prefer `use z4::api::{...}` over reaching
/// into internal crates like `z4_dpll::api`.
///
/// # Example
///
/// ```no_run
/// use z4::api::{Logic, SolveResult, Solver, Sort};
///
/// let mut solver = Solver::try_new(Logic::QfLia).unwrap();
/// let x = solver.declare_const("x", Sort::Int);
/// let zero = solver.int_const(0);
/// let x_gt_zero = solver.gt(x, zero);
/// solver.assert_term(x_gt_zero);
/// assert!(solver.check_sat().is_sat());
/// ```
pub mod api {
    pub use crate::{
        AssumptionSolveDetails, ConsumerAcceptanceError, CounterexampleStyle, FpSpecialKind,
        FuncDecl, Logic, Model, ModelValue, SolveDetails, SolveResult, Solver, SolverError,
        SolverScope, Sort, StatValue, Statistics, Term, TermKind, UnknownReason, VerificationLevel,
        VerificationSummary, VerifiedModel, VerifiedSolveResult,
    };
    pub use z4_core::{ArraySort, BitVecSort, DatatypeConstructor, DatatypeField, DatatypeSort};
    pub use z4_dpll::api::SortExt;

    // Parser and error facade (#3039)
    pub use crate::{parse, Command, Error, ParseError, Result};

    // Numeric types from Model API return values (#5140)
    pub use crate::{BigInt, BigRational};

    // Proof certificate types for UNSAT consumers (#4521)
    pub use crate::{
        FarkasCertificate, PartialProofCheck, ProofAcceptanceError, ProofAcceptanceMode,
        ProofCheckError, ProofQuality, StrictProofVerdict, UnsatProofArtifact,
    };

    // Helper utilities for downstream consumers (#6589, #5140)
    pub use crate::cached_env_flag;
    pub use crate::{catch_z4_panics, is_z4_panic_reason, panic_payload_to_string, VERSION};

    // S-expression types for AST-level consumers (#5140)
    pub use crate::sexp::{parse_sexp, parse_sexps};
    pub use crate::SExpr;

    // Formula diagnostics for parse+analyze consumers (#461)
    pub use crate::{collect_formula_stats, FormulaStats};
}

/// Constrained Horn Clause (CHC) solver surface for downstream consumers.
///
/// This module exposes the consumer-facing CHC types from `z4_chc`. Downstream
/// crates (tla2, zani) should prefer `use z4::chc::{...}` over reaching into
/// `z4_chc` directly.
///
/// # Example
///
/// ```no_run
/// use z4::chc::{ChcProblem, PdrConfig, AdaptiveConfig, AdaptivePortfolio};
///
/// let problem = ChcProblem::new();
/// let config = AdaptiveConfig::default();
/// ```
///
/// # Type stability
///
/// Most types in this module are stable consumer types. However, `SmtContext`
/// and `SmtResult` are engine-internal types exposed for deep integrations
/// and may change between minor versions.
pub mod chc {
    pub use z4_chc::{
        // Lemma hint API (zani auto_invariants integration)
        canonical_var_for_pred_arg,
        canonical_var_name,
        canonical_vars_for_pred,
        // Core data model
        engines,
        // Engine API
        AdaptiveConfig,
        AdaptivePortfolio,
        CancellationToken,
        // Result types (verified envelope + inner types)
        CexVerificationResult,
        // DT problem construction
        ChcDtConstructor,
        ChcDtSelector,
        ChcEngineResult,
        ChcError,
        ChcExpr,
        ChcOp,
        ChcParser,
        ChcProblem,
        ChcResult,
        ChcSort,
        ChcStatistics,
        ChcVar,
        ClauseBody,
        ClauseHead,
        Counterexample,
        CounterexampleStep,
        EngineConfig,
        HintProviders,
        HintRequest,
        HintStage,
        HornClause,
        InvariantModel,
        LemmaHint,
        LemmaHintProvider,
        // MBP (model-based projection)
        Mbp,
        PdrConfig,
        PdrResult,
        PdrSolver,
        PortfolioConfig,
        PortfolioResult,
        PortfolioSolver,
        Predicate,
        PredicateId,
        PredicateInterpretation,
        // SMT context and model types
        SmtContext,
        SmtResult,
        SmtValue,
        UnsatCoreDiagnostics,
        VerifiedChcResult,
        VerifiedCounterexample,
        VerifiedInvariant,
        VerifiedUnknownMarker,
    };
}

/// Text-driven SMT-LIB executor surface.
///
/// `Executor` is the text-driven SMT-LIB path used by zani and tla2. It is a
/// different abstraction layer from `z4::api::Solver` (which is the typed
/// solver-construction surface).
///
/// # Example
///
/// ```no_run
/// use z4::executor::Executor;
/// use z4::parse;
///
/// let commands = parse("(set-logic QF_LIA)\n(check-sat)").expect("valid input");
/// let mut exec = Executor::new();
/// let outputs = exec.execute_all(&commands).expect("execution succeeds");
/// ```
pub mod executor {
    pub use z4_core::{Proof, TermStore};
    pub use z4_dpll::{Executor, ExecutorError};
    pub use z4_frontend::Context;

    /// Convenience alias for `std::result::Result<T, ExecutorError>`.
    pub type Result<T> = std::result::Result<T, ExecutorError>;
}

/// Solution enumeration (ALL-SAT) surface for downstream consumers.
///
/// This module exposes the consumer-facing ALL-SAT types from `z4_allsat`.
/// Downstream crates (tla2) should prefer `use z4::allsat::{...}` over
/// depending on `z4_allsat` directly.
///
/// # Example
///
/// ```
/// use z4::allsat::{AllSatSolver, AllSatConfig};
///
/// let mut solver = AllSatSolver::new();
/// solver.add_clause(vec![1, 2]);
/// solver.add_clause(vec![-1, -2]);
/// let solutions: Vec<_> = solver.iter().collect();
/// assert_eq!(solutions.len(), 2);
/// ```
pub mod allsat {
    pub use z4_allsat::{AllSatConfig, AllSatIterator, AllSatSolver, AllSatStats, Solution};
}

/// Proof internals for deep consumers that reconstruct or analyze proof certificates.
///
/// This module exposes the internal proof representation types from `z4_core`
/// and `z4_proof`. Downstream crates that perform proof reconstruction
/// (lean5-auto) or proof translation should prefer `use z4::proof_internals::{...}`
/// over reaching into `z4_core` or `z4_proof` directly.
///
/// # Stability
///
/// These types reflect internal proof representation and may change between
/// minor versions. Pin your z4 dependency version if you use this module.
pub mod proof_internals {
    // Proof data structures from z4_core (#6742)
    pub use z4_core::{
        AletheRule, FarkasAnnotation, Proof, ProofId, ProofStep, Sort, TermData, TermId, TermStore,
        TheoryLemmaKind,
    };
    // Symbol formatting for proof output
    pub use z4_core::quote_symbol;
    // Proof checking and export from z4_proof
    pub use z4_proof::{check_proof_with_quality, export_alethe, export_alethe_with_problem_scope};
}

/// Formula translation surface for consumers that transform z4 terms into
/// external representations (Lean expressions, other solver formats, etc.).
///
/// This module exposes the translation framework from `z4_translate`.
/// Downstream crates (lean5-auto) should prefer `use z4::translate::{...}`
/// over depending on `z4_translate` directly.
///
/// # Stability
///
/// These types reflect internal term representation and may change between
/// minor versions. Pin your z4 dependency version if you use this module.
pub mod translate {
    pub use z4_translate::{
        SortTranslator, TermTranslator, TranslationContext, TranslationSession, TranslationState,
        TranslationTermHost,
    };
    /// Theory-specific operation translators.
    pub mod ops {
        pub use z4_translate::ops::*;
    }
}

/// Prelude module for convenient glob imports.
///
/// # Example
///
/// ```no_run
/// use z4::prelude::*;
///
/// let mut solver = Solver::try_new(Logic::QfLia).unwrap();
/// let x = solver.declare_const("x", Sort::Int);
/// let zero = solver.int_const(0);
/// let x_gt_zero = solver.gt(x, zero);
/// solver.assert_term(x_gt_zero);
/// assert!(solver.check_sat().is_sat());
/// ```
pub mod prelude {
    // Core solver types
    pub use crate::{
        AssumptionSolveDetails, CounterexampleStyle, FpSpecialKind, Logic, Model, ModelValue,
        SolveDetails, SolveResult, Solver, SolverError, SolverScope, Sort, StatValue, Statistics,
        Term, TermKind, UnknownReason, VerificationLevel, VerificationSummary, VerifiedModel,
        VerifiedSolveResult,
    };

    // API types for declare_fun() → apply() pattern (#2080)
    pub use crate::FuncDecl;
    pub use z4_dpll::api::SortExt;

    // Datatype types for datatype declarations (#2080)
    pub use z4_core::{DatatypeConstructor, DatatypeField, DatatypeSort};

    // Array and bitvector sort constructors (#2080)
    pub use z4_core::{ArraySort, BitVecSort};

    // Frontend parsing and error facade (#3039)
    pub use crate::{parse, Command, Error, ParseError, Result};

    // Numeric types from Model API return values (#5140)
    pub use crate::{BigInt, BigRational};

    // Proof certificate types for UNSAT consumers (#4521)
    pub use crate::{
        FarkasCertificate, PartialProofCheck, ProofAcceptanceError, ProofAcceptanceMode,
        ProofCheckError, ProofQuality, StrictProofVerdict, UnsatProofArtifact,
    };

    // Helper utilities for downstream consumers (#6589, #5140)
    pub use crate::cached_env_flag;
    pub use crate::{catch_z4_panics, is_z4_panic_reason, panic_payload_to_string, VERSION};

    // S-expression types for AST-level consumers (#5140)
    pub use crate::sexp::{parse_sexp, parse_sexps};
    pub use crate::SExpr;

    // Formula diagnostics for parse+analyze consumers (#461)
    pub use crate::{collect_formula_stats, FormulaStats};
}

#[cfg(test)]
#[path = "facade_reexport_tests.rs"]
mod facade_reexport_tests;

#[cfg(test)]
#[path = "proof_facade_tests.rs"]
mod proof_facade_tests;
