// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg_attr(
    not(any(feature = "unsafe-bcp", feature = "jit")),
    forbid(unsafe_code)
)]
#![cfg_attr(
    any(feature = "unsafe-bcp", feature = "jit"),
    deny(unsafe_code)
)]
// SAT solvers use many domain acronyms (BCE, BVE, VSIDS, HTR, CDCL, etc.).
#![allow(clippy::upper_case_acronyms)]

//! Z4 SAT - CDCL SAT solver core
//!
//! A high-performance Conflict-Driven Clause Learning SAT solver with
//! competitive techniques from CaDiCaL and Kissat.
//!
//! ## Example
//!
//! ```rust
//! use z4_sat::{Literal, SatResult, Solver};
//!
//! let mut solver = Solver::new(0);
//! let x0 = solver.new_var();
//! let x1 = solver.new_var();
//!
//! assert!(solver.add_clause(vec![Literal::positive(x0)]));
//! assert!(solver.add_clause(vec![Literal::positive(x1)]));
//!
//! match solver.solve().into_inner() {
//!     SatResult::Sat(model) => {
//!         assert!(model[x0.index()]);
//!         assert!(model[x1.index()]);
//!     }
//!     other => panic!("unexpected result: {other:?}"),
//! }
//! ```
//!
//! ## Core CDCL Features
//! - 2-watched literal scheme for efficient unit propagation
//! - VSIDS/VMTF variable selection heuristics with decay
//! - 1UIP conflict analysis with recursive clause minimization
//! - Luby and glucose-style EMA restarts
//! - LBD-based tier clause management (core/mid/local)
//! - Chronological backtracking with lazy reimplication
//! - Phase saving
//!
//! ## Inprocessing Techniques
//! - Vivification (clause strengthening via propagation)
//! - Bounded variable elimination (BVE)
//! - Blocked clause elimination (BCE)
//! - Subsumption and self-subsumption
//! - Failed literal probing
//! - Hyper-ternary resolution (HTR)
//! - Block-level clause shrinking
//!
//! ## Advanced SAT Techniques
//! - Gate extraction (AND/XOR/ITE/EQUIV recognition)
//! - SAT sweeping (equivalent literal detection)
//! - Congruence closure (gate-based equivalence detection)
//! - Walk/ProbSAT local search
//! - Factorization, transitive reduction, SCC decomposition, conditioning
//! - Model reconstruction for equisatisfiable transformations
//!
//! ## Parallel Portfolio Solving (test-only prototype)
//! - Multiple solver configurations running in parallel
//! - Different restart policies (Luby, Glucose EMA)
//! - Configurable inprocessing strategies
//! - First-result wins, others terminate
//!
//! ## Proof Generation
//! - DRAT proof output (text and binary formats)
//! - LRAT proof output with resolution hints (text and binary formats)
//! - Variable-length binary encoding for compact proofs

#![warn(missing_docs)]
#![warn(clippy::all)]

// Import safe_eprintln! from z4-core (non-panicking eprintln replacement)
#[macro_use]
extern crate z4_core;

pub(crate) mod bce;
pub(crate) mod bve;
pub(crate) mod cce;
pub(crate) mod clause;
pub(crate) mod clause_arena;
pub(crate) mod clause_trace;
pub(crate) mod condition;
pub(crate) mod conflict;
pub(crate) mod congruence;
pub(crate) mod decision_trace;
pub(crate) mod decompose;
pub(crate) mod diagnostic_trace;
pub(crate) mod dimacs;
/// Shared DIMACS-family parser core for SAT/XOR/QBF format tokenization.
pub mod dimacs_core;
pub(crate) mod elim_heap;
pub(crate) mod extension;
pub(crate) mod factor;
/// Compile-time feature flag constants for downstream crate introspection.
///
/// Zero-cost: all values are `const bool` resolved at compile time via `cfg!()`.
pub mod feature_flags {
    /// CaDiCaL-exact raw pointer BCP enabled.
    pub const UNSAFE_BCP: bool = cfg!(feature = "unsafe-bcp");
    /// Cranelift JIT-compiled BCP enabled.
    pub const JIT: bool = cfg!(feature = "jit");
    /// GPU compute infrastructure enabled.
    pub const GPU: bool = cfg!(feature = "gpu");
}

pub(crate) mod adaptive;
pub(crate) mod features;
pub(crate) mod forward_checker;
pub(crate) mod gates;
#[cfg(feature = "gpu")]
pub(crate) mod gpu;
pub(crate) mod htr;
pub(crate) mod kani_compat;
pub(crate) mod kitten;
pub(crate) mod lit_marks;
pub(crate) mod literal;
#[cfg(any(debug_assertions, test))]
pub(crate) mod lrat_checker;
pub(crate) mod mab;
pub(crate) mod occ_list;
#[cfg(test)]
mod portfolio;
pub(crate) mod probe;
pub(crate) mod proof;
mod proof_certificate;
pub(crate) mod proof_manager;
pub(crate) mod reconstruct;
pub(crate) mod replay_trace;
pub(crate) mod solver;
pub(crate) mod solver_log;
pub(crate) mod subsume;
pub(crate) mod sweep;
pub(crate) mod symmetry;
#[cfg(any(test, kani))]
pub(crate) mod test_util;
pub(crate) mod tla_trace;
pub(crate) mod tla_traceable;
pub(crate) mod transred;
mod variant;
pub(crate) mod vivify;
pub(crate) mod vsids;
pub(crate) mod walk;
pub(crate) mod warmup;
pub(crate) mod watched;

/// Snapshot of SAT solver feature toggles relevant to inprocessing soundness gates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct InprocessingFeatureProfile {
    /// Initial preprocess pipeline toggle.
    pub preprocess: bool,
    /// Walk-based phase initialization toggle.
    pub walk: bool,
    /// Warmup-based phase initialization toggle.
    pub warmup: bool,
    /// Conflict-clause shrink toggle.
    pub shrink: bool,
    /// Hyper-binary resolution within probing toggle.
    pub hbr: bool,
    /// Vivification toggle.
    pub vivify: bool,
    /// Subsumption toggle.
    pub subsume: bool,
    /// Failed-literal probing toggle.
    pub probe: bool,
    /// Bounded variable elimination toggle.
    pub bve: bool,
    /// Blocked clause elimination toggle.
    pub bce: bool,
    /// Conditioning toggle.
    pub condition: bool,
    /// SCC decomposition toggle.
    pub decompose: bool,
    /// Factorization toggle.
    pub factor: bool,
    /// Transitive reduction toggle.
    pub transred: bool,
    /// Hyper-ternary resolution toggle.
    pub htr: bool,
    /// Gate extraction toggle.
    pub gate: bool,
    /// Congruence-closure toggle.
    pub congruence: bool,
    /// SAT sweeping toggle.
    pub sweep: bool,
    /// Backbone literal computation toggle.
    pub backbone: bool,
    /// Root-only symmetry preprocessing toggle.
    pub symmetry: bool,
}

// -- Public API: types used by downstream crates and integration tests --
pub use clause_trace::{ClauseTrace, ClauseTraceEntry};
pub use dimacs::{parse_str as parse_dimacs, DimacsError, DimacsFormula};
pub use extension::{
    ExtCheckResult, ExtPropagateResult, Extension, PreparedExtension, SolverContext,
};
pub use literal::{Literal, SignedClause, Variable};
pub use mab::{BranchHeuristic, BranchHeuristicStats, BranchSelectorMode};
pub use proof::{DratWriter, LratWriter, ProofOutput};
pub use proof_certificate::{ProofCertificate, ProofStep};
pub use solver::{
    AssumeResult, FactorStats, LookaheadStats, SatResult, SatUnknownReason, SetSolutionError,
    Solver, TheoryPropResult, VerifiedAssumeResult, VerifiedSatResult,
};
pub use tla_trace::TlaTraceWriter;
pub use tla_traceable::TlaTraceable;
pub use variant::{SolverVariant, VariantConfig, VariantInput, VariantRestartPolicy};
pub use adaptive::{adjust_features_for_instance, should_disable_reorder};
pub use features::{InstanceClass, SatFeatures};
pub use watched::ClauseRef;

// -- Inprocessing statistics types (consumed by integration tests and z4 binary) --
pub use bce::BCEStats;
pub use bve::BVEStats;
pub use condition::ConditioningStats;
pub use congruence::CongruenceStats;
pub use decompose::DecomposeStats;
pub use gates::GateStats;
pub use htr::HTRStats;
pub use probe::ProbeStats;
pub use subsume::SubsumeStats;
pub use sweep::SweepStats;
pub use transred::TransRedStats;
pub use vivify::VivifyStats;
