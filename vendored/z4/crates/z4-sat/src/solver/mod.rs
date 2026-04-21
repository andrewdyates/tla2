// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Verified result wrappers (VerifiedSatResult, VerifiedAssumeResult) are
// defined in `types.rs` and re-exported from this module.
// Crate-level `#![forbid(unsafe_code)]` prevents transmute-based type forgery.

//! Main CDCL SAT solver
//!
//! Implements the Conflict-Driven Clause Learning algorithm with:
//! - 2-watched literal scheme for unit propagation
//! - 1UIP conflict analysis with recursive clause minimization
//! - VSIDS (stable mode) and VMTF (focused mode) variable selection
//! - Chronological and non-chronological backtracking (SAT'18 paper)
//! - Lazy reimplication for out-of-order trail literals
//! - Phase saving for decision polarity
//! - Luby and glucose-style EMA restarts
//! - Block-level clause shrinking
//! - DRAT/LRAT proof generation for UNSAT certificates

use crate::bce::{BCEStats, BCE};
use crate::bve::{BVEStats, BVE};
use crate::clause::{ClauseTier, CORE_LBD, TIER1_LBD};
use crate::clause_arena::ClauseArena;
use crate::clause_trace::ClauseTrace;
use crate::condition::Conditioning;
use crate::conflict::{ConflictAnalyzer, ConflictResult};
use crate::congruence::CongruenceClosure;
use crate::decision_trace::{self, DecisionTraceWriter, ReplayTrace, SolveOutcome, TraceEvent};
use crate::decompose::Decompose;
use crate::diagnostic_trace::{DiagnosticPass, SatDiagnosticWriter};
use crate::extension::{ExtCheckResult, Extension, PreparedExtension, SolverContext};
use crate::factor::Factor;
use crate::gates::GateStats;
use crate::htr::{HTRStats, HTR};
use crate::lit_marks::LitMarks;
use crate::literal::{Literal, Variable};
use crate::mab::{BranchHeuristic, BranchHeuristicStats, BranchSelectorMode, MabController};
use crate::probe::{
    failed_literal_dominator, find_failed_literal_uip, hyper_binary_resolve, ProbeStats, Prober,
};
use crate::proof::ProofOutput;
use crate::proof_manager::{ProofAddKind, ProofManager};
use crate::reconstruct::ReconstructionStack;
use crate::subsume::{SubsumeStats, Subsumer};
use crate::sweep::{SweepStats, Sweeper};
use crate::tla_trace::TlaTraceWriter;
use crate::tla_traceable::TlaTraceable;
use crate::transred::TransRed;
use crate::vivify::{VivifyStats, VivifyTier};
use crate::vsids::VSIDS;
use crate::walk::Random;
use crate::watched::{ClauseRef, WatchList, WatchedLists, Watcher, BINARY_FLAG};
use std::io::Write;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

pub(crate) mod inproc_engines;
#[cfg(feature = "jit")]
mod jit_compile;
pub(crate) mod minimization_state;
pub(crate) mod phase_init_state;
#[cfg(feature = "jit")]
mod propagation_jit;
pub(crate) mod solver_stats;
mod state;
pub(crate) mod tier_state;
mod types;
mod var_data;
pub use state::Solver;
#[cfg(test)]
pub(crate) use types::MemoryStats;
pub(crate) use types::WatchOrderPolicy;
pub use types::*;
pub(crate) use types::{LRAT_A, LRAT_B, MIN_KEEP, MIN_POISON, MIN_REMOVABLE, MIN_VISITED};
pub(crate) use state::ReasonKind;
pub use lookahead::LookaheadStats;
pub(crate) use var_data::{
    VarData, NO_REASON,
    is_binary_literal_reason, binary_reason_lit, make_binary_reason, is_clause_reason,
};

// Solver struct is defined in state.rs (canonical after file split).
// Do NOT add a second `pub struct Solver` here — causes E0255.

// Implement SolverContext for Solver to allow extensions to observe state
impl SolverContext for Solver {
    fn value(&self, var: Variable) -> Option<bool> {
        self.var_value_from_vals(var.index())
    }

    fn decision_level(&self) -> u32 {
        self.decision_level
    }

    fn var_level(&self, var: Variable) -> Option<u32> {
        if self.var_is_assigned(var.index()) {
            Some(self.var_data[var.index()].level)
        } else {
            None
        }
    }

    fn trail(&self) -> &[Literal] {
        &self.trail
    }
}

mod arena_gc;
mod assumptions;
mod backtrack;
pub(crate) mod backward_proof;
mod branching;
mod build;
mod clause_add;
mod clause_add_internal;
mod clause_add_theory;
mod cold;
pub(crate) mod compact;
mod config;
mod config_preprocess;
mod config_preprocess_bve;
mod config_preprocess_finalize;
mod config_preprocess_probe;
mod config_preprocess_symmetry;
mod conflict_analysis;
mod conflict_analysis_bumping;
mod conflict_analysis_finalize;
mod conflict_analysis_invariants;
mod conflict_analysis_level;
mod conflict_analysis_lrat;
mod conflict_analysis_lrat_specialized;
mod conflict_analysis_lrat_unit_chain;
mod conflict_analysis_minimize;
mod conflict_analysis_minimize_lrat;
mod constants;
mod incremental;
mod inproc_control;
mod inprocessing;
pub(crate) mod lifecycle;
mod lookahead;
mod mutate;
mod mutate_delete;
mod mutate_replace;
mod mutate_replace_lrat;
mod mutate_validate;
mod otfs;
mod preprocess;
mod preprocess_reset;
mod preprocess_verify;
mod proof_emit;
mod propagation;
mod propagation_bcp;
mod propagation_dense;
#[cfg(feature = "unsafe-bcp")]
#[path = "propagation_bcp_unsafe.rs"]
mod propagation_bcp_unsafe;
pub(crate) mod reap;
mod reduction;
mod reduction_execute;
mod rephase;
mod restart;
mod shrink;
mod solve;
mod stats;
mod tracing_config;
mod vars;

use constants::*;
use tier_state::TIER_RECOMPUTE_INIT;

/// CDCL solver TLA+ trace module and variable constants.
const CDCL_TRACE_MODULE: &str = "cdcl_test";
const CDCL_TRACE_VARIABLES: [&str; 5] = [
    "assignment",
    "trail",
    "state",
    "decisionLevel",
    "learnedClauses",
];

impl TlaTraceable for Solver {
    fn tla_module() -> &'static str {
        CDCL_TRACE_MODULE
    }

    fn tla_variables() -> &'static [&'static str] {
        &CDCL_TRACE_VARIABLES
    }

    /// Enable TLA2 trace output for runtime verification.
    ///
    /// When enabled, the solver writes a JSONL trace file at each CDCL action
    /// boundary (propagate, decide, conflict, backtrack, sat, unsat).
    /// The trace file matches TLA2's `TraceHeader`/`TraceStep` format and can
    /// be validated with `tla2 trace validate`.
    ///
    /// This must be called before `solve()`.
    fn enable_tla_trace(&mut self, path: &str, module: &str, variables: &[&str]) {
        self.cold.tla_trace = Some(TlaTraceWriter::new(path, module, variables));
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

#[cfg(kani)]
mod verification;
