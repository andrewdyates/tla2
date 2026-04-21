// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]
// Clippy 1.93.0 fires large_stack_arrays with a lost span (lib.rs:1:1) on
// monomorphised code visible only in test builds.  Fixed on nightly; suppress
// until stable catches up.
#![cfg_attr(test, allow(clippy::large_stack_arrays))]
// CHC crate has forward-looking infrastructure with some unused code paths
// and rapid iteration patterns. Suppress common style lints at crate level.
#![allow(
    dead_code,
    unused_variables,
    unused_qualifications,
    private_interfaces,
    deprecated,
    clippy::redundant_closure,
    clippy::redundant_closure_for_method_calls,
    clippy::redundant_clone,
    clippy::needless_lifetimes,
    clippy::elidable_lifetime_names,
    clippy::needless_return,
    clippy::suboptimal_flops,
    clippy::option_option,
    clippy::let_and_return,
    clippy::match_like_matches_macro,
    clippy::cast_lossless,
    clippy::question_mark,
    clippy::type_complexity,
    clippy::too_many_arguments,
    clippy::vec_init_then_push,
    clippy::filter_map_bool_then,
    clippy::unnecessary_lazy_evaluations,
    clippy::manual_contains,
    clippy::uninlined_format_args
)]

//! CHC (Constrained Horn Clause) solver with adaptive portfolio
//!
//! This crate implements an 11-engine adaptive portfolio for solving Constrained
//! Horn Clause (CHC) problems, used in program verification to find inductive
//! invariants or counterexamples. Engines: PDR/IC3 (primary), BMC, k-induction,
//! PDKind, TPA, TRL, Decomposition, LAWI, IMC, DAR, CEGAR.
//!
//! # Example
//!
//! ```rust,no_run
//! use z4_chc::{
//!     AdaptiveConfig, AdaptivePortfolio, ChcExpr, ChcProblem, ChcSort, ChcVar,
//!     ClauseBody, ClauseHead, HornClause,
//! };
//!
//! let mut problem = ChcProblem::new();
//! let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
//!
//! let x = ChcVar::new("x", ChcSort::Int);
//! problem.add_clause(HornClause::new(
//!     ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
//!     ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
//! ));
//!
//! problem.add_clause(HornClause::new(
//!     ClauseBody::new(
//!         vec![(inv, vec![ChcExpr::var(x.clone())])],
//!         Some(ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(0))),
//!     ),
//!     ClauseHead::False,
//! ));
//!
//! let solver = AdaptivePortfolio::new(problem, AdaptiveConfig::default());
//! let result = solver.solve();
//! assert!(result.is_safe());
//! ```
//!
//! # Example CHC Problem
//!
//! ```text
//! ; Find invariant Inv(x) such that:
//! ; 1. x = 0 => Inv(x)              (initial state)
//! ; 2. Inv(x) /\ x < 10 => Inv(x+1) (transition)
//! ; 3. Inv(x) /\ x >= 10 => false   (safety - should be unsat)
//! ```
//!
//! # Architecture
//!
//! - `Predicate`: Uninterpreted relation to synthesize interpretation for
//! - `HornClause`: Rule of form `body => head`
//! - `ChcProblem`: Collection of Horn clauses with a query
//! - `PdrSolver`: PDR algorithm implementation
//! - `PortfolioSolver`: Runs multiple engines (PDR/BMC/Kind/PDKind/TPA/TRL/Decomposition/LAWI/IMC/DAR/CEGAR)
//! - `BmcSolver`: Bounded model checking engine
//! - `PdkindSolver`: K-induction style engine
//! - `TpaSolver`: Transition Power Abstraction engine
//! - `TrlSolver`: Transitive relation learning engine

// Import safe_eprintln! from z4-core (non-panicking eprintln replacement)
#[macro_use]
extern crate z4_core;

cached_env_flag!(pub(crate) debug_prop_enabled, "Z4_DEBUG_PROP");
cached_env_flag!(pub(crate) debug_chc_smt_enabled, "Z4_DEBUG_CHC_SMT");
cached_env_flag!(pub(crate) debug_algebraic_enabled, "Z4_DEBUG_ALGEBRAIC");

mod adaptive;
mod adaptive_bv_dual_lane;
mod adaptive_bv_strategy;
mod adaptive_decision_log;
mod adaptive_engines;
mod adaptive_multi_pred;
mod adaptive_multi_pred_complex;
mod adaptive_validation;
pub(crate) mod algebraic_invariant;
#[allow(dead_code)]
mod blackboard;
mod bmc;
pub(crate) mod bv_util;
mod cancellation;
pub(crate) mod cegar;
mod chc_statistics;
mod classifier;
mod clause;
mod convex_closure;
pub(crate) mod cvp;
mod dar;
pub(crate) mod decomposition;
mod engine_config;
pub(crate) mod engine_result;
mod engine_utils;
mod error;
pub(crate) mod expr;
mod expr_vars;
pub(crate) mod failure_analysis;
mod farkas;
mod farkas_decomposition;
mod generalize;
mod imc;
mod interpolant_validation;
mod interpolation;
mod iuc_solver;
mod k_to_1_inductive;
mod kind;
mod lawi;
pub(crate) mod lemma_cache;
mod lemma_hints;
pub(crate) mod lemma_pool;
mod mbp;
mod parser;
mod pdkind;
mod pdr;
mod portfolio;
mod predicate;
mod problem;
mod proof_interpolation;
mod qualifier;
pub(crate) mod recurrence;
pub(crate) mod single_loop;
mod smt;
mod synthesis;
mod tarjan;
pub(crate) mod term_bridge;
pub(crate) mod tpa;
pub(crate) mod trace;
pub(crate) mod transform;
pub(crate) mod transition_system;
pub(crate) mod trl;
pub(crate) mod trp;

// Core data model — used in public API signatures (ChcParser::parse -> ChcProblem, etc.)
pub use clause::HornClause;
pub use expr::{ChcDtConstructor, ChcDtSelector, ChcExpr, ChcSort, ChcVar};
pub use predicate::Predicate;
pub use problem::ChcProblem;

// Core types used by integration tests for problem construction
pub use clause::{ClauseBody, ClauseHead};
pub use expr::ChcOp;
pub use predicate::PredicateId;

// Public engine API — consumed by z4 binary, fuzz targets, examples, integration tests
pub use adaptive::{AdaptiveConfig, AdaptivePortfolio};
pub use bmc::{BmcConfig, BmcSolver};
pub use cancellation::CancellationToken;
pub use chc_statistics::ChcStatistics;
pub use engine_result::{
    ChcEngineResult, VerifiedChcResult, VerifiedCounterexample, VerifiedInvariant,
    VerifiedUnknownMarker,
};
pub use kind::{KindConfig, KindResult, KindSolver};
pub use lemma_hints::{
    canonical_var_for_pred_arg, canonical_var_name, canonical_vars_for_pred, HintProviders,
    HintRequest, HintStage, LemmaHint, LemmaHintProvider,
};
pub use mbp::Mbp;
pub use parser::ChcParser;
pub use pdkind::{IncrementalMode, PdkindConfig, PdkindResult, PdkindSolver};
pub use pdr::{CexVerificationResult, PredicateInterpretation};
pub use pdr::{Counterexample, CounterexampleStep, InvariantModel};
pub use pdr::{PdrConfig, PdrResult, PdrSolver};
pub use portfolio::{EngineConfig, PortfolioConfig, PortfolioResult, PortfolioSolver};
pub use smt::{SmtContext, SmtResult, SmtValue, UnsatCoreDiagnostics};

/// Stable public API for constructing individual CHC engines.
///
/// For most use cases, [`AdaptivePortfolio`] is recommended — it runs multiple
/// engines and verifies results automatically. Use the functions in this module
/// when you need direct control over a specific engine (e.g., PDR-only solving
/// or custom portfolio configurations).
///
/// # Examples
///
/// ```rust,no_run
/// use z4_chc::{engines, ChcProblem, PdrConfig, PortfolioConfig};
///
/// let problem = ChcProblem::new();
///
/// // Direct PDR solving
/// let mut solver = engines::new_pdr_solver(problem.clone(), PdrConfig::default());
///
/// // Custom portfolio
/// let solver = engines::new_portfolio_solver(problem, PortfolioConfig::default());
/// ```
pub mod engines {
    use super::*;

    /// Construct a [`PdrSolver`] with the given configuration.
    ///
    /// PDR (Property-Directed Reachability) is the primary invariant discovery
    /// engine. Use this when you need direct access to PDR results, model
    /// verification, or counterexample analysis.
    pub fn new_pdr_solver(problem: ChcProblem, config: PdrConfig) -> PdrSolver {
        PdrSolver::new(problem, config)
    }

    /// Construct a [`PortfolioSolver`] with the given configuration.
    ///
    /// The portfolio solver runs multiple engines (PDR, BMC, PDKIND, TPA, etc.)
    /// and returns the first result. Use this when you want multi-engine coverage
    /// with explicit control over which engines to enable.
    pub fn new_portfolio_solver(problem: ChcProblem, config: PortfolioConfig) -> PortfolioSolver {
        PortfolioSolver::new(problem, config)
    }
}

/// Test support: factory functions for constructing individual CHC engines.
///
/// This module provides access to all engine constructors for integration tests.
/// For production use, prefer [`engines`] (stable public API) or
/// [`AdaptivePortfolio`] (recommended default).
#[doc(hidden)]
pub mod testing {
    use super::*;

    // Re-export the stable engine constructors so existing test code using
    // `testing::new_pdr_solver` and `testing::new_portfolio_solver` continues
    // to compile without changes.
    pub use super::engines::{new_pdr_solver, new_portfolio_solver};

    /// Construct a [`BmcSolver`] for testing.
    pub fn new_bmc_solver(problem: ChcProblem, config: BmcConfig) -> BmcSolver {
        BmcSolver::new(problem, config)
    }

    /// Construct a [`PdkindSolver`] for testing.
    pub fn new_pdkind_solver(problem: ChcProblem, config: PdkindConfig) -> PdkindSolver {
        PdkindSolver::new(problem, config)
    }

    /// Construct a [`PdkindSolver`] with default config for testing.
    pub fn pdkind_solver_defaults(problem: ChcProblem) -> PdkindSolver {
        PdkindSolver::with_defaults(problem)
    }

    /// Construct a [`PdkindSolver`] with cancellation for testing.
    pub fn pdkind_solver_cancellation(
        problem: ChcProblem,
        token: CancellationToken,
    ) -> PdkindSolver {
        PdkindSolver::with_cancellation(problem, token)
    }

    /// Construct a [`KindSolver`] for testing.
    pub fn new_kind_solver(problem: ChcProblem, config: KindConfig) -> KindSolver {
        KindSolver::new(problem, config)
    }

    /// Run PDR on a problem for testing (convenience wrapper for
    /// [`PdrSolver::solve_problem`]).
    pub fn pdr_solve_problem(problem: &ChcProblem, config: PdrConfig) -> PdrResult {
        PdrSolver::solve_problem(problem, config)
    }

    /// Parse a CHC input string and run PDR for testing (convenience wrapper
    /// for [`PdrSolver::solve_from_str`]).
    pub fn pdr_solve_from_str(input: &str, config: PdrConfig) -> ChcResult<PdrResult> {
        PdrSolver::solve_from_str(input, config)
    }

    /// Parse a CHC file and run PDR for testing (convenience wrapper for
    /// [`PdrSolver::solve_from_file`]).
    pub fn pdr_solve_from_file(
        path: impl AsRef<std::path::Path>,
        config: PdrConfig,
    ) -> ChcResult<PdrResult> {
        PdrSolver::solve_from_file(path, config)
    }

    /// Report whether adaptive classification selects the direct BV-native
    /// simple-loop route for the given problem.
    pub fn adaptive_uses_bv_native_direct_route(problem: &ChcProblem) -> bool {
        let adaptive = AdaptivePortfolio::new(problem.clone(), AdaptiveConfig::default());
        let features = classifier::ProblemClassifier::classify(problem);
        adaptive.use_bv_native_direct_route(&features)
    }

    /// Parse an SMT model value through the CHC SMT backend's model parser.
    ///
    /// This stays under `testing` so integration tests can verify parser
    /// regressions without depending on the crate's internal module layout.
    pub fn parse_smt_model_value_for_testing(
        input: &str,
        sort: &z4_core::Sort,
    ) -> Option<SmtValue> {
        smt::parse_model_value_for_testing(input, sort)
    }

    /// Direction for TRL-only test runs.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum TrlTestDirection {
        /// Run TRL on the original transition system.
        Forward,
        /// Run TRL on the reversed transition system (init/query swapped).
        Backward,
    }

    /// Parse a CHC problem from a string and run TRL-only in the given direction.
    ///
    /// Returns a [`PortfolioResult`] (which is a type alias for [`ChcEngineResult`]).
    /// If `validate` is true, the TRL config enables verbose mode for diagnostics.
    pub fn solve_trl_only_from_str(
        input: &str,
        direction: TrlTestDirection,
        validate: bool,
        timeout: std::time::Duration,
    ) -> ChcResult<PortfolioResult> {
        use crate::engine_config::ChcEngineConfig;
        use crate::transition_system::TransitionSystem;
        use crate::trl::{TrlConfig, TrlSolver};

        let problem = ChcParser::parse(input).map_err(|e| ChcError::Parse(e.to_string()))?;
        let ts = TransitionSystem::from_chc_problem(&problem).map_err(ChcError::Parse)?;

        let ts = match direction {
            TrlTestDirection::Forward => ts,
            TrlTestDirection::Backward => ts.reverse(),
        };

        let token = CancellationToken::new();
        let token_clone = token.clone();
        let timer = std::thread::spawn(move || {
            std::thread::sleep(timeout);
            token_clone.cancel();
        });

        let config = TrlConfig {
            base: ChcEngineConfig {
                verbose: validate,
                cancellation_token: Some(token),
            },
            ..TrlConfig::default()
        };

        let mut solver = TrlSolver::new(ts, config);
        let result = solver.solve();
        drop(timer);
        Ok(result)
    }
}

// Error types — public so consumers can match on structured errors from try_solve()
pub use error::{ChcError, ChcResult};
pub(crate) use proof_interpolation::{
    compute_interpolant_from_lia_farkas, compute_interpolant_from_smt_farkas_history,
};
pub(crate) use qualifier::QualifierSet;
pub(crate) use smt::{InterpolatingResult, InterpolatingSmtContext};

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
