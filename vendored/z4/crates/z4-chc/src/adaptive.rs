// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adaptive portfolio solver for CHC problems.
//!
//! This module wraps `PortfolioSolver` with intelligent strategy selection
//! based on problem classification. The goal is to predict which engine
//! will work best and budget time accordingly for 30s bounded execution.
//!
//! # Strategy
//!
//! 1. Classify problem (<100ms overhead)
//! 2. Select engine configuration based on class
//! 3. Set appropriate timeouts for graceful degradation
//! 4. Return best result within time budget
//!
//! # Reference
//!
//! Part of #1868 - Adaptive portfolio for 30s bounded execution.
//! See `designs/2026-02-01-adaptive-portfolio-30s.md` for full design.

use crate::adaptive_decision_log::DecisionEntry;
use crate::adaptive_decision_log::DecisionLog;
use crate::chc_statistics::ChcStatistics;
use crate::classifier::{ProblemClass, ProblemClassifier, ProblemFeatures};
use crate::engine_result::ValidationEvidence;
use crate::failure_analysis::SolverStats;
use crate::lemma_hints::{HintProviders, LemmaHint};
use crate::pdr::{PdrConfig, PdrResult, PdrSolver};
use crate::portfolio::features::ChcFeatureExtractor;
use crate::portfolio::selector::EngineSelector;
use crate::portfolio::{EngineConfig, PortfolioConfig, PortfolioResult, PortfolioSolver};
use crate::transform::{BvToIntAbstractor, DeadParamEliminator, TransformationPipeline};
use crate::ChcProblem;
use std::sync::Mutex;
use std::time::{Duration, Instant};

/// Default total time budget for CHC solving (27s solving + 3s margin).
const DEFAULT_SOLVE_BUDGET: Duration = Duration::from_secs(27);

/// Stack size for the adaptive solver thread (#6847).
///
/// The adaptive solver runs probe PDR, Kind, and retry engines directly
/// on its thread (not via portfolio thread spawning). Deep `ChcExpr` trees
/// from `SingleLoop` encoding + PDKind unrolling overflow the default 8 MiB
/// stack during recursive `Arc<ChcExpr>` Drop. 128 MiB matches the portfolio
/// solver thread budget and handles expression trees of depth 500K+.
pub(crate) const ADAPTIVE_SOLVER_STACK_SIZE: usize = 128 * 1024 * 1024;

/// Adaptive portfolio solver configuration.
#[derive(Debug, Clone)]
pub struct AdaptiveConfig {
    /// Total time budget for solving (default: 27s)
    pub(crate) time_budget: Duration,
    /// Enable verbose output
    pub(crate) verbose: bool,
    /// Enable extra runtime validation of engine results (default: false).
    ///
    /// Safe results returned directly from the adaptive layer are always
    /// validated, matching the portfolio's mandatory Safe-validation contract.
    /// When this flag is true, direct-engine Unsafe results are also re-verified
    /// by a fresh solver during adaptive search. When false, adaptive strategy
    /// selection may accept raw Unsafe candidates directly, but
    /// `AdaptivePortfolio::solve()` still re-validates any final Unsafe before
    /// exposing `VerifiedChcResult::Unsafe`.
    pub validate: bool,
    /// Skip classification and use default portfolio
    pub(crate) skip_classification: bool,
    /// Force single-engine PDR with TLA trace from `Z4_TRACE_FILE`.
    ///
    /// When true, bypasses classification and runs a single PDR solver
    /// with `enable_tla_trace` wired from the environment. This avoids
    /// both parallel clobbering AND sequential overwrites from multiple
    /// engines, while still validating results through the verified pipeline.
    ///
    /// Part of #5811: route trace-mode through VerifiedChcResult.
    pub(crate) trace_mode: bool,
    /// User-provided lemma hints injected into all PDR engines.
    ///
    /// These are merged with built-in hint providers at startup/restart.
    /// See [`PdrConfig::user_hints`] for details.
    pub user_hints: Vec<LemmaHint>,
    /// User-provided runtime hint providers injected into all PDR engines.
    ///
    /// These are called alongside built-in providers. See [`PdrConfig::user_hint_providers`].
    pub user_hint_providers: HintProviders,
    /// When true, emit periodic progress lines to stderr (~5s interval).
    ///
    /// CHC progress lines report the current engine phase, elapsed time,
    /// and classification. Uses the `c` comment prefix for compatibility.
    pub progress_enabled: bool,
}

impl Default for AdaptiveConfig {
    fn default() -> Self {
        Self {
            time_budget: DEFAULT_SOLVE_BUDGET,
            verbose: false,
            validate: false,
            skip_classification: false,
            trace_mode: false,
            user_hints: Vec::new(),
            user_hint_providers: HintProviders::default(),
            progress_enabled: false,
        }
    }
}

impl AdaptiveConfig {
    /// Create an adaptive config with the given time budget and verbosity.
    pub fn with_budget(time_budget: Duration, verbose: bool) -> Self {
        Self {
            time_budget,
            verbose,
            ..Self::default()
        }
    }

    /// Enable trace mode: single-engine PDR with TLA trace from `Z4_TRACE_FILE`.
    ///
    /// Runs a single PDR solver to avoid multiple engines clobbering the
    /// trace file, while still validating through the verified pipeline.
    ///
    /// Part of #5811.
    #[must_use]
    pub fn with_trace_mode(mut self, trace: bool) -> Self {
        self.trace_mode = trace;
        self
    }

    /// Builder: add user-provided lemma hints.
    #[must_use]
    pub fn with_user_hints(mut self, hints: Vec<LemmaHint>) -> Self {
        self.user_hints = hints;
        self
    }

    /// Builder: add user-provided runtime hint providers.
    #[must_use]
    pub fn with_user_hint_providers(mut self, providers: HintProviders) -> Self {
        self.user_hint_providers = providers;
        self
    }
}

/// Adaptive portfolio solver for CHC problems.
///
/// Classifies problems and selects appropriate solving strategy
/// for bounded execution scenarios like CHC-COMP (30s timeout).
pub struct AdaptivePortfolio {
    /// The original problem (may contain Array-sorted predicate parameters).
    /// Used for PDR which has native array MBP support.
    pub(crate) problem: ChcProblem,
    /// Scalarized problem where constant-index Array params are expanded to scalars.
    /// Used for engines without native array support (Kind, TRL, TPA).
    /// `None` if the problem has no scalarizable arrays.
    scalarized_problem: Option<ChcProblem>,
    pub(crate) config: AdaptiveConfig,
    /// Structured decision logger for observability. Active only when
    /// `Z4_DECISION_LOG` environment variable is set.
    pub(crate) decision_log: DecisionLog,
    /// Accumulated CHC statistics from all engine runs.
    ///
    /// Updated via [`accumulate_stats`](Self::accumulate_stats) from each PDR
    /// solve attempt. Read via [`statistics`](Self::statistics) after `solve()`
    /// completes. Part of #4710 -- CHC stats envelope observability.
    accumulated_stats: Mutex<ChcStatistics>,
}

impl Drop for AdaptivePortfolio {
    fn drop(&mut self) {
        std::mem::take(&mut self.problem).iterative_drop();
        if let Some(problem) = self.scalarized_problem.take() {
            problem.iterative_drop();
        }
    }
}

impl AdaptivePortfolio {
    /// Create a new adaptive portfolio solver.
    ///
    /// # Contracts
    ///
    /// REQUIRES: `problem` is a valid ChcProblem with at least one clause.
    ///
    /// ENSURES: Returns a solver ready to invoke `solve()`.
    pub fn new(problem: ChcProblem, config: AdaptiveConfig) -> Self {
        // Part of #6047: keep the original (non-scalarized) problem for PDR,
        // which has native array MBP support and doesn't need scalarization.
        // Scalarize a separate copy for engines that need it (Kind, TRL, TPA).
        // This avoids the arity explosion from scalarizing BV-indexed arrays
        // (e.g., zani harnesses go from 68 to 191 params per predicate).
        let mut scalarized = problem.clone();
        scalarized.try_scalarize_const_array_selects();
        let scalarized_problem = if scalarized
            .predicates()
            .iter()
            .zip(problem.predicates().iter())
            .any(|(s, o)| s.arity() != o.arity())
        {
            // Scalarization changed the problem — keep both versions
            Some(scalarized)
        } else {
            // No change — no Array params to scalarize
            None
        };
        Self {
            problem,
            scalarized_problem,
            config,
            decision_log: DecisionLog::from_env(),
            accumulated_stats: Mutex::new(ChcStatistics::default()),
        }
    }

    /// Return a snapshot of accumulated CHC statistics.
    ///
    /// Call this after [`solve()`](Self::solve) to retrieve counters collected
    /// during all internal PDR engine runs. The statistics are additive across
    /// probe, retry, and portfolio stages.
    /// Get a reference to the original (non-scalarized) CHC problem.
    ///
    /// Used for certificate output: invariant models reference predicate IDs
    /// from the original problem and need its metadata (predicate names,
    /// argument sorts) to generate SMT-LIB formatted certificates.
    pub fn problem(&self) -> &ChcProblem {
        &self.problem
    }

    pub fn statistics(&self) -> ChcStatistics {
        self.accumulated_stats
            .lock()
            .expect("invariant: stats mutex not poisoned")
            .clone()
    }

    /// Merge stats from a PDR solve attempt into the accumulated counters.
    pub(crate) fn accumulate_stats(&self, solver_stats: &SolverStats) {
        let chc_stats: ChcStatistics = solver_stats.clone().into();
        self.accumulated_stats
            .lock()
            .expect("invariant: stats mutex not poisoned")
            .merge(&chc_stats);
    }

    /// Get the scalarized problem for non-PDR engines (Kind, TRL, TPA).
    /// Falls back to the original problem if no scalarization was needed.
    pub(crate) fn scalarized_problem(&self) -> &ChcProblem {
        self.scalarized_problem.as_ref().unwrap_or(&self.problem)
    }

    /// Apply user hints and providers from the adaptive config to a PdrConfig.
    pub(crate) fn apply_user_hints(&self, pdr: &mut PdrConfig) {
        if !self.config.user_hints.is_empty() {
            pdr.user_hints = self.config.user_hints.clone();
        }
        if !self.config.user_hint_providers.0.is_empty() {
            pdr.user_hint_providers = self.config.user_hint_providers.clone();
        }
    }

    /// Apply user hints and providers to all PDR engines in a portfolio config.
    fn apply_user_hints_portfolio(&self, config: &mut PortfolioConfig) {
        if !self.config.user_hints.is_empty() {
            config.set_pdr_user_hints(self.config.user_hints.clone());
        }
        if !self.config.user_hint_providers.0.is_empty() {
            config.set_pdr_user_hint_providers(self.config.user_hint_providers.clone());
        }
    }

    /// Run a portfolio solver with user hints applied.
    pub(crate) fn run_portfolio(&self, mut config: PortfolioConfig) -> PortfolioResult {
        self.apply_user_hints_portfolio(&mut config);
        PortfolioSolver::new(self.problem.clone(), config).solve()
    }

    /// Solve the CHC problem using adaptive strategy selection.
    ///
    /// Returns a `VerifiedChcResult` where Safe results have been validated
    /// by the portfolio's validation pipeline.
    ///
    /// # Contracts
    ///
    /// REQUIRES: `self.problem` is a valid ChcProblem (validated during construction).
    ///
    /// ENSURES: If `VerifiedChcResult::Safe(inv)` is returned:
    ///          1. The invariant satisfies all clauses in `self.problem`
    ///          2. Solving completed within `self.config.time_budget` (if set)
    ///
    /// ENSURES: If `VerifiedChcResult::Unsafe(cex)` is returned:
    ///          1. The counterexample witnesses reachability to a query clause
    ///
    /// ENSURES: `VerifiedChcResult::Unknown` is returned if:
    ///          - No strategy could determine satisfiability within the budget
    pub fn solve(&self) -> crate::VerifiedChcResult {
        // Run on a dedicated thread with a large stack to prevent stack
        // overflow from deep Arc<ChcExpr> recursive Drop (#6847).
        // The adaptive solver runs probe PDR, Kind, and retry engines
        // directly (not via portfolio thread spawning), so the calling
        // thread's stack must be large enough for deep expression trees
        // created by SingleLoop encoding + PDKind unrolling.
        std::thread::scope(|scope| {
            match std::thread::Builder::new()
                .name("z4-adaptive-solver".to_string())
                .stack_size(ADAPTIVE_SOLVER_STACK_SIZE)
                .spawn_scoped(scope, || {
                    let (result, evidence) = self.solve_internal();
                    self.finalize_verified_result(result, evidence)
                }) {
                Ok(handle) => match handle.join() {
                    Ok(result) => result,
                    // Re-propagate the original panic payload so that
                    // try_solve()'s catch_z4_panics can classify it (#6847).
                    Err(payload) => std::panic::resume_unwind(payload),
                },
                Err(_) => {
                    // Fallback: run on calling thread if spawn fails
                    let (result, evidence) = self.solve_internal();
                    self.finalize_verified_result(result, evidence)
                }
            }
        })
    }

    /// Panic-safe variant of [`solve`](Self::solve).
    ///
    /// Catches z4-internal panics (sort mismatches, verification failures, BUG
    /// markers) and returns them as [`ChcError::Internal`]. Non-z4 panics
    /// (index out of bounds, assertion failures) propagate normally via
    /// `resume_unwind`.
    ///
    /// Consumers (zani, tla2) should prefer this over wrapping `solve()` in
    /// their own `catch_unwind` because this uses the canonical z4 panic
    /// classifier (`is_z4_panic_reason`).
    ///
    /// # Errors
    ///
    /// Returns [`ChcError::Internal`] if a z4-classified panic is caught.
    pub fn try_solve(&self) -> crate::ChcResult<crate::VerifiedChcResult> {
        z4_core::catch_z4_panics(
            std::panic::AssertUnwindSafe(|| Ok(self.solve())),
            |reason| Err(crate::ChcError::Internal(reason)),
        )
    }

    fn solve_internal(&self) -> (PortfolioResult, ValidationEvidence) {
        // Compute a global deadline once for cumulative budget enforcement (#7034).
        let deadline = if self.config.time_budget.is_zero() {
            None
        } else {
            Some(Instant::now() + self.config.time_budget)
        };

        // Trace mode: single PDR with TLA trace, validated through the
        // same pipeline as normal results. Part of #5811.
        if self.config.trace_mode {
            return (
                self.solve_trace_mode(),
                ValidationEvidence::FullVerification,
            );
        }

        // Skip classification if requested
        if self.config.skip_classification {
            return (self.solve_default(), ValidationEvidence::FullVerification);
        }

        // Classify the problem
        let features = ProblemClassifier::classify(&self.problem);

        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: Problem classified as {} ({} preds, {} clauses, linear={}, \
                 single_pred={}, cycles={}, arrays={}, real={}, \
                 trans={}, facts={}, queries={}, entry_exit={}, phase_bounded={:?}, \
                 sccs={}, max_scc={}, dag_depth={}, max_vars={}, mean_vars={:.1}, \
                 mul={}, moddiv={}, ite={}, self_loop={:.2}, max_arity={})",
                features.class,
                features.num_predicates,
                features.num_clauses,
                features.is_linear,
                features.is_single_predicate,
                features.has_cycles,
                features.uses_arrays,
                features.uses_real,
                features.num_transitions,
                features.num_facts,
                features.num_queries,
                features.is_entry_exit_only,
                features.phase_bounded_depth,
                features.scc_count,
                features.max_scc_size,
                features.dag_depth,
                features.max_clause_variables,
                features.mean_clause_variables,
                features.has_multiplication,
                features.has_mod_div,
                features.has_ite,
                features.self_loop_ratio,
                features.max_predicate_arity,
            );
        }

        // Log classification decision if decision logging is active.
        let class_name = format!("{}", features.class);

        // Pre-strategy: Try algebraic invariant synthesis from polynomial
        // closed forms. This handles accumulator/polynomial patterns that
        // PDR and other engines cannot solve (e.g., sum = i*(i-1)/2).
        // Algebraic synthesis is fast (<100ms) and runs on the original
        // problem shape (before preprocessing destroys self-loop structure).
        // Part of #7897, #7931.
        if !matches!(features.class, ProblemClass::EntryExitOnly) {
            use crate::algebraic_invariant::AlgebraicResult;
            use crate::pdr::counterexample::Counterexample;

            let alg_start = Instant::now();
            match crate::algebraic_invariant::try_algebraic_solve(
                &self.problem,
                self.config.verbose,
            ) {
                AlgebraicResult::Safe(model) => {
                    let alg_elapsed = alg_start.elapsed().as_secs_f64();
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: Algebraic invariant synthesis succeeded in {:.3}s",
                            alg_elapsed,
                        );
                    }
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "algebraic_synthesis",
                        gate_result: true,
                        gate_reason: "polynomial closed form".to_string(),
                        budget_secs: 0.1,
                        elapsed_secs: alg_elapsed,
                        result: "safe",
                        lemmas_learned: 0,
                        max_frame: 0,
                    });
                    return (
                        PortfolioResult::Safe(model),
                        ValidationEvidence::FullVerification,
                    );
                }
                AlgebraicResult::Unsafe => {
                    let alg_elapsed = alg_start.elapsed().as_secs_f64();
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: Algebraic synthesis detected UNSAFE in {:.3}s",
                            alg_elapsed,
                        );
                    }
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "algebraic_synthesis",
                        gate_result: true,
                        gate_reason: "concrete counterexample from algebraic invariant".to_string(),
                        budget_secs: 0.1,
                        elapsed_secs: alg_elapsed,
                        result: "unsafe",
                        lemmas_learned: 0,
                        max_frame: 0,
                    });
                    return (
                        PortfolioResult::Unsafe(Counterexample {
                            steps: Vec::new(),
                            witness: None,
                        }),
                        ValidationEvidence::AlgebraicUnsafe,
                    );
                }
                AlgebraicResult::NotApplicable if self.problem.has_bv_sorts() => {
                    // BV problems: the original problem has BvAdd/BvMul ops that
                    // recurrence analysis cannot handle. Apply BvToInt + DeadParamElim
                    // (without BvToBool which bitblasts to 96 Bool args) and retry.
                    // This is the same pipeline as portfolio's try_algebraic_prepass
                    // but runs BEFORE the quad-lane to avoid thread-join blocking
                    // that causes the result to be lost even when synthesis succeeds.
                    // Part of #7931.
                    let bv_to_int_problem = {
                        let pipeline = TransformationPipeline::new()
                            .with(BvToIntAbstractor::new().with_verbose(self.config.verbose))
                            .with(DeadParamEliminator::new().with_verbose(self.config.verbose));
                        pipeline.transform(self.problem.clone()).problem
                    };
                    match crate::algebraic_invariant::try_algebraic_solve(
                        &bv_to_int_problem,
                        self.config.verbose,
                    ) {
                        AlgebraicResult::Safe(model) => {
                            let alg_elapsed = alg_start.elapsed().as_secs_f64();
                            if self.config.verbose {
                                safe_eprintln!(
                                    "Adaptive: Algebraic invariant synthesis succeeded (BvToInt) in {:.3}s",
                                    alg_elapsed,
                                );
                            }
                            self.decision_log.log_decision(DecisionEntry {
                                stage: "algebraic_synthesis_bvtoint",
                                gate_result: true,
                                gate_reason: "polynomial closed form via BvToInt".to_string(),
                                budget_secs: 0.1,
                                elapsed_secs: alg_elapsed,
                                result: "safe",
                                lemmas_learned: 0,
                                max_frame: 0,
                            });
                            return (
                                PortfolioResult::Safe(model),
                                ValidationEvidence::FullVerification,
                            );
                        }
                        AlgebraicResult::Unsafe => {
                            let alg_elapsed = alg_start.elapsed().as_secs_f64();
                            if self.config.verbose {
                                safe_eprintln!(
                                    "Adaptive: Algebraic synthesis (BvToInt) detected UNSAFE in {:.3}s",
                                    alg_elapsed,
                                );
                            }
                            self.decision_log.log_decision(DecisionEntry {
                                stage: "algebraic_synthesis_bvtoint",
                                gate_result: true,
                                gate_reason:
                                    "concrete counterexample from algebraic invariant (BvToInt)"
                                        .to_string(),
                                budget_secs: 0.1,
                                elapsed_secs: alg_elapsed,
                                result: "unsafe",
                                lemmas_learned: 0,
                                max_frame: 0,
                            });
                            return (
                                PortfolioResult::Unsafe(Counterexample {
                                    steps: Vec::new(),
                                    witness: None,
                                }),
                                ValidationEvidence::AlgebraicUnsafe,
                            );
                        }
                        AlgebraicResult::NotApplicable => {
                            self.decision_log.log_decision(DecisionEntry {
                                stage: "algebraic_synthesis",
                                gate_result: false,
                                gate_reason: "not applicable or validation failed (incl. BvToInt)"
                                    .to_string(),
                                budget_secs: 0.1,
                                elapsed_secs: alg_start.elapsed().as_secs_f64(),
                                result: "skipped",
                                lemmas_learned: 0,
                                max_frame: 0,
                            });
                        }
                    }
                }
                AlgebraicResult::NotApplicable => {
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "algebraic_synthesis",
                        gate_result: false,
                        gate_reason: "not applicable or validation failed".to_string(),
                        budget_secs: 0.1,
                        elapsed_secs: alg_start.elapsed().as_secs_f64(),
                        result: "skipped",
                        lemmas_learned: 0,
                        max_frame: 0,
                    });
                }
            }
        }

        // Select and run appropriate strategy.
        //
        // #7930: Complex problem classes MUST use specialized solve paths
        // (solve_complex_loop, solve_multi_pred_linear, solve_multi_pred_complex)
        // with DT-aware guards (max_escalation_level cap, Kind skip), budget
        // management, and deadline enforcement. Do NOT collapse these arms
        // into a single learned-selector call -- that bypasses DT+BV guards
        // and causes canary timeouts. Regressed twice (bec6a4ff9, 3e7b66b16)
        // and fixed twice (aeb44ab8d, this commit).
        let strategy_start = Instant::now();
        let budget_secs = self.config.time_budget.as_secs_f64();

        let (result, evidence) = match features.class {
            ProblemClass::EntryExitOnly => (
                self.solve_entry_exit_only(&features),
                ValidationEvidence::TrivialProblem,
            ),
            ProblemClass::Trivial => (
                self.solve_trivial(&features, deadline),
                ValidationEvidence::FullVerification,
            ),
            ProblemClass::SimpleLoop => self.solve_simple_loop_with_evidence(&features, deadline),
            ProblemClass::ComplexLoop => {
                // All complex loops use the full staging pipeline. For multi-
                // predicate problems (2+ preds), solve_complex_loop runs a
                // non-inlined PDR pre-stage before the portfolio to preserve
                // per-predicate structure that clause inlining would destroy.
                let result = self.solve_complex_loop(&features, deadline);
                // #7983: BMC counterexamples are constructively sound —
                // the SMT solver found a satisfying assignment to the
                // exact reachability encoding. Skip re-verification which
                // times out for deep traces (depth >=22).
                let evidence = if matches!(result, PortfolioResult::Unsafe(_)) {
                    ValidationEvidence::BmcCounterexample
                } else {
                    ValidationEvidence::FullVerification
                };
                (result, evidence)
            }
            ProblemClass::MultiPredLinear => self.solve_multi_pred_linear(&features, deadline),
            ProblemClass::MultiPredComplex => (
                self.solve_multi_pred_complex(&features, deadline),
                ValidationEvidence::FullVerification,
            ),
        };

        // Log the overall strategy decision.
        self.decision_log.log_decision(DecisionEntry {
            stage: "strategy_dispatch",
            gate_result: true,
            gate_reason: class_name,
            budget_secs,
            elapsed_secs: strategy_start.elapsed().as_secs_f64(),
            result: Self::result_to_str(&result),
            lemmas_learned: 0,
            max_frame: 0,
        });

        (result, evidence)
    }

    /// Final verified-result boundary for adaptive solving.
    ///
    /// `solve_internal()` is allowed to use the lighter-weight adaptive
    /// acceptance policy while exploring strategies. Before returning the public
    /// `VerifiedChcResult`, however, any `Unsafe` must be re-validated so the
    /// verified wrapper's contract holds even when `AdaptiveConfig.validate` is
    /// `false`.
    fn finalize_verified_result(
        &self,
        result: PortfolioResult,
        evidence: ValidationEvidence,
    ) -> crate::VerifiedChcResult {
        match result {
            PortfolioResult::Unsafe(cex) => {
                if matches!(
                    evidence,
                    ValidationEvidence::AlgebraicUnsafe | ValidationEvidence::BmcCounterexample
                ) {
                    // Constructive proofs: algebraic synthesis or BMC both
                    // produce counterexamples that are sound by construction.
                    // Algebraic: closed-form recurrence + concrete witness.
                    // BMC: satisfying assignment to init ∧ trans^k ∧ query.
                    // Re-verification would time out for deep BMC traces.
                    crate::VerifiedChcResult::from_validated(PortfolioResult::Unsafe(cex), evidence)
                } else if matches!(evidence, ValidationEvidence::TrivialProblem)
                    && self.problem.predicates().is_empty()
                    && cex.steps.is_empty()
                {
                    crate::VerifiedChcResult::from_validated(
                        PortfolioResult::Unsafe(cex),
                        ValidationEvidence::TrivialProblem,
                    )
                } else if self.validate_final_unsafe_result(&cex) {
                    crate::VerifiedChcResult::from_validated(
                        PortfolioResult::Unsafe(cex),
                        ValidationEvidence::CounterexampleVerification,
                    )
                } else {
                    tracing::debug!(
                        "Adaptive: final Unsafe result failed verified-result validation, demoting to Unknown"
                    );
                    crate::VerifiedChcResult::from_validated(
                        PortfolioResult::Unknown,
                        ValidationEvidence::CounterexampleVerification,
                    )
                }
            }
            other => crate::VerifiedChcResult::from_validated(other, evidence),
        }
    }

    /// Returns the remaining time until the deadline, or None if unbounded.
    #[allow(clippy::single_option_map)]
    pub(crate) fn remaining_budget(&self, deadline: Option<Instant>) -> Option<Duration> {
        deadline.map(|d| d.saturating_duration_since(Instant::now()))
    }

    /// Returns true if the deadline has passed (budget exhausted).
    pub(crate) fn budget_exhausted(&self, deadline: Option<Instant>) -> bool {
        deadline.is_some_and(|d| Instant::now() >= d)
    }

    /// Convert a `PortfolioResult` to a decision log result string.
    pub(crate) fn result_to_str(result: &PortfolioResult) -> &'static str {
        match result {
            PortfolioResult::Safe(_) => "safe",
            PortfolioResult::Unsafe(_) => "unsafe",
            PortfolioResult::Unknown => "unknown",
            PortfolioResult::NotApplicable => "not_applicable",
        }
    }

    /// Solve using default portfolio (for comparison/fallback).
    fn solve_default(&self) -> PortfolioResult {
        let mut config = PortfolioConfig::default();
        config.parallel_timeout = if self.config.time_budget.is_zero() {
            None
        } else {
            Some(self.config.time_budget)
        };
        config.verbose = self.config.verbose;
        config.validate = self.config.validate;
        self.run_portfolio(config)
    }

    /// Build a `PortfolioConfig` with engines ordered by the learned selector.
    fn make_learned_portfolio_config(&self, deadline: Option<Instant>) -> PortfolioConfig {
        let features = ChcFeatureExtractor::extract(&self.problem);
        let selection = EngineSelector::select(&features);
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: Learned selector chose engine order: {} (reason: {})",
                selection
                    .engines
                    .iter()
                    .map(|e| e.name())
                    .collect::<Vec<_>>()
                    .join(", "),
                selection.reason,
            );
        }
        let portfolio_timeout = if self.config.time_budget.is_zero() {
            None
        } else {
            Some(
                self.remaining_budget(deadline)
                    .unwrap_or(self.config.time_budget),
            )
        };
        PortfolioConfig {
            engines: selection.engines,
            parallel: true,
            timeout: None,
            parallel_timeout: portfolio_timeout,
            verbose: self.config.verbose,
            validate: self.config.validate,
            enable_preprocessing: true,
        }
    }

    /// Solve using learned feature-based engine selection.
    pub(crate) fn solve_with_learned_selection(
        &self,
        deadline: Option<Instant>,
    ) -> PortfolioResult {
        let config = self.make_learned_portfolio_config(deadline);
        self.run_portfolio(config)
    }

    /// Hybrid: non-inlined PDR pre-stage then learned selection portfolio.
    ///
    /// NOTE: Superseded by the non-inlined PDR pre-stage integrated into
    /// `solve_complex_loop` (#7934). Retained for potential future use.
    #[allow(dead_code)]
    fn solve_with_non_inlined_pdr_then_learned(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> PortfolioResult {
        if features.num_predicates >= 2 && self.should_try_non_inlined_pdr(features) {
            let stage_budget = self.non_inlined_pdr_stage_budget(features, deadline);
            if !stage_budget.is_zero() {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Hybrid non-inlined PDR pre-stage ({} preds, {:.1}s budget)",
                        features.num_predicates,
                        stage_budget.as_secs_f64()
                    );
                }
                let mut pdr_config = Self::multi_pred_pdr_config(PdrConfig {
                    verbose: self.config.verbose,
                    solve_timeout: Some(stage_budget),
                    ..PdrConfig::default()
                })
                .with_tla_trace_from_env();
                self.apply_user_hints(&mut pdr_config);
                let pre_stage_start = Instant::now();
                let mut pdr = PdrSolver::new(self.problem.clone(), pdr_config);
                pdr.enable_tla_trace_from_config();
                let result = pdr.solve();
                let validated = self.validate_adaptive_result(result);
                if !matches!(validated, PdrResult::Unknown) {
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "hybrid_non_inlined_pdr",
                        gate_result: true,
                        gate_reason: format!("{} predicates", features.num_predicates),
                        budget_secs: stage_budget.as_secs_f64(),
                        elapsed_secs: pre_stage_start.elapsed().as_secs_f64(),
                        result: Self::result_to_str(&validated),
                        lemmas_learned: 0,
                        max_frame: 0,
                    });
                    return validated;
                }
                let pool = pdr.export_lemmas();
                let elapsed = pre_stage_start.elapsed();
                self.decision_log.log_decision(DecisionEntry {
                    stage: "hybrid_non_inlined_pdr",
                    gate_result: true,
                    gate_reason: format!("{} predicates, unknown", features.num_predicates),
                    budget_secs: stage_budget.as_secs_f64(),
                    elapsed_secs: elapsed.as_secs_f64(),
                    result: "unknown",
                    lemmas_learned: pool.len(),
                    max_frame: 0,
                });
                if !self.budget_exhausted(deadline) {
                    let mut config = self.make_learned_portfolio_config(deadline);
                    if !pool.is_empty() {
                        for engine in &mut config.engines {
                            if let EngineConfig::Pdr(ref mut pdr_cfg) = engine {
                                pdr_cfg.lemma_hints = Some(pool.clone());
                            }
                        }
                    }
                    return self.run_portfolio(config);
                }
                return PortfolioResult::Unknown;
            }
        }
        self.solve_with_learned_selection(deadline)
    }

    /// Solve in trace mode: single PDR with TLA trace, validated.
    ///
    /// Runs one PDR solver with `enable_tla_trace` from `Z4_TRACE_FILE`,
    /// validates the result via `validate_adaptive_result()`, and converts to
    /// `PortfolioResult` for the standard `VerifiedChcResult` wrapping.
    ///
    /// This replaces the old `main.rs` trace-mode bypass that returned raw
    /// `PdrResult` without verification. Part of #5811.
    fn solve_trace_mode(&self) -> PortfolioResult {
        let mut pdr_config = PdrConfig::production(self.config.verbose).with_tla_trace_from_env();
        self.apply_user_hints(&mut pdr_config);
        let trace_path = pdr_config.tla_trace_path.clone();

        // Wire cancellation token for budget enforcement.
        // The timer thread uses park_timeout so it can be woken early
        // when the solve completes, avoiding orphaned sleeping threads
        // in library mode (#6231).
        let timer_handle = if !self.config.time_budget.is_zero() {
            let token = crate::CancellationToken::new();
            let watchdog = token.clone();
            let budget = self.config.time_budget;
            let cancelled = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
            let cancel_flag = cancelled.clone();
            let handle = std::thread::spawn(move || {
                std::thread::park_timeout(budget);
                if !cancel_flag.load(std::sync::atomic::Ordering::Acquire) {
                    watchdog.cancel();
                }
            });
            pdr_config = pdr_config.with_cancellation_token(Some(token));
            Some((handle, cancelled))
        } else {
            None
        };

        // Reserve Z4_TRACE_FILE for the top-level PDR trace only.
        // Nested SAT/DPLL helpers inside CHC solving also honor this env var;
        // if left in place, they reopen the same JSONL path and corrupt the
        // trace with mixed CDCL/PDR records.
        if pdr_config.enable_tla_trace {
            std::env::remove_var("Z4_TRACE_FILE");
        }
        let result = PdrSolver::solve_problem(&self.problem, pdr_config);
        if let Some(path) = trace_path.as_deref() {
            std::env::set_var("Z4_TRACE_FILE", path);
        }

        // Cancel the watchdog timer early — solve is done.
        if let Some((handle, cancelled)) = timer_handle {
            cancelled.store(true, std::sync::atomic::Ordering::Release);
            handle.thread().unpark();
        }

        let validated = self.validate_adaptive_result(result);

        // Convert PdrResult to PortfolioResult (ChcEngineResult)
        match validated {
            PdrResult::Safe(model) => PortfolioResult::Safe(model),
            PdrResult::Unsafe(cex) => PortfolioResult::Unsafe(cex),
            PdrResult::Unknown | PdrResult::NotApplicable => PortfolioResult::Unknown,
        }
    }

    // Engine methods (solve_entry_exit_only, solve_trivial, try_alternative_engine_budgeted,
    // try_kind, try_synthesis) are in adaptive_engines.rs.
    // BV strategy methods are in adaptive_bv_strategy.rs.
    // Multi-pred strategy methods are in adaptive_multi_pred.rs.
    // Validation methods are in adaptive_validation.rs.
}

#[cfg(test)]
impl AdaptivePortfolio {
    /// Get the classified features for this problem (test-only).
    pub(crate) fn features(&self) -> ProblemFeatures {
        ProblemClassifier::classify(&self.problem)
    }
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "adaptive_tests.rs"]
mod tests;
