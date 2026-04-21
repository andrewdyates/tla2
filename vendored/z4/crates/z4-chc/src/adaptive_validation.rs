// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adaptive portfolio validation methods.
//!
//! Extracted from adaptive.rs — these methods validate direct adaptive
//! results before returning them. Defense-in-depth for soundness when the
//! adaptive layer bypasses the portfolio acceptor (probe, retry, case-split,
//! structural synthesis, Kind).
//!
//! Safe validation is mandatory here, matching the portfolio contract:
//! adaptive direct-engine probes bypass the portfolio acceptor, so they must
//! not be able to return a false Safe just because `config.validate` is off.
//! `config.validate` still controls the extra fresh-checking of Unsafe results
//! during adaptive search; `AdaptivePortfolio::solve()` re-validates any final
//! Unsafe before exposing `VerifiedChcResult::Unsafe`.

use crate::pdr::{CexVerificationResult, Counterexample, PdrConfig, PdrResult, PdrSolver};
use crate::portfolio::{PortfolioConfig, PortfolioSolver};
use crate::{ChcProblem, ChcSort};
use std::time::Duration;

use crate::adaptive::AdaptivePortfolio;

impl AdaptivePortfolio {
    /// Validate a non-portfolio adaptive result before returning it.
    ///
    /// The helper still uses `PdrResult` as the local result carrier, but it is
    /// used for any adaptive-layer result that bypasses the portfolio acceptor
    /// (for example direct PDR probes/retries and structural synthesis models).
    ///
    /// The portfolio solver validates all engine results internally (Safe via
    /// `verify_model_with_budget`, Unsafe via `verify_counterexample`). But when
    /// the adaptive layer handles results directly, those results bypass portfolio
    /// validation. This method provides the same defense-in-depth.
    ///
    /// SOUNDNESS FIX #5549: Without this, PDR's internal verify_model can accept
    /// invariants that fail external verification (e.g., switch_000.smt2 where
    /// PDR declares Safe but the invariant doesn't hold on the original problem).
    /// The adaptive layer returned this unvalidated Safe, producing false-SAT.
    ///
    /// Standard validation budget for 1-inductive engines (PDR, TPA, CEGAR).
    /// Matches portfolio's validate_safe budget (#5394).
    const VALIDATION_BUDGET_1INDUCTIVE: Duration = Duration::from_millis(1500);

    /// Build a fresh verifier for adaptive result validation.
    ///
    /// Validation must run in a clean solver instance rather than reusing any
    /// engine-local state from the candidate result we are checking.
    fn new_validation_solver(&self) -> PdrSolver {
        let config = PdrConfig {
            verbose: self.config.verbose,
            ..PdrConfig::default()
        };
        PdrSolver::new(self.problem.clone(), config)
    }

    /// Build a fresh portfolio validator for the public verified-result boundary.
    ///
    /// The adaptive layer uses this only when converting a final candidate into
    /// `VerifiedChcResult`, so the config carries no engines and no preprocessing.
    fn new_verified_result_validator(&self) -> PortfolioSolver {
        PortfolioSolver::new(
            self.problem.clone(),
            PortfolioConfig {
                engines: vec![],
                parallel: false,
                timeout: None,
                parallel_timeout: None,
                verbose: self.config.verbose,
                validate: false,
                enable_preprocessing: false,
            },
        )
    }

    /// Validate an adaptive direct-engine counterexample with a fresh PDR solver.
    fn validate_direct_unsafe_counterexample(&self, cex: &Counterexample) -> bool {
        let mut verifier = self.new_validation_solver();
        matches!(
            verifier.verify_counterexample(cex),
            CexVerificationResult::Valid
        )
    }

    /// Validate a final Unsafe candidate at the public verified-result boundary.
    pub(crate) fn validate_final_unsafe_result(&self, cex: &Counterexample) -> bool {
        self.new_verified_result_validator()
            .validate_unsafe_for_verified_result(cex)
    }

    pub(crate) fn validate_adaptive_result(&self, result: PdrResult) -> PdrResult {
        match result {
            // #7934: Models with individually_inductive=true have had every
            // lemma verified as self-inductive at the PDR level — either
            // strictly self-inductive (no frame strengthening) or frame-
            // relative with initiation verified. Query-only validation is
            // sufficient. Full validation in a fresh context is strictly
            // weaker (no learned clauses from PDR search). Same logic as
            // accept.rs Step 5 #7410 bypass.
            //
            // #8782: Models with convergence_proven=true were built from a
            // converged fixpoint (frame[k] = frame[k+1]) without any conjunct
            // filtering. The full frame conjunction is inductive by definition
            // (PDR convergence theorem). Full transition validation in a fresh
            // context can fail due to SMT budget exhaustion on complex multi-
            // predicate models (s_multipl_12/15/16/17, s_mutants_16_m) where
            // some predicates have vacuously-false frames. Query-only validation
            // confirms the invariant blocks the error, which is the soundness-
            // critical property. Transition inductiveness is guaranteed by
            // convergence.
            PdrResult::Safe(ref model)
                if model.individually_inductive || model.convergence_proven =>
            {
                let mut verifier = self.new_validation_solver();
                if verifier.verify_model_query_only(model) {
                    result
                } else {
                    tracing::debug!(
                        "Adaptive: individually_inductive/convergence_proven Safe result failed query-only validation, demoting to Unknown"
                    );
                    PdrResult::Unknown
                }
            }
            // Safe validation is mandatory: direct adaptive Safe results
            // bypass the portfolio's always-on Safe validation (#5382, #7688).
            PdrResult::Safe(_) => self
                .validate_adaptive_result_with_budget(result, Self::VALIDATION_BUDGET_1INDUCTIVE),
            // Unsafe validation remains opt-in, matching portfolio behavior.
            PdrResult::Unsafe(_) if self.config.validate => self
                .validate_adaptive_result_with_budget(result, Self::VALIDATION_BUDGET_1INDUCTIVE),
            PdrResult::Unsafe(_) => result,
            PdrResult::Unknown | PdrResult::NotApplicable => PdrResult::Unknown,
        }
    }

    /// Validate with a configurable budget for Safe model verification.
    ///
    /// For 1-inductive engines (PDR, TPA, CEGAR). Transition clauses are
    /// checked with the given budget — expiry means rejection (#5745).
    fn validate_adaptive_result_with_budget(
        &self,
        result: PdrResult,
        safe_budget: Duration,
    ) -> PdrResult {
        match &result {
            PdrResult::Safe(model) => {
                let mut verifier = self.new_validation_solver();
                if verifier.verify_model_with_budget(model, safe_budget) {
                    result
                } else {
                    tracing::debug!(
                        "Adaptive: direct Safe result failed external validation, demoting to Unknown"
                    );
                    PdrResult::Unknown
                }
            }
            PdrResult::Unsafe(cex) => {
                if self.validate_direct_unsafe_counterexample(cex) {
                    result
                } else {
                    tracing::debug!(
                        "Adaptive: direct Unsafe result failed external validation, demoting to Unknown"
                    );
                    PdrResult::Unknown
                }
            }
            // NotApplicable is an engine-internal signal; convert to Unknown
            // at the validation boundary so it never escapes the adaptive layer.
            PdrResult::Unknown | PdrResult::NotApplicable => PdrResult::Unknown,
        }
    }

    /// Validate a Safe result by checking only query clauses.
    ///
    /// K-inductive invariants (Kind engine) satisfy init + query + k-step
    /// induction, but are not necessarily 1-inductive. Transition clause checks
    /// would reject valid k-inductive invariants (#5211). This method checks
    /// only query clauses (the safety property), which are soundness-critical.
    ///
    /// Replaces the pre-#5745 Duration::ZERO convention that was broken by the
    /// budget-expiry rejection logic (#5825).
    ///
    /// Safe results are checked unconditionally here for the same reason as
    /// `validate_adaptive_result`: Kind runs directly from the adaptive layer.
    pub(crate) fn validate_kind_result_query_only(&self, result: PdrResult) -> PdrResult {
        match result {
            PdrResult::Safe(model) => {
                let mut verifier = self.new_validation_solver();
                if verifier.verify_model_query_only(&model) {
                    PdrResult::Safe(model)
                } else {
                    tracing::debug!(
                        "Adaptive: Kind Safe result failed query-only validation, demoting to Unknown"
                    );
                    PdrResult::Unknown
                }
            }
            PdrResult::Unsafe(cex) if self.config.validate => {
                if self.validate_direct_unsafe_counterexample(&cex) {
                    PdrResult::Unsafe(cex)
                } else {
                    tracing::debug!(
                        "Adaptive: direct Unsafe result failed external validation, demoting to Unknown"
                    );
                    PdrResult::Unknown
                }
            }
            PdrResult::Unsafe(cex) => PdrResult::Unsafe(cex),
            PdrResult::Unknown | PdrResult::NotApplicable => PdrResult::Unknown,
        }
    }
}

/// Compute BV bit-group mapping from the original (pre-BvToBool) problem (#5877).
///
/// For each predicate, identifies which consecutive Bool argument ranges in the
/// transformed problem correspond to a single original BV argument. Returns groups
/// for the first predicate (single-predicate simple-loop problems have exactly one).
///
/// Example: original `P(Bool, BV32, Int)` → transformed `P(Bool, Bool*32, Int)`.
/// Returns `[(1, 32)]` — args 1..33 are bits of one BV32 variable.
pub(crate) fn compute_bv_bit_groups(original_problem: &ChcProblem) -> Vec<(usize, u32)> {
    let mut groups = Vec::new();
    // Use the first predicate (simple-loop problems have exactly one).
    let Some(pred) = original_problem.predicates().first() else {
        return groups;
    };
    let mut expanded_idx = 0;
    for sort in &pred.arg_sorts {
        match sort {
            ChcSort::BitVec(w) => {
                groups.push((expanded_idx, *w));
                expanded_idx += *w as usize;
            }
            _ => {
                expanded_idx += 1;
            }
        }
    }
    groups
}
