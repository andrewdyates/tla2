// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Multi-predicate linear strategy methods for the adaptive portfolio solver.
//!
//! Contains multi-pred linear solving, failure-guided retry, portfolio config
//! building, and the non-inlined PDR gate.
//!
//! Companion: `adaptive_multi_pred_complex.rs` has `solve_complex_loop` and
//! `solve_multi_pred_complex`.

use crate::bmc::BmcConfig;
use crate::cegar::CegarConfig;
use crate::classifier::ProblemFeatures;
use crate::dar::DarConfig;
use crate::engine_config::ChcEngineConfig;
use crate::engine_result::ValidationEvidence;
use crate::failure_analysis::{FailureAnalysis, FailureGuide};
use crate::imc::ImcConfig;
use crate::kind::KindConfig;
use crate::lemma_pool::LemmaPool;
use crate::pdkind::PdkindConfig;
use crate::pdr::{PdrConfig, PdrResult, PdrSolver};
use crate::portfolio::{
    EngineConfig, PortfolioConfig, PortfolioResult, PortfolioSolver, PreprocessSummary,
};
use crate::tpa::TpaConfig;
use crate::trl::TrlConfig;
use std::time::{Duration, Instant};
use z4_core::TermStore;

use crate::adaptive::AdaptivePortfolio;
use crate::adaptive_decision_log::DecisionEntry;

impl AdaptivePortfolio {
    pub(crate) fn multi_pred_pdr_config(mut config: PdrConfig) -> PdrConfig {
        // Entry-CEGAR discharge can burn the whole adaptive budget on
        // multi-predicate arithmetic chains while repeatedly rejecting the same
        // near-inductive lemmas. Keep the entry check, but skip the expensive
        // discharge loop on these paths.
        config.use_entry_cegar_discharge = false;
        config
    }

    pub(crate) fn try_acyclic_array_bv_bmc_probe(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> Option<PortfolioResult> {
        if !features.is_linear
            || features.has_cycles
            || features.num_predicates <= 1
            || !features.uses_arrays
            || !self.problem.has_bv_sorts()
            || self.budget_exhausted(deadline)
        {
            return None;
        }

        let remaining = self
            .remaining_budget(deadline)
            .unwrap_or(Duration::from_secs(15));
        let stage_budget = if remaining <= Duration::from_secs(6) {
            remaining
        } else {
            remaining
                .mul_f64(0.85)
                .max(Duration::from_secs(6))
                .min(Duration::from_secs(13))
                .min(remaining)
        };
        if stage_budget.is_zero() {
            return None;
        }

        let depth = features.num_predicates.max(1);
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: Trying acyclic array/BV BMC probe (depth={}, timeout={:.1}s, per-depth=unbounded)",
                depth,
                stage_budget.as_secs_f64()
            );
        }

        let config = PortfolioConfig {
            engines: vec![EngineConfig::Bmc(BmcConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                max_depth: depth,
                acyclic_safe: true,
                // For bounded acyclic array/BV DAGs, the deepest exact query is
                // usually the expensive one. Let the portfolio-level timeout
                // enforce the budget instead of cutting off each depth early.
                per_depth_timeout: None,
            })],
            parallel: false,
            timeout: Some(stage_budget),
            parallel_timeout: None,
            verbose: self.config.verbose,
            validate: self.config.validate,
            // Inline the acyclic predicate chain first so the probe can return
            // a validation-friendly Safe result instead of an exhausted BMC
            // run with no invariant model.
            enable_preprocessing: true,
        };

        // This probe only needs chain-collapsing/inlining. Running the full
        // BvToBool+BvToInt preprocess stack on BV-indexed arrays can route the
        // exact acyclic BMC proof through BV back-translation and produce an
        // ill-typed Safe witness during query-only validation. Keep the
        // preprocessing BV-native here: local-var elimination, dead-param
        // elimination, and clause inlining still shrink the acyclic chain,
        // while the proof remains in the original BV/array domain.
        let summary = PreprocessSummary::build_bv_native(self.problem.clone(), self.config.verbose);
        let result = PortfolioSolver::from_summary(summary, config).solve();
        match result {
            PortfolioResult::Safe(_) | PortfolioResult::Unsafe(_) => Some(result),
            PortfolioResult::Unknown | PortfolioResult::NotApplicable => None,
        }
    }

    pub(crate) fn multi_pred_portfolio_timeout(remaining: Duration) -> Duration {
        const MIN_PORTFOLIO_BUDGET: Duration = Duration::from_secs(3);

        if remaining <= MIN_PORTFOLIO_BUDGET {
            return remaining;
        }

        remaining
            .mul_f64(0.7)
            .max(MIN_PORTFOLIO_BUDGET)
            .min(remaining)
    }

    pub(crate) fn multi_pred_probe_timeout(&self, deadline: Option<Instant>) -> Duration {
        match self.remaining_budget(deadline) {
            Some(remaining) => remaining.min(Duration::from_secs(5)),
            None => Duration::from_secs(5),
        }
    }

    pub(crate) fn multi_pred_retry_timeout(&self, deadline: Option<Instant>) -> Option<Duration> {
        self.remaining_budget(deadline)
            .or(Some(Duration::from_secs(10)))
    }

    /// Solve multi-predicate linear problems - PDR focused.
    ///
    /// Uses failure-guided retry: if portfolio returns Unknown, run a quick PDR
    /// probe with stats collection, analyze the failure, and retry with adjusted
    /// configuration.
    ///
    /// Part of #2082 - Extend failure-guided retry to multi-predicate paths.
    pub(super) fn solve_multi_pred_linear(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> (PortfolioResult, ValidationEvidence) {
        if self.config.verbose {
            safe_eprintln!("Adaptive: Using multi-pred linear strategy (PDR focused)");
        }

        // Stage 0: Try structural synthesis (< 1ms overhead on extra-small-lia)
        if let Some(result) = self.try_synthesis() {
            if self.config.verbose {
                safe_eprintln!("Adaptive: MultiPredLinear problem solved by structural synthesis");
            }
            return (result, ValidationEvidence::FullVerification);
        }

        // Stage 0.5: Exact BMC probe for acyclic array/BV DAGs.
        // Zani-style CHC often encode bounded basic-block chains with BV64
        // pointer state plus array memories. These problems are acyclic, so a
        // short original-problem BMC run can prove safety or find a bug before
        // the heavier non-inlined PDR and portfolio stages.
        if let Some(result) = self.try_acyclic_array_bv_bmc_probe(features, deadline) {
            if self.config.verbose {
                safe_eprintln!("Adaptive: Acyclic array/BV BMC probe solved the problem");
            }
            return (result, ValidationEvidence::FullVerification);
        }

        // Stage 1: Case-split preprocessing (#1306).
        // For problems with unconstrained constant arguments (like dillig12_m),
        // case-split can simplify the problem by partitioning based on mode
        // values. Keep the dedicated limit narrow so it cannot starve the later
        // PDR lane on longer phase chains.
        if self.config.verbose {
            safe_eprintln!("Adaptive: Trying case-split preprocessing (Stage 0)");
        }
        let mut case_split_config = Self::multi_pred_pdr_config(PdrConfig {
            max_iterations: 1000,
            max_obligations: 500_000,
            max_frames: 100,
            verbose: self.config.verbose,
            max_escalation_level: if features.uses_datatypes { 0 } else { 3 },
            // Cap case-split at 2s so the portfolio gets the bulk of the budget.
            // Case-split either finds a simple decomposition quickly or not at all;
            // spending more time here steals from TPA/PDKIND which need the budget
            // to converge on harder multi-predicate problems (#4751).
            // 5s budget: branches typically solve in <1s each; the extra time
            // covers merged-model verification which needs SMT checks on complex
            // guarded formulas (e.g., dillig12_m's quadratic invariant).
            solve_timeout: Some(Duration::from_secs(5)),
            ..PdrConfig::default()
        })
        .with_tla_trace_from_env();
        self.apply_user_hints(&mut case_split_config);
        let case_split_start = Instant::now();
        if let Some(result) = PdrSolver::try_case_split_solve(&self.problem, case_split_config) {
            // Validate case-split result (#5549 soundness fix)
            let validated = self.validate_adaptive_result(result);
            if !matches!(validated, PdrResult::Unknown) {
                self.decision_log.log_decision(DecisionEntry {
                    stage: "multi_pred_linear_case_split",
                    gate_result: true,
                    gate_reason: "case-split solved".to_string(),
                    budget_secs: 5.0,
                    elapsed_secs: case_split_start.elapsed().as_secs_f64(),
                    result: Self::result_to_str(&validated),
                    lemmas_learned: 0,
                    max_frame: 0,
                });
                return (validated, ValidationEvidence::FullVerification);
            }
        }
        self.decision_log.log_decision(DecisionEntry {
            stage: "multi_pred_linear_case_split",
            gate_result: true,
            gate_reason: "case-split returned none/unknown".to_string(),
            budget_secs: 5.0,
            elapsed_secs: case_split_start.elapsed().as_secs_f64(),
            result: "unknown",
            lemmas_learned: 0,
            max_frame: 0,
        });
        if self.config.verbose {
            safe_eprintln!("Adaptive: Case-split returned None, continuing to portfolio");
        }

        // Stage 1.25: direct Kind pre-pass.
        //
        // Kind uses query-only validation in the adaptive layer because its
        // proofs are k-inductive, not necessarily 1-inductive. Keep that
        // evidence explicit at the verified-result boundary, and run this
        // probe after case-split so it cannot starve the rest of the
        // multi-predicate pipeline on long phase-chain benchmarks.
        let allow_direct_kind_prepass = features.num_predicates <= 2 && features.dag_depth <= 2;
        if allow_direct_kind_prepass && !self.budget_exhausted(deadline) {
            // Cap the Kind prepass at 3s. Kind either converges quickly
            // (k=0,1,2) or it stalls indefinitely unrolling long transitions.
            // The portfolio already runs Kind in parallel with other engines,
            // so the prepass only needs to catch the easy wins. Previous cap
            // of 20s starved TPA/PDR/DAR on benchmarks like half_true_modif_m
            // and dillig12_m where Kind cannot converge but TPA can.
            let kind_budget = self
                .remaining_budget(deadline)
                .unwrap_or(Duration::from_secs(3))
                .min(Duration::from_secs(3));
            if !kind_budget.is_zero() {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Trying direct Kind before non-inlined PDR ({:.1}s budget)",
                        kind_budget.as_secs_f64()
                    );
                }
                if let Some(result) = self.try_kind(kind_budget) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: Direct Kind solved the multi-pred linear problem"
                        );
                    }
                    let evidence = if matches!(result, PortfolioResult::Unsafe(_)) {
                        ValidationEvidence::CounterexampleVerification
                    } else {
                        ValidationEvidence::QueryOnly
                    };
                    return (result, evidence);
                }
            }
        } else if self.config.verbose && !allow_direct_kind_prepass {
            safe_eprintln!(
                "Adaptive: Skipping direct Kind pre-pass for long multi-predicate chain (preds={}, dag_depth={})",
                features.num_predicates,
                features.dag_depth
            );
        }

        // Cross-engine lemma transfer pool (#7919). Populated by non-inlined PDR
        // when it returns Unknown, consumed by portfolio engines and retry.
        let mut transferred_pool: Option<LemmaPool> = None;

        // Stage 1.5: Run PDR on the original non-inlined problem for modular,
        // ITE-heavy, or long multi-predicate chains. Clause inlining can erase
        // the per-predicate structure these problems need for invariant discovery.
        //
        // self.problem is the ORIGINAL non-inlined problem. PdrSolver::new() on it
        // bypasses the portfolio's ClauseInliner preprocessing entirely.
        if self.should_try_non_inlined_pdr(features) && !self.budget_exhausted(deadline) {
            let stage_budget = self.non_inlined_pdr_stage_budget(features, deadline);
            if !stage_budget.is_zero() {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Trying non-inlined PDR before portfolio ({} predicates, {:.1}s budget)",
                        features.num_predicates,
                        stage_budget.as_secs_f64()
                    );
                }

                let mut pdr_config = Self::multi_pred_pdr_config(PdrConfig {
                    verbose: self.config.verbose,
                    solve_timeout: Some(stage_budget),
                    // #7930: Cap escalation for DT problems.
                    max_escalation_level: if features.uses_datatypes { 0 } else { 3 },
                    ..PdrConfig::default()
                })
                .with_tla_trace_from_env();
                // Re-enable Entry-CEGAR for deep multi-predicate chains in the
                // non-inlined PDR stage. multi_pred_pdr_config disables it to
                // avoid burning unbounded portfolio budget, but the non-inlined
                // stage already has a bounded solve_timeout.
                // Gate: dag_depth >= 4 or num_predicates >= 4. Deep chains like
                // gj2007_m_2 (5 preds, dag_depth=5) need CEGAR to propagate
                // invariants across predicate boundaries. Shallower chains
                // (s_multipl_13: 3 preds) solve faster without it.
                if features.dag_depth >= 4 || features.num_predicates >= 4 {
                    pdr_config.use_entry_cegar_discharge = true;
                }
                self.apply_user_hints(&mut pdr_config);
                let non_inlined_start = Instant::now();
                let mut pdr = PdrSolver::new(self.problem.clone(), pdr_config);
                pdr.enable_tla_trace_from_config();
                let result = pdr.solve();
                let validated = self.validate_adaptive_result(result);
                if !matches!(validated, PdrResult::Unknown) {
                    if self.config.verbose {
                        safe_eprintln!("Adaptive: Non-inlined PDR solved the problem");
                    }
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "multi_pred_linear_non_inlined_pdr",
                        gate_result: true,
                        gate_reason: format!("{} predicates", features.num_predicates),
                        budget_secs: stage_budget.as_secs_f64(),
                        elapsed_secs: non_inlined_start.elapsed().as_secs_f64(),
                        result: Self::result_to_str(&validated),
                        lemmas_learned: 0,
                        max_frame: 0,
                    });
                    return (validated, ValidationEvidence::FullVerification);
                }
                self.decision_log.log_decision(DecisionEntry {
                    stage: "multi_pred_linear_non_inlined_pdr",
                    gate_result: true,
                    gate_reason: format!("{} predicates, unknown", features.num_predicates),
                    budget_secs: stage_budget.as_secs_f64(),
                    elapsed_secs: non_inlined_start.elapsed().as_secs_f64(),
                    result: "unknown",
                    lemmas_learned: 0,
                    max_frame: 0,
                });
                // Export learned lemmas for cross-engine transfer (#7919).
                // Non-inlined PDR may have discovered useful lemmas even
                // though it could not prove safety within its budget.
                let pool = pdr.export_lemmas();
                if self.config.verbose && !pool.is_empty() {
                    safe_eprintln!(
                        "Adaptive: Exported {} lemmas from non-inlined PDR for cross-engine transfer",
                        pool.len()
                    );
                }
                transferred_pool = Some(pool);
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Non-inlined PDR returned Unknown, continuing to portfolio"
                    );
                }
            }
        }

        // Stage 2: Run mixed portfolio
        // Multi-predicate linear problems use PDR for joint invariant discovery,
        // plus PDKind via SingleLoop encoding for k-induction (Golem-style).
        // PDKind runs in parallel with other engines to avoid consuming budget
        // sequentially on spurious results (#2750).
        //
        // Budget check before portfolio (#7034)
        if self.budget_exhausted(deadline) {
            if self.config.verbose {
                safe_eprintln!("Adaptive: Budget exhausted after case-split, skipping portfolio");
            }
            return (
                PortfolioResult::Unknown,
                ValidationEvidence::FullVerification,
            );
        }

        // Use deadline-based remaining budget (#7034, supersedes #4751).
        // Propagate verbose flag to PDR engine configs (#1969)
        // Seed portfolio PDR engines with transferred lemma pool (#7919).
        //
        // #7930: For DT problems, cap escalation at level 0. PDR generalization
        // escalation is unproductive for Datatype sorts — DT needs SMT-level
        // constructor/selector reasoning, not LIA lemma generalization. Without
        // this cap, PDR spends 4x longer stagnating through escalation levels,
        // starving other engines of budget.
        let max_esc = if features.uses_datatypes { 0 } else { 3 };
        let mut pdr1 = Self::multi_pred_pdr_config(PdrConfig {
            verbose: self.config.verbose,
            max_escalation_level: max_esc,
            ..PdrConfig::default()
        });
        let mut pdr2 = Self::multi_pred_pdr_config(PdrConfig {
            verbose: self.config.verbose,
            max_escalation_level: max_esc,
            ..PdrConfig::portfolio_variant_with_splits()
        });
        if let Some(ref pool) = transferred_pool {
            if !pool.is_empty() {
                pdr1.lemma_hints = Some(pool.clone());
                pdr2.lemma_hints = Some(pool.clone());
            }
        }

        let mut config = self.multi_pred_linear_portfolio_config(pdr1, pdr2, features);

        // Use deadline for portfolio timeout (#7034).
        if let Some(ref mut timeout) = config.parallel_timeout {
            if let Some(remaining) = self.remaining_budget(deadline) {
                *timeout = Self::multi_pred_portfolio_timeout(remaining);
            }
        }

        let portfolio_start = Instant::now();
        let portfolio_result = self.run_portfolio(config);

        self.decision_log.log_decision(DecisionEntry {
            stage: "multi_pred_linear_portfolio",
            gate_result: true,
            gate_reason: "mixed portfolio".to_string(),
            budget_secs: self
                .remaining_budget(deadline)
                .map_or(0.0, |d| d.as_secs_f64()),
            elapsed_secs: portfolio_start.elapsed().as_secs_f64(),
            result: Self::result_to_str(&portfolio_result),
            lemmas_learned: 0,
            max_frame: 0,
        });

        // If solved, return immediately
        if !matches!(portfolio_result, PortfolioResult::Unknown) {
            return (portfolio_result, ValidationEvidence::FullVerification);
        }

        // Check global memory budget before starting retry stages (#2771)
        if TermStore::global_memory_exceeded() {
            return (
                PortfolioResult::Unknown,
                ValidationEvidence::FullVerification,
            );
        }

        // Budget check before failure-guided retry (#7034)
        if self.budget_exhausted(deadline) {
            if self.config.verbose {
                safe_eprintln!("Adaptive: Budget exhausted after portfolio, skipping retry");
            }
            return (
                PortfolioResult::Unknown,
                ValidationEvidence::FullVerification,
            );
        }

        // Stage 3: Failure-guided retry (with transferred lemma pool)
        (
            self.failure_guided_retry(deadline, transferred_pool.as_ref())
                .unwrap_or(portfolio_result),
            ValidationEvidence::FullVerification,
        )
    }

    /// Failure-guided retry: probe PDR, analyze the failure, and retry with
    /// adjusted configuration. Returns `Some(result)` if retry solves or
    /// `None` to fall through to the original portfolio Unknown.
    pub(super) fn failure_guided_retry(
        &self,
        deadline: Option<Instant>,
        transferred_pool: Option<&LemmaPool>,
    ) -> Option<PortfolioResult> {
        if self.budget_exhausted(deadline) {
            if self.config.verbose {
                safe_eprintln!("Adaptive: Budget exhausted, skipping failure-guided retry");
            }
            return None;
        }
        if self.config.verbose {
            safe_eprintln!("Adaptive: Portfolio returned Unknown, running failure analysis probe");
        }

        let probe_timeout = self.multi_pred_probe_timeout(deadline);
        // #7930: Cap PDR escalation for DT problems in retry path too.
        let max_esc = if self.problem.has_datatype_sorts() {
            0
        } else {
            3
        };
        let mut probe_config = Self::multi_pred_pdr_config(PdrConfig {
            max_frames: 30,
            max_iterations: 500,
            verbose: self.config.verbose,
            solve_timeout: Some(probe_timeout),
            max_escalation_level: max_esc,
            ..PdrConfig::default()
        })
        .with_tla_trace_from_env();
        // Re-enable Entry-CEGAR for bounded probe when predicate count >= 4.
        if self.problem.predicates().len() >= 4 {
            probe_config.use_entry_cegar_discharge = true;
        }
        self.apply_user_hints(&mut probe_config);
        // Seed probe with transferred lemmas from non-inlined PDR (#7919).
        if let Some(pool) = transferred_pool {
            if !pool.is_empty() {
                probe_config.lemma_hints = Some(pool.clone());
            }
        }
        let probe_result = PdrSolver::solve_problem_with_stats(&self.problem, probe_config);
        self.accumulate_stats(&probe_result.stats);

        // Validate before returning (#5549 soundness fix)
        if !matches!(probe_result.result, PdrResult::Unknown) {
            let validated = self.validate_adaptive_result(probe_result.result);
            if !matches!(validated, PdrResult::Unknown) {
                return Some(validated);
            }
        }

        if self.budget_exhausted(deadline) {
            return None;
        }

        let analysis = FailureAnalysis::from_stats(&probe_result.stats);
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: Probe analysis - {} (confidence {:.0}%)",
                analysis.mode,
                analysis.confidence * 100.0
            );
            safe_eprintln!("Adaptive: Diagnostic: {}", analysis.diagnostic);
        }

        let guide = FailureGuide::from_analysis(&analysis);

        if let Some(ref alt_engine) = guide.try_alternative_engine {
            if let Some(result) = self.try_alternative_engine_budgeted(alt_engine, deadline) {
                return Some(result);
            }
        }

        if self.budget_exhausted(deadline) {
            return None;
        }

        if !guide.adjustments.is_empty() {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Retrying with {} config adjustments",
                    guide.adjustments.len()
                );
            }
            let mut retry_base = Self::multi_pred_pdr_config(PdrConfig {
                verbose: self.config.verbose,
                solve_timeout: self.multi_pred_retry_timeout(deadline),
                max_escalation_level: max_esc,
                ..PdrConfig::default()
            })
            .with_tla_trace_from_env();
            // Re-enable Entry-CEGAR for bounded retry when predicate count >= 4.
            if self.problem.predicates().len() >= 4 {
                retry_base.use_entry_cegar_discharge = true;
            }
            self.apply_user_hints(&mut retry_base);
            retry_base.user_hints.extend(probe_result.learned_lemmas);
            // Also seed retry with transferred lemmas from non-inlined PDR (#7919).
            if let Some(pool) = transferred_pool {
                if !pool.is_empty() {
                    retry_base.lemma_hints = Some(pool.clone());
                }
            }
            let retry_config = guide.apply_to_config(retry_base);
            let retry_result = PdrSolver::solve_problem_with_stats(&self.problem, retry_config);
            self.accumulate_stats(&retry_result.stats);
            let validated = self.validate_adaptive_result(retry_result.result);
            if !matches!(validated, PdrResult::Unknown) {
                return Some(validated);
            }
        }

        None
    }

    pub(crate) fn multi_pred_linear_portfolio_config(
        &self,
        pdr1: PdrConfig,
        pdr2: PdrConfig,
        features: &ProblemFeatures,
    ) -> PortfolioConfig {
        let mut engines = vec![EngineConfig::Pdr(pdr1), EngineConfig::Pdr(pdr2)];

        // #7930: Skip Kind for DT problems. Kind with SingleLoop encoding
        // produces huge flattened formulas for DT+BV problems (13+ predicates
        // with constructor/selector terms). This adds active CPU contention
        // without producing useful k-induction results. For non-DT problems,
        // Kind via SingleLoop replaces the no-op PDKind (#6500).
        if !features.uses_datatypes {
            engines.push(EngineConfig::Kind(KindConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                ..KindConfig::default()
            }));
        }

        engines.extend([
            // TPA closes mode-dispatch arithmetic cases (e.g., dillig12_m) that
            // often stall in PDR/TRL due heavy implication checks.
            EngineConfig::Tpa(TpaConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                ..TpaConfig::default()
            }),
            // PDKind via SingleLoop encoding: combines PDR frames with
            // k-induction. Golem's pdkind solves benchmarks like s_multipl_24
            // that pure PDR and Kind cannot handle individually.
            EngineConfig::Pdkind(PdkindConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                ..PdkindConfig::default()
            }),
            // IMC (interpolation-based model checking) via SingleLoop.
            // Solves multi-predicate problems with alternating counter
            // patterns (e.g., s_multipl_24) that PDR stalls on.
            EngineConfig::Imc(ImcConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                ..ImcConfig::default()
            }),
            // DAR is effective on linear arithmetic benchmarks where proof-search
            // engines saturate on unknown implication checks.
            EngineConfig::Dar(DarConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                ..DarConfig::default()
            }),
            // TRL subsumes BMC (unrolling + transitive relation learning).
            // Replacing plain BMC with TRL to add loop summarization
            // capability without increasing engine count.
            EngineConfig::Trl(TrlConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                ..TrlConfig::default()
            }),
            EngineConfig::Cegar(CegarConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                ..CegarConfig::default()
            }),
        ]);

        // Acyclic BMC completeness (#6047): For acyclic problems, add BMC with
        // acyclic_safe=true. After ClauseInliner collapses the predicate chain,
        // BMC on the preprocessed problem only needs depth = num_predicates to
        // achieve completeness (every execution path is bounded by chain length).
        // This handles the zani memory-tracking pattern: 27-predicate acyclic
        // basic-block chains where PDR can't initialize after inlining.
        if !features.has_cycles {
            let depth = features.num_predicates.max(1);
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Adding acyclic BMC to portfolio (depth={})",
                    depth
                );
            }
            engines.push(EngineConfig::Bmc(BmcConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                max_depth: depth,
                acyclic_safe: true,
                per_depth_timeout: None,
            }));
        }

        PortfolioConfig {
            engines,
            parallel: true,
            timeout: None,
            parallel_timeout: if self.config.time_budget.is_zero() {
                None
            } else {
                Some(self.config.time_budget)
            },
            verbose: self.config.verbose,
            validate: self.config.validate,
            enable_preprocessing: true,
        }
    }

    pub(crate) fn non_inlined_pdr_stage_budget(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> Duration {
        // Budget scaling (#1398): 5s base + scaling per predicate beyond 3.
        // For 5 preds (gj2007_m_2): 5 + 3*2 = 11s. For 2-3 preds: 5s.
        // Cap at 15s to avoid starving the portfolio. push_lemmas requires
        // O(predicates × lemmas) SMT calls per level — 5s is insufficient
        // for 5+ predicate chains where invariants are discovered at level 1
        // but convergence needs multiple push rounds.
        let num_preds = features.num_predicates as u64;
        let base_budget_secs = if num_preds >= 5 {
            // #1362 D2: 3s per predicate beyond 3 for long chains.
            // gj2007_m_2 (5 preds) needs ~15s (Z3 needs 15.4s).
            5 + 3 * num_preds.saturating_sub(3)
        } else if num_preds >= 4 {
            5 + 2 * num_preds.saturating_sub(3)
        } else {
            5
        };
        let max_budget = Duration::from_secs(base_budget_secs.min(15));
        let remaining = self.remaining_budget(deadline).unwrap_or(max_budget);

        if features.uses_arrays {
            // #7897: Array-heavy zani memory-tracking harnesses spend the whole
            // external 15s cap in non-inlined PDR and never reach the portfolio.
            // Keep a short probe here, but reserve most of the budget for the
            // downstream array-aware portfolio (persistent-array sessions,
            // BvToBool/BvToInt, CEGAR/BMC/TRL).
            return (remaining / 4).min(Duration::from_secs(4)).min(max_budget);
        }

        // #7457: Cap non-inlined PDR to a fraction of remaining budget.
        // Without this cap, discover_counting_invariants can consume the
        // entire budget via O(n^2 * k) SMT checks, leaving zero for the
        // portfolio. dillig22_m regressed from <0.1s to ~5s because of this.
        // #1362 D2: Relax to 66% for 5+ predicate chains where non-inlined
        // PDR is the primary strategy and portfolio has lower expected yield.
        // For 2-3 predicates, use 50% of remaining budget.
        if num_preds >= 5 {
            (remaining * 2 / 3).min(max_budget)
        } else {
            (remaining / 2).min(max_budget)
        }
    }

    pub(crate) fn should_try_non_inlined_pdr(&self, features: &ProblemFeatures) -> bool {
        // Always try non-inlined PDR for 2+ predicate problems.
        // Clause inlining destroys per-predicate structure that PDR needs
        // for modular invariant discovery. The zone/chc-hard-tail peak (53/55)
        // was achieved with this wide gate; narrowing it to mod/div/ITE-only
        // caused the s_multipl_* regression from 53 to 42.
        if features.num_predicates <= 1 {
            if self.config.verbose {
                safe_eprintln!("should_try_non_inlined_pdr: false (single predicate)");
            }
            return false;
        }
        if self.config.verbose {
            safe_eprintln!(
                "should_try_non_inlined_pdr: true ({} predicates)",
                features.num_predicates
            );
        }
        true
    }
}
