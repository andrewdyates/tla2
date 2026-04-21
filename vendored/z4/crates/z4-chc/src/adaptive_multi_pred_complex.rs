// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Complex multi-predicate and complex-loop strategy methods for the adaptive
//! portfolio solver.
//!
//! Companion to `adaptive_multi_pred.rs`: contains `solve_complex_loop` and
//! `solve_multi_pred_complex`, while the parent retains linear multi-pred
//! strategies, failure-guided retry, and the non-inlined PDR gate.

use crate::bmc::BmcConfig;
use crate::cegar::CegarConfig;
use crate::classifier::ProblemFeatures;
use crate::engine_config::ChcEngineConfig;
use crate::failure_analysis::{FailureAnalysis, FailureGuide};
use crate::kind::KindConfig;
use crate::lemma_pool::LemmaPool;
use crate::pdkind::PdkindConfig;
use crate::pdr::{PdrConfig, PdrResult, PdrSolver};
use crate::portfolio::{EngineConfig, PortfolioConfig, PortfolioResult};
use crate::tpa::TpaConfig;
use crate::trl::TrlConfig;
use std::time::{Duration, Instant};
use z4_core::TermStore;

use crate::adaptive::AdaptivePortfolio;
use crate::adaptive_decision_log::DecisionEntry;

impl AdaptivePortfolio {
    /// Solve complex loop problems - PDR primary with multiple configs.
    ///
    /// When the classifier detects a phase-bounded problem (#7897), a
    /// BMC engine with `acyclic_safe=true` is run as Stage 0 and included
    /// in the parallel portfolio. This handles zani-generated phased
    /// execution patterns that PDR struggles with.
    pub(super) fn solve_complex_loop(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> PortfolioResult {
        if self.config.verbose {
            safe_eprintln!("Adaptive: Using complex loop strategy (PDR with multiple configs)");
        }

        // Stage -2: Focused BMC probe FIRST for counterexample discovery (#7983).
        //
        // BMC with monolithic encoding finds counterexamples faster than PDR
        // for phase-bounded problems (e.g., two_phase_unsafe needs depth ~22).
        // Running BMC first avoids wasting budget on PDR's DPLL(T) loops which
        // don't respect soft timeouts.
        if features.is_single_predicate
            && !features.uses_arrays
            && !self.problem.has_bv_sorts()
            && !self.budget_exhausted(deadline)
        {
            let bmc_probe_budget_secs: u64 = 10;
            let bmc_budget = self
                .remaining_budget(deadline)
                .unwrap_or(Duration::from_secs(25))
                .min(Duration::from_secs(bmc_probe_budget_secs));
            if !bmc_budget.is_zero() {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: ComplexLoop focused BMC probe (budget {:.1}s, direct)",
                        bmc_budget.as_secs_f64()
                    );
                }
                let cancel = crate::cancellation::CancellationToken::new();
                let cancel_clone = cancel.clone();
                let bmc_probe_max_depth: usize = 22;
                let bmc_config = BmcConfig {
                    base: ChcEngineConfig {
                        verbose: self.config.verbose,
                        cancellation_token: Some(cancel),
                    },
                    max_depth: bmc_probe_max_depth,
                    ..BmcConfig::default()
                };
                let budget = bmc_budget;
                std::thread::spawn(move || {
                    std::thread::sleep(budget);
                    cancel_clone.cancel();
                });
                let bmc_start = Instant::now();
                let bmc_solver = crate::bmc::BmcSolver::new(self.problem.clone(), bmc_config);
                let bmc_result = bmc_solver.solve();
                let bmc_elapsed = bmc_start.elapsed();
                match bmc_result {
                    crate::engine_result::ChcEngineResult::Unsafe(cex) => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "Adaptive: ComplexLoop BMC probe found counterexample in {:.2}s",
                                bmc_elapsed.as_secs_f64()
                            );
                        }
                        let result = PortfolioResult::Unsafe(cex);
                        self.decision_log.log_decision(DecisionEntry {
                            stage: "complex_loop_bmc_probe",
                            gate_result: true,
                            gate_reason: "counterexample found".to_string(),
                            budget_secs: bmc_budget.as_secs_f64(),
                            elapsed_secs: bmc_elapsed.as_secs_f64(),
                            result: Self::result_to_str(&result),
                            lemmas_learned: 0,
                            max_frame: 0,
                        });
                        return result;
                    }
                    _ => {
                        self.decision_log.log_decision(DecisionEntry {
                            stage: "complex_loop_bmc_probe",
                            gate_result: false,
                            gate_reason: "no counterexample in budget".to_string(),
                            budget_secs: bmc_budget.as_secs_f64(),
                            elapsed_secs: bmc_elapsed.as_secs_f64(),
                            result: "unknown",
                            lemmas_learned: 0,
                            max_frame: 0,
                        });
                    }
                }
            }
        }

        // Stage -1: Fast PDR probe (500ms hard cap). Many ComplexLoop problems
        // are trivially solvable by PDR in <1s. The hard cancellation token
        // ensures PDR doesn't consume the budget in DPLL(T) loops that ignore
        // soft timeouts.
        {
            let pdr_probe_timeout_ms: u64 = 500;
            let probe_start = Instant::now();
            let pdr_cancel = crate::cancellation::CancellationToken::new();
            let pdr_cancel_clone = pdr_cancel.clone();
            let pdr_probe_dur = Duration::from_millis(pdr_probe_timeout_ms);
            std::thread::spawn(move || {
                std::thread::sleep(pdr_probe_dur);
                pdr_cancel_clone.cancel();
            });
            let mut probe_config = PdrConfig {
                max_frames: 30,
                max_iterations: 500,
                solve_timeout: Some(Duration::from_millis(pdr_probe_timeout_ms)),
                verbose: self.config.verbose,
                cancellation_token: Some(pdr_cancel),
                ..PdrConfig::default()
            }
            .with_tla_trace_from_env();
            self.apply_user_hints(&mut probe_config);
            let probe_result = PdrSolver::solve_problem_with_stats(&self.problem, probe_config);
            self.accumulate_stats(&probe_result.stats);
            let probe_elapsed = probe_start.elapsed().as_secs_f64();

            if !matches!(probe_result.result, PdrResult::Unknown) {
                let validated = self.validate_adaptive_result(probe_result.result);
                if !matches!(validated, PortfolioResult::Unknown) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: ComplexLoop fast PDR probe solved in {:.2}s",
                            probe_elapsed
                        );
                    }
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "complex_loop_pdr_probe",
                        gate_result: true,
                        gate_reason: "fast probe solved".to_string(),
                        budget_secs: 2.0,
                        elapsed_secs: probe_elapsed,
                        result: Self::result_to_str(&validated),
                        lemmas_learned: probe_result.learned_lemmas.len(),
                        max_frame: probe_result.stats.max_frame,
                    });
                    return validated;
                }
            }
            self.decision_log.log_decision(DecisionEntry {
                stage: "complex_loop_pdr_probe",
                gate_result: false,
                gate_reason: "probe returned unknown".to_string(),
                budget_secs: 2.0,
                elapsed_secs: probe_elapsed,
                result: "unknown",
                lemmas_learned: probe_result.learned_lemmas.len(),
                max_frame: probe_result.stats.max_frame,
            });
        }

        // Cross-engine lemma transfer pool (#7934). Populated by non-inlined
        // PDR when it returns Unknown, consumed by portfolio engines.
        let mut transferred_pool: Option<LemmaPool> = None;

        // #7934: Non-inlined PDR pre-stage for multi-predicate complex loops.
        // Clause inlining destroys per-predicate structure that PDR needs for
        // modular invariant discovery. Run PDR on the original problem first
        // to find per-predicate invariants before falling through to the
        // inlined portfolio. This was previously in the separate hybrid path
        // (solve_with_non_inlined_pdr_then_learned) but using the learned
        // selector portfolio instead of the tuned complex-loop portfolio
        // caused a 5-benchmark regression.
        if features.num_predicates >= 2
            && self.should_try_non_inlined_pdr(features)
            && !self.budget_exhausted(deadline)
        {
            let stage_budget = self.non_inlined_pdr_stage_budget(features, deadline);
            if !stage_budget.is_zero() {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: ComplexLoop non-inlined PDR pre-stage ({} preds, {:.1}s budget)",
                        features.num_predicates,
                        stage_budget.as_secs_f64()
                    );
                }
                let mut pdr_config = Self::multi_pred_pdr_config(PdrConfig {
                    verbose: self.config.verbose,
                    solve_timeout: Some(stage_budget),
                    max_escalation_level: if features.uses_datatypes { 0 } else { 3 },
                    ..PdrConfig::default()
                })
                .with_tla_trace_from_env();
                self.apply_user_hints(&mut pdr_config);
                let non_inlined_start = Instant::now();
                let mut pdr = PdrSolver::new(self.problem.clone(), pdr_config);
                pdr.enable_tla_trace_from_config();
                let result = pdr.solve();
                let validated = self.validate_adaptive_result(result);
                if !matches!(validated, PdrResult::Unknown) {
                    if self.config.verbose {
                        safe_eprintln!("Adaptive: ComplexLoop non-inlined PDR solved the problem");
                    }
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "complex_loop_non_inlined_pdr",
                        gate_result: true,
                        gate_reason: format!("{} predicates", features.num_predicates),
                        budget_secs: stage_budget.as_secs_f64(),
                        elapsed_secs: non_inlined_start.elapsed().as_secs_f64(),
                        result: Self::result_to_str(&validated),
                        lemmas_learned: 0,
                        max_frame: 0,
                    });
                    return validated;
                }
                // Export learned lemmas for cross-engine transfer.
                let pool = pdr.export_lemmas();
                if self.config.verbose && !pool.is_empty() {
                    safe_eprintln!(
                        "Adaptive: Exported {} lemmas from ComplexLoop non-inlined PDR",
                        pool.len()
                    );
                }
                let pool_size = pool.len();
                transferred_pool = Some(pool);
                self.decision_log.log_decision(DecisionEntry {
                    stage: "complex_loop_non_inlined_pdr",
                    gate_result: true,
                    gate_reason: format!("{} predicates, unknown", features.num_predicates),
                    budget_secs: stage_budget.as_secs_f64(),
                    elapsed_secs: non_inlined_start.elapsed().as_secs_f64(),
                    result: "unknown",
                    lemmas_learned: pool_size,
                    max_frame: 0,
                });
            }
        }

        // Stage 0: BMC probe already ran above (Stage -2). No duplicate needed.

        // #7897: Phase-bounded detection for zani-style phased execution.
        // When a single-predicate problem has a monotonically-increasing
        // integer argument (phase counter), BMC with acyclic_safe=true can
        // prove safety by exhausting all reachable states.
        if let Some(depth) = features.phase_bounded_depth {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Phase-bounded problem detected (depth={}), trying BMC with acyclic_safe",
                    depth
                );
            }
            let bmc_config = BmcConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                max_depth: depth,
                acyclic_safe: true,
                per_depth_timeout: Some(Duration::from_secs(5)),
            };
            let bmc_solver = crate::bmc::BmcSolver::new(self.problem.clone(), bmc_config);
            let bmc_result = bmc_solver.solve();
            match bmc_result {
                crate::engine_result::ChcEngineResult::Safe(model) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: Phase-bounded BMC proved Safe at depth {}",
                            depth
                        );
                    }
                    let result = PortfolioResult::Safe(model);
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "complex_loop_phase_bmc",
                        gate_result: true,
                        gate_reason: format!("phase_bounded depth={depth}"),
                        budget_secs: 0.0,
                        elapsed_secs: 0.0,
                        result: Self::result_to_str(&result),
                        lemmas_learned: 0,
                        max_frame: depth,
                    });
                    return result;
                }
                crate::engine_result::ChcEngineResult::Unsafe(cex) => {
                    if self.config.verbose {
                        safe_eprintln!("Adaptive: Phase-bounded BMC found counterexample");
                    }
                    let result = PortfolioResult::Unsafe(cex);
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "complex_loop_phase_bmc",
                        gate_result: true,
                        gate_reason: format!("phase_bounded depth={depth}"),
                        budget_secs: 0.0,
                        elapsed_secs: 0.0,
                        result: Self::result_to_str(&result),
                        lemmas_learned: 0,
                        max_frame: depth,
                    });
                    return result;
                }
                crate::engine_result::ChcEngineResult::Unknown
                | crate::engine_result::ChcEngineResult::NotApplicable => {
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "complex_loop_phase_bmc",
                        gate_result: true,
                        gate_reason: format!("phase_bounded depth={depth}, unknown"),
                        budget_secs: 0.0,
                        elapsed_secs: 0.0,
                        result: "unknown",
                        lemmas_learned: 0,
                        max_frame: depth,
                    });
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: Phase-bounded BMC returned Unknown, falling through to portfolio"
                        );
                    }
                }
            }
        }

        // Propagate verbose flag to PDR engine configs (#1969)
        // #7930: Cap escalation for DT problems.
        let max_esc = if features.uses_datatypes { 0 } else { 3 };
        let mut pdr1 = PdrConfig {
            max_escalation_level: max_esc,
            verbose: self.config.verbose,
            ..PdrConfig::default()
        };
        let mut pdr2 = PdrConfig {
            max_escalation_level: max_esc,
            verbose: self.config.verbose,
            ..PdrConfig::portfolio_variant_with_splits()
        };
        // Seed portfolio PDR engines with transferred lemma pool (#7934).
        if let Some(ref pool) = transferred_pool {
            if !pool.is_empty() {
                pdr1.lemma_hints = Some(pool.clone());
                pdr2.lemma_hints = Some(pool.clone());
            }
        }

        // #7897: Include phase-bounded BMC in the parallel portfolio as well.
        let bmc_engine = if let Some(depth) = features.phase_bounded_depth {
            EngineConfig::Bmc(BmcConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                max_depth: depth,
                acyclic_safe: true,
                per_depth_timeout: Some(Duration::from_secs(5)),
            })
        } else {
            EngineConfig::Bmc(BmcConfig::default())
        };

        let mut engines = vec![
            EngineConfig::Pdr(pdr1),
            EngineConfig::Pdr(pdr2),
            EngineConfig::Pdkind(PdkindConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                ..PdkindConfig::default()
            }),
            // TRL adds loop summarization via transitive relation learning
            // with n-retention. Safety proving only (no UNSAT path).
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
            // TPA handles multi-phase loops efficiently by squaring the
            // transition relation (#6331). Power 2^k reaches depth 2^k in
            // one check, solving e.g. two_phase_unsafe (depth ~22) at power 5.
            EngineConfig::Tpa(TpaConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                max_power: 30,
                timeout_per_power: Duration::from_secs(3),
                verbose_level: u8::from(self.config.verbose),
            }),
            bmc_engine,
        ];
        // #7930: Skip Kind for DT problems. Kind with SingleLoop encoding
        // produces huge flattened formulas for DT+BV problems, adding CPU
        // contention without useful k-induction results.
        if !features.uses_datatypes {
            engines.push(EngineConfig::Kind(KindConfig::default()));
        }

        // Use deadline-based remaining budget (#7932). Previous code used
        // `self.config.time_budget` which didn't account for time spent in
        // probe stages (Stage -1 PDR probe, phase-bounded BMC), causing the
        // portfolio to overrun the caller's budget and starve downstream
        // fallback solvers (e.g., Z3 Spacer in Zani's auto mode).
        let portfolio_timeout = self.remaining_budget(deadline);
        let config = PortfolioConfig {
            engines,
            parallel: true,
            timeout: None,
            parallel_timeout: portfolio_timeout,
            verbose: self.config.verbose,
            validate: self.config.validate,
            enable_preprocessing: true,
        };

        let portfolio_start = Instant::now();
        let result = self.run_portfolio(config);
        self.decision_log.log_decision(DecisionEntry {
            stage: "complex_loop_portfolio",
            gate_result: true,
            gate_reason: "full portfolio".to_string(),
            budget_secs: portfolio_timeout.map_or(0.0, |d| d.as_secs_f64()),
            elapsed_secs: portfolio_start.elapsed().as_secs_f64(),
            result: Self::result_to_str(&result),
            lemmas_learned: 0,
            max_frame: 0,
        });
        result
    }

    /// Solve multi-predicate complex problems - full portfolio.
    ///
    /// Uses failure-guided retry: if portfolio returns Unknown, run a quick PDR
    /// probe with stats collection, analyze the failure, and retry with adjusted
    /// configuration.
    ///
    /// Part of #2082 - Extend failure-guided retry to multi-predicate paths.
    pub(super) fn solve_multi_pred_complex(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> PortfolioResult {
        if self.config.verbose {
            safe_eprintln!("Adaptive: Using multi-pred complex strategy (full portfolio)");
        }

        // Stage 0: Try structural synthesis (< 1ms overhead on extra-small-lia)
        if let Some(result) = self.try_synthesis() {
            if self.config.verbose {
                safe_eprintln!("Adaptive: MultiPredComplex problem solved by structural synthesis");
            }
            return result;
        }

        // Cross-engine lemma transfer pool (#7919). Populated by non-inlined PDR
        // when it returns Unknown, consumed by retry engines.
        let mut transferred_pool: Option<LemmaPool> = None;

        // Stage 0.5: Non-inlined PDR for multi-predicate problems (#1362).
        // Same rationale as solve_multi_pred_linear Stage 1.5: inlining destroys
        // per-predicate parity structure that PDR needs for modular invariants.
        if self.problem.predicates().len() > 1 && !self.budget_exhausted(deadline) {
            // Budget scaling (#1398): same formula as Stage 1.5.
            let num_preds = self.problem.predicates().len() as u64;
            let base_budget_secs = if num_preds >= 4 {
                5 + 2 * num_preds.saturating_sub(3)
            } else {
                5
            };
            let max_budget = Duration::from_secs(base_budget_secs.min(15));
            // #7457: Cap to 50% of remaining budget (same as Stage 1.5).
            let remaining = self.remaining_budget(deadline).unwrap_or(max_budget);
            let stage_budget = (remaining / 2).min(max_budget);
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Trying non-inlined PDR ({} predicates, {:.1}s budget)",
                    self.problem.predicates().len(),
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
                    stage: "multi_pred_complex_non_inlined_pdr",
                    gate_result: true,
                    gate_reason: format!("{} predicates", self.problem.predicates().len()),
                    budget_secs: stage_budget.as_secs_f64(),
                    elapsed_secs: non_inlined_start.elapsed().as_secs_f64(),
                    result: Self::result_to_str(&validated),
                    lemmas_learned: 0,
                    max_frame: 0,
                });
                return validated;
            }
            // Export learned lemmas for cross-engine transfer (#7919).
            let pool = pdr.export_lemmas();
            if self.config.verbose && !pool.is_empty() {
                safe_eprintln!(
                    "Adaptive: Exported {} lemmas from non-inlined PDR for cross-engine transfer (complex)",
                    pool.len()
                );
            }
            let pool_size = pool.len();
            transferred_pool = Some(pool);
            self.decision_log.log_decision(DecisionEntry {
                stage: "multi_pred_complex_non_inlined_pdr",
                gate_result: true,
                gate_reason: format!("{} predicates, unknown", self.problem.predicates().len()),
                budget_secs: stage_budget.as_secs_f64(),
                elapsed_secs: non_inlined_start.elapsed().as_secs_f64(),
                result: "unknown",
                lemmas_learned: pool_size,
                max_frame: 0,
            });
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Non-inlined PDR returned Unknown, continuing to portfolio"
                );
            }
        }

        // Stage 1: Run full portfolio with deadline-based timeout (#7034, #7932)
        let mut config = PortfolioConfig::default();
        match self.remaining_budget(deadline) {
            Some(remaining) => {
                config.parallel_timeout = Some(Self::multi_pred_portfolio_timeout(remaining));
            }
            None => {
                // Unbounded budget (no deadline). Leave parallel_timeout as None.
            }
        }
        config.verbose = self.config.verbose;
        config.validate = self.config.validate;
        // Cap PDR escalation and remove Kind for DT problems (#7930).
        if features.uses_datatypes {
            config.apply_dt_guards(0);
        }
        // Seed portfolio PDR engines with transferred lemma pool (#7919).
        // This closes the gap where the complex path discarded non-inlined PDR
        // lemmas when entering the portfolio, unlike the linear path which
        // explicitly set lemma_hints on its PDR configs.
        if let Some(ref pool) = transferred_pool {
            config.set_pdr_lemma_pool(pool);
            if self.config.verbose && !pool.is_empty() {
                safe_eprintln!(
                    "Adaptive: Seeded portfolio PDR engines with {} transferred lemmas (#7919)",
                    pool.len()
                );
            }
        }

        let portfolio_start = Instant::now();
        let portfolio_result = self.run_portfolio(config);

        self.decision_log.log_decision(DecisionEntry {
            stage: "multi_pred_complex_portfolio",
            gate_result: true,
            gate_reason: "full portfolio".to_string(),
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
            return portfolio_result;
        }

        // Check global memory budget before starting retry stages (#2771)
        if TermStore::global_memory_exceeded() {
            return PortfolioResult::Unknown;
        }

        // Budget check before retry stages (#7034)
        if self.budget_exhausted(deadline) {
            if self.config.verbose {
                safe_eprintln!("Adaptive: Budget exhausted after portfolio, skipping retry");
            }
            return PortfolioResult::Unknown;
        }

        // Stage 2: Failure-guided retry
        if self.config.verbose {
            safe_eprintln!("Adaptive: Portfolio returned Unknown, running failure analysis probe");
        }

        let probe_timeout = self.multi_pred_probe_timeout(deadline);
        let max_esc = if features.uses_datatypes { 0 } else { 3 };
        let mut probe_config = Self::multi_pred_pdr_config(PdrConfig {
            max_frames: 30,
            max_iterations: 500,
            verbose: self.config.verbose,
            solve_timeout: Some(probe_timeout),
            max_escalation_level: max_esc,
            ..PdrConfig::default()
        })
        .with_tla_trace_from_env();
        self.apply_user_hints(&mut probe_config);
        // Seed probe with transferred lemmas from non-inlined PDR (#7919).
        if let Some(ref pool) = transferred_pool {
            if !pool.is_empty() {
                probe_config.lemma_hints = Some(pool.clone());
            }
        }
        let probe_result = PdrSolver::solve_problem_with_stats(&self.problem, probe_config);
        self.accumulate_stats(&probe_result.stats);

        // If probe solves, validate before returning (#5549 soundness fix)
        if !matches!(probe_result.result, PdrResult::Unknown) {
            let validated = self.validate_adaptive_result(probe_result.result);
            if !matches!(validated, PdrResult::Unknown) {
                return validated;
            }
        }

        if self.budget_exhausted(deadline) {
            return PortfolioResult::Unknown;
        }

        // Analyze failure and guide retry
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

        // Try alternative engine with remaining budget (#7034)
        if let Some(ref alt_engine) = guide.try_alternative_engine {
            if let Some(result) = self.try_alternative_engine_budgeted(alt_engine, deadline) {
                return result;
            }
        }

        if self.budget_exhausted(deadline) {
            return PortfolioResult::Unknown;
        }

        // Retry PDR with guided config adjustments
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
            self.apply_user_hints(&mut retry_base);
            // Also seed retry with transferred lemmas from non-inlined PDR (#7919).
            if let Some(ref pool) = transferred_pool {
                if !pool.is_empty() {
                    retry_base.lemma_hints = Some(pool.clone());
                }
            }
            let retry_config = guide.apply_to_config(retry_base);
            let retry_result = PdrSolver::solve_problem_with_stats(&self.problem, retry_config);
            self.accumulate_stats(&retry_result.stats);
            return self.validate_adaptive_result(retry_result.result);
        }

        // No retry possible, return original Unknown
        portfolio_result
    }
}
