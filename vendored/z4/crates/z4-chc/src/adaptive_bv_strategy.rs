// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV strategy methods for the adaptive portfolio solver.
//!
//! Contains portfolio config builders and the simple loop orchestrator.
//! Companion: `adaptive_bv_dual_lane.rs` has the quad-lane BV solving
//! method (`solve_bv_dual_lane`).

use crate::bmc::BmcConfig;
use crate::cegar::CegarConfig;
use crate::classifier::ProblemFeatures;
use crate::engine_config::ChcEngineConfig;
use crate::engine_result::ValidationEvidence;
use crate::pdkind::PdkindConfig;
use crate::pdr::{PdrConfig, PdrResult, PdrSolver};
use crate::portfolio::{EngineConfig, PortfolioConfig, PortfolioResult};
use crate::tpa::TpaConfig;
use crate::trl::TrlConfig;
use std::time::{Duration, Instant};

use crate::adaptive::AdaptivePortfolio;

fn try_budgeted_pdr(
    portfolio: &AdaptivePortfolio,
    mut pdr_config: PdrConfig,
    budget: Duration,
) -> Option<(PortfolioResult, ValidationEvidence)> {
    if budget.is_zero() {
        return None;
    }

    pdr_config.solve_timeout = Some(budget);
    portfolio.apply_user_hints(&mut pdr_config);
    let mut solver = PdrSolver::new(portfolio.problem.clone(), pdr_config);
    solver.enable_tla_trace_from_config();
    let result = solver.solve();
    let validated = portfolio.validate_adaptive_result(result);

    match validated {
        PdrResult::Safe(model) => Some((
            PortfolioResult::Safe(model),
            ValidationEvidence::FullVerification,
        )),
        PdrResult::Unsafe(cex) => Some((
            PortfolioResult::Unsafe(cex),
            ValidationEvidence::FullVerification,
        )),
        PdrResult::Unknown | PdrResult::NotApplicable => None,
    }
}

fn unknown_accepted_result() -> (PortfolioResult, ValidationEvidence) {
    (
        PortfolioResult::Unknown,
        ValidationEvidence::FullVerification,
    )
}

impl AdaptivePortfolio {
    /// Solve simple loop problems with validation evidence tracking.
    ///
    /// Kind results get `QueryOnly` evidence (k-inductive, query-only validation).
    /// All other paths get `FullVerification`, either from portfolio validation
    /// or from adaptive direct validation that still checks init/transition/query.
    /// Part of #5746.
    pub(super) fn solve_simple_loop_with_evidence(
        &self,
        features: &ProblemFeatures,
        deadline: Option<std::time::Instant>,
    ) -> (PortfolioResult, ValidationEvidence) {
        let strategy_start = Instant::now();

        // Stage 0: Try structural synthesis (< 1ms overhead)
        if let Some(result) = self.try_synthesis() {
            if self.config.verbose {
                safe_eprintln!("Adaptive: Simple loop solved by structural synthesis");
            }
            return (result, ValidationEvidence::FullVerification);
        }

        // Stage 1: Try K-Induction (forward AND backward per Golem's Kind.cc)
        // This gives quick wins for problems with k-inductive invariants.
        // Reference: Golem Kind.cc:44-133 tries both forward and backward k-induction.
        // Cap Kind budget to the remaining time budget (if any).
        //
        // #6047: Skip KIND for problems with arrays. Bit-blasting array operations
        // (especially with BV32 indices) causes catastrophic blowup: a BV32-indexed
        // array at k=1 produces 689K SAT variables and 4.9M clauses, consuming the
        // entire solve budget. PDR/Spacer handles arrays far better via SMT-level
        // reasoning with array MBP (Model-Based Projection).
        //
        // #5877: KIND now uses non-incremental mode for BV problems (each query
        // gets a fresh SmtContext). This avoids the incremental solver state
        // corruption that caused false-UNSAT on BV bitblast formulas, while still
        // allowing KIND's k-induction to find proofs. The non-incremental path
        // is slower (no learned clause reuse) but correct.
        //
        // #7930: Skip Kind for DT problems too. Kind with SingleLoop encoding
        // produces huge flattened formulas for DT+BV problems (Option<u8>,
        // struct wrappers), adding CPU contention without useful k-induction
        // results. Matches the ComplexLoop DT guard in adaptive_multi_pred_complex.rs.
        let skip_kind = features.uses_arrays || features.uses_datatypes;
        if !skip_kind {
            // #5877: BV problems get a tight KIND budget. Non-incremental
            // BV-to-Int queries at k>=2 produce formulas with 3+ copies of
            // the transition relation (each with BV range constraints). Even
            // with a 1s per-query timeout, preprocessing consumes the entire
            // budget before DPLL starts. Cap BV to 1s (enough for k=0/k=1
            // which take ~40ms total). Pure LIA gets 3s — enough for k=0..3
            // attempts while leaving budget for the PDR probe and parallel
            // portfolio that follow. Previous 8s starved PDR for problems
            // like yz_plus_minus_1 and s_mutants_02 that need relational
            // invariants (not k-inductive).
            // #8856: Reduced LIA budget from 3s to 1.5s. Kind finds UNSAT
            // counterexamples at k<=10 in <1s; the extra 1.5s was wasted on
            // fruitless induction attempts while starving the downstream PDR
            // probe. Benchmarks like s_mutants_23 need the full PDR budget
            // and were non-deterministically timing out at 15s.
            let kind_budget_secs = if self.problem.has_bv_sorts() { 1 } else { 2 };
            let kind_budget = match self.remaining_budget(deadline) {
                Some(remaining) => remaining.min(Duration::from_secs(kind_budget_secs)),
                None => Duration::from_secs(kind_budget_secs),
            };
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Simple loop direct Kind attempt (budget {:.1}s)",
                    kind_budget.as_secs_f64()
                );
            }
            if let Some(result) = self.try_kind(kind_budget) {
                // Kind Safe results use query-only validation (k-inductive
                // invariants are not necessarily 1-inductive).
                // Kind Unsafe results carry counterexample traces that
                // finalize_verified_result validates independently (#7897).
                let evidence = if matches!(result, PortfolioResult::Unsafe(_)) {
                    ValidationEvidence::CounterexampleVerification
                } else {
                    ValidationEvidence::QueryOnly
                };
                if self.config.verbose {
                    safe_eprintln!("Adaptive: Simple loop direct Kind solved the problem");
                }
                return (result, evidence);
            }
            if self.config.verbose {
                safe_eprintln!("Adaptive: Simple loop direct Kind returned Unknown");
            }
        } else if self.config.verbose {
            tracing::info!(
                "Adaptive: Skipping K-Induction for array problem (bit-blasting blowup)"
            );
        }

        if self.config.verbose {
            safe_eprintln!("Adaptive: Using simple loop strategy (TPA probe, PDR fallback)");
        }

        // Use deadline-based remaining budget (#7932). Previous code used
        // `self.config.time_budget.saturating_sub(strategy_start.elapsed())`
        // which didn't account for time spent before this function (classification,
        // algebraic prepass, etc.), causing budget overruns that starve downstream
        // fallback solvers (e.g., Z3 Spacer in Zani's auto mode).
        let unbounded_budget = deadline.is_none();
        let remaining_budget = self
            .remaining_budget(deadline)
            .unwrap_or(Duration::from_secs(25));
        if !unbounded_budget && remaining_budget.is_zero() {
            return (
                PortfolioResult::Unknown,
                ValidationEvidence::FullVerification,
            );
        }

        // Stage 1.25: Focused BMC probe for counterexample discovery.
        //
        // After Kind returns Unknown, run a dedicated BMC probe with a short
        // budget. BMC finds counterexamples by unrolling the transition relation
        // to increasing depths. Without CPU competition from other engines, BMC
        // iterates through depths quickly (each depth adds one incremental SMT
        // query). This catches unsafe problems like accumulator_unsafe (needs
        // k=11) and two_phase_unsafe that previously timed out because BMC was
        // CPU-starved in the parallel portfolio.
        //
        // Only for non-BV, non-array simple loops (BV BMC is handled separately
        // in bv_native_portfolio_config with tighter depth limits).
        if features.is_single_predicate && !features.uses_arrays && !self.problem.has_bv_sorts() {
            // #8856: Reduced from 2s to 1.5s. BMC finds shallow
            // counterexamples quickly; the saved budget goes to the
            // PDR probe which handles deeper invariant discovery.
            let bmc_probe_budget = if unbounded_budget {
                Duration::from_millis(1500)
            } else {
                remaining_budget.min(Duration::from_millis(1500))
            };
            if !bmc_probe_budget.is_zero() {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Simple loop focused BMC probe (budget {:.1}s, direct)",
                        bmc_probe_budget.as_secs_f64()
                    );
                }
                // Run BMC directly (no portfolio wrapper) to avoid preprocessing,
                // thread spawning, and timeout management overhead. The cancellation
                // token provides cooperative timeout enforcement.
                let cancel = crate::cancellation::CancellationToken::new();
                let cancel_clone = cancel.clone();
                let bmc_config = BmcConfig {
                    base: ChcEngineConfig {
                        verbose: self.config.verbose,
                        cancellation_token: Some(cancel),
                    },
                    max_depth: 50,
                    ..BmcConfig::default()
                };
                let bmc_start = Instant::now();
                // Spawn a timer thread that cancels BMC after the budget expires.
                let budget = bmc_probe_budget;
                std::thread::spawn(move || {
                    std::thread::sleep(budget);
                    cancel_clone.cancel();
                });
                let bmc_solver = crate::bmc::BmcSolver::new(self.problem.clone(), bmc_config);
                let bmc_result = bmc_solver.solve();
                let bmc_elapsed = bmc_start.elapsed();
                match bmc_result {
                    crate::engine_result::ChcEngineResult::Unsafe(cex) => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "Adaptive: Simple loop BMC probe found counterexample in {:.2}s",
                                bmc_elapsed.as_secs_f64()
                            );
                        }
                        return (
                            PortfolioResult::Unsafe(cex),
                            ValidationEvidence::CounterexampleVerification,
                        );
                    }
                    other => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "Adaptive: Simple loop BMC probe returned {} in {:.2}s, continuing",
                                match other {
                                    crate::engine_result::ChcEngineResult::Safe(_) => "Safe",
                                    crate::engine_result::ChcEngineResult::Unknown => "Unknown",
                                    crate::engine_result::ChcEngineResult::NotApplicable =>
                                        "NotApplicable",
                                    _ => "other",
                                },
                                bmc_elapsed.as_secs_f64()
                            );
                        }
                    }
                }
            }
        }

        // Refresh remaining budget after BMC probe.
        let remaining_budget = self
            .remaining_budget(deadline)
            .unwrap_or(Duration::from_secs(25));
        if !unbounded_budget && remaining_budget.is_zero() {
            return (
                PortfolioResult::Unknown,
                ValidationEvidence::FullVerification,
            );
        }

        // Stage 1.5: Focused production-PDR probe for non-BV simple loops.
        //
        // Some single-predicate loops regress after KIND soundness hardening:
        // KIND spends its budget on rejected induction candidates, while a
        // direct production PDR run can still prove safety quickly
        // (dillig32-style pattern). Give PDR a short solo window before the
        // wider parallel portfolio so it can return a verified result without
        // competing with less-matched engines.
        let direct_pdr_candidate = features.is_single_predicate
            && !features.uses_arrays
            && !features.uses_real
            && !self.problem.has_bv_sorts();
        if direct_pdr_candidate {
            // #8856: Increased from 6s to 8s. Budget freed by reducing
            // Kind (3s→2s) and BMC (2s→1.5s) probes goes to PDR which
            // handles the majority of SAT invariant discovery.
            let pdr_probe_budget = if unbounded_budget {
                Duration::from_secs(8)
            } else {
                remaining_budget.min(Duration::from_secs(8))
            };
            if !pdr_probe_budget.is_zero() {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Simple loop production PDR probe (budget {:.1}s)",
                        pdr_probe_budget.as_secs_f64()
                    );
                }
                let pdr_config =
                    PdrConfig::production(self.config.verbose).with_tla_trace_from_env();
                if let Some(result) = try_budgeted_pdr(self, pdr_config, pdr_probe_budget) {
                    return result;
                }
            }
        }

        let remaining_budget = self
            .remaining_budget(deadline)
            .unwrap_or(Duration::from_secs(25));
        if !unbounded_budget && remaining_budget.is_zero() {
            return unknown_accepted_result();
        }

        // Stage 2: Run all engines in parallel.
        let full_budget = if unbounded_budget {
            Duration::from_secs(25)
        } else {
            remaining_budget
        };

        if features.uses_arrays {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Using array-safe simple loop portfolio (PDR primary, BMC fallback)"
                );
            }
            let config = self.simple_loop_array_portfolio_config(full_budget);
            return (
                self.run_portfolio(config),
                ValidationEvidence::FullVerification,
            );
        }

        // #5877: For BV simple loops, run dual-lane portfolio — BvToBool (Boolean
        // lane) and BvToInt (LIA lane) race in parallel. BvToBool expands BV args
        // to individual Bool bits, creating a large state space (100-1000+ args) that
        // PDR/PDKIND can struggle with. BvToInt converts BV to integer arithmetic,
        // preserving the original variable count but introducing ITE-heavy modular
        // encoding. Neither encoding dominates: BvToBool solves problems needing
        // bit-level reasoning, BvToInt solves problems with arithmetic invariants.
        // Running both in parallel maximizes coverage.
        //
        // #7930: DT+BV problems (Option<u8>, struct wrappers with BV fields) must
        // NOT enter the BV dual-lane. BvToBool/BvToInt preprocessing does not handle
        // DT constructor/selector/tester operations, causing combinatorial blowup
        // that consumes the entire budget. Route DT+BV through a DT-safe portfolio
        // with escalation caps and no Kind, matching the ComplexLoop DT guard.
        // Regressed three times when this guard was missing or collapsed.
        if self.problem.has_bv_sorts() {
            if self.problem.has_datatype_sorts() {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: DT+BV simple loop — using DT-safe portfolio (skipping BV dual-lane)"
                    );
                }
                let mut config = self.simple_loop_portfolio_config(full_budget);
                config.apply_dt_guards(0);
                return (
                    self.run_portfolio(config),
                    ValidationEvidence::FullVerification,
                );
            }
            let result = self.solve_bv_dual_lane(full_budget);
            return (result, ValidationEvidence::FullVerification);
        }

        let config = self.simple_loop_portfolio_config(full_budget);
        (
            self.run_portfolio(config),
            ValidationEvidence::FullVerification,
        )
    }

    pub(crate) fn use_bv_native_direct_route(&self, features: &ProblemFeatures) -> bool {
        self.problem.has_bv_sorts()
            && features.class == crate::classifier::ProblemClass::SimpleLoop
            && features.is_single_predicate
            && features.num_transitions == 1
            && !features.uses_arrays
            && !features.uses_real
    }

    /// Build the portfolio config for simple loop problems.
    pub(super) fn simple_loop_portfolio_config(&self, budget: Duration) -> PortfolioConfig {
        let pdr_config_val = PdrConfig {
            verbose: self.config.verbose,
            use_lemma_hints: true,
            ..PdrConfig::default()
        }
        .with_tla_trace_from_env();

        PortfolioConfig {
            engines: vec![
                EngineConfig::Tpa(TpaConfig {
                    base: ChcEngineConfig {
                        verbose: self.config.verbose,
                        ..ChcEngineConfig::default()
                    },
                    max_power: 20,
                    timeout_per_power: Duration::from_secs(2),
                    verbose_level: u8::from(self.config.verbose),
                }),
                EngineConfig::Pdkind(PdkindConfig {
                    base: ChcEngineConfig {
                        verbose: self.config.verbose,
                        ..ChcEngineConfig::default()
                    },
                    ..PdkindConfig::default()
                }),
                // TRL adds loop summarization via transitive relation learning
                // with n-retention (Golem TRL.cc:296-351). Safety proving only.
                EngineConfig::Trl(TrlConfig {
                    base: ChcEngineConfig {
                        verbose: self.config.verbose,
                        ..ChcEngineConfig::default()
                    },
                    ..TrlConfig::default()
                }),
                EngineConfig::Pdr(pdr_config_val),
                EngineConfig::Cegar(CegarConfig {
                    base: ChcEngineConfig {
                        verbose: self.config.verbose,
                        ..ChcEngineConfig::default()
                    },
                    ..CegarConfig::default()
                }),
                // BMC for bounded counterexample discovery (#5383).
                // TRL subsumes BMC's safety proving but NOT its UNSAT capability.
                EngineConfig::Bmc(BmcConfig::default()),
            ],
            parallel: true,
            timeout: None,
            parallel_timeout: Some(budget),
            verbose: self.config.verbose,
            validate: self.config.validate,
            enable_preprocessing: true,
        }
    }

    /// Build the portfolio config for array-containing simple loops.
    ///
    /// Arrays stay on the original problem and avoid the simple-loop engines
    /// whose transition-system encodings assume scalar Int/Bool state.
    pub(super) fn simple_loop_array_portfolio_config(&self, budget: Duration) -> PortfolioConfig {
        let pdr_config = PdrConfig {
            verbose: self.config.verbose,
            use_lemma_hints: true,
            ..PdrConfig::default()
        }
        .with_tla_trace_from_env();

        PortfolioConfig {
            engines: vec![
                EngineConfig::Pdr(pdr_config.clone()),
                EngineConfig::Pdr(PdrConfig {
                    use_negated_equality_splits: true,
                    ..pdr_config
                }),
                EngineConfig::Bmc(BmcConfig::default()),
            ],
            parallel: true,
            timeout: None,
            parallel_timeout: Some(budget),
            verbose: self.config.verbose,
            validate: self.config.validate,
            enable_preprocessing: true,
        }
    }

    /// Build the portfolio config for pure-Boolean simple loop problems (#5877).
    ///
    /// After BvToBool preprocessing, the predicate state space is all Bool+Int.
    /// Interpolation-heavy engines (CEGAR, DAR, IMC, TRL, TPA) are mismatched
    /// for 100+ shared Boolean variables. Use PDKIND for safety proving and
    /// BMC for counterexample discovery. PDR is also included as it uses
    /// SMT-level reasoning that works with Bool constraints.
    pub(super) fn boolean_simple_loop_portfolio_config(
        &self,
        budget: Duration,
        bv_bit_groups: &[(usize, u32)],
    ) -> PortfolioConfig {
        let pdr_config_val = PdrConfig {
            verbose: self.config.verbose,
            use_lemma_hints: true,
            bv_bit_groups: bv_bit_groups.to_vec(),
            ..PdrConfig::default()
        }
        .with_tla_trace_from_env();

        PortfolioConfig {
            engines: vec![
                EngineConfig::Pdkind(PdkindConfig {
                    base: ChcEngineConfig {
                        verbose: self.config.verbose,
                        ..ChcEngineConfig::default()
                    },
                    bv_to_bool_applied: true,
                    // BvToBool expands BV(32) to 160+ Boolean state vars. The
                    // k-transition formula is huge, so the default 5s timeout
                    // causes immediate Unknown from k-induction. Use 30s and
                    // FreshOnly to avoid BV state corruption (#5877, #8161).
                    per_obligation_timeout_secs: 30,
                    incremental_mode: crate::pdkind::IncrementalMode::FreshOnly(
                        "BitVector state unsupported".to_string(),
                    ),
                    ..PdkindConfig::default()
                }),
                EngineConfig::Pdr(pdr_config_val),
                EngineConfig::Bmc(BmcConfig::default()),
            ],
            parallel: true,
            timeout: None,
            parallel_timeout: Some(budget),
            verbose: self.config.verbose,
            validate: self.config.validate,
            // Preprocessing already done via PreprocessSummary — do not re-run.
            enable_preprocessing: false,
        }
    }

    /// Build the portfolio config for BV-native PDR solving (#5877 Wave 3).
    ///
    /// Runs PDR + BMC on the original BV-sorted problem with no BV transforms.
    /// PDR operates on BV-sorted predicates directly, delegating BV constraints
    /// to the SMT solver's BV theory. This matches Z3 Spacer's default behavior
    /// where `xform.bit_blast = false`.
    ///
    /// PDR is the primary engine for both SAT-finding (backward reachability with
    /// BV-native cubes) and UNSAT-proving (BV-level inductive invariants). BMC
    /// provides bounded counterexample discovery. Other engines (TPA, CEGAR, TRL)
    /// are excluded because their interpolation/abstraction passes assume Int/Bool
    /// state variables.
    pub(super) fn bv_native_portfolio_config(&self, budget: Duration) -> PortfolioConfig {
        let pdr_config_val = PdrConfig {
            verbose: self.config.verbose,
            use_must_summaries: true,
            use_lemma_hints: true,
            max_frames: 50,
            ..PdrConfig::default()
        }
        .with_tla_trace_from_env();

        // #5877: BV bitblasting at deep BMC depths produces exponentially
        // larger formulas. On nested4 (9-branch BV32 transition), depths 0-5
        // complete in ~55ms total but depth 6 hangs for >25s because the
        // Tseitin+bitblast encoding itself is intractable (no mid-encoding
        // interrupt). Cap BV-native BMC at 15 (vs default 50) and add
        // per_depth_timeout as a secondary guard. The pre-encoding timeout
        // checks in incremental.rs bail before encoding starts when cumulative
        // depth time exceeds the per-depth timeout.
        let bmc_config = BmcConfig {
            max_depth: 15,
            per_depth_timeout: Some(Duration::from_secs(3)),
            ..BmcConfig::default()
        };

        PortfolioConfig {
            engines: vec![
                EngineConfig::Pdr(pdr_config_val),
                EngineConfig::Bmc(bmc_config),
            ],
            parallel: true,
            timeout: None,
            parallel_timeout: Some(budget),
            verbose: self.config.verbose,
            validate: self.config.validate,
            // Preprocessing already done via PreprocessSummary::build_bv_native.
            enable_preprocessing: false,
        }
    }
}
