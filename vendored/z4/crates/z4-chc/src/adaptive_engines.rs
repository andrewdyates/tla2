// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Alternative engine methods for the adaptive portfolio solver.
//!
//! Solve-trivial fast path, K-induction, structural synthesis, and
//! budget-aware alternative engine dispatch.

use crate::adaptive::AdaptivePortfolio;
use crate::adaptive_decision_log::DecisionEntry;
use crate::bmc::BmcConfig;
use crate::classifier::ProblemFeatures;
use crate::failure_analysis::{FailureAnalysis, FailureGuide};
use crate::kind::{KindConfig, KindResult, KindSolver};
use crate::pdr::{InvariantModel, PdrConfig, PdrResult, PdrSolver, PredicateInterpretation};
use crate::portfolio::{EngineConfig, PortfolioConfig, PortfolioResult};
use crate::single_loop::SingleLoopTransformation;
use crate::synthesis::{StructuralSynthesizer, SynthesisResult};
use crate::{ChcExpr, ChcVar};
use std::time::{Duration, Instant};
use z4_sat::TlaTraceable;

impl AdaptivePortfolio {
    /// Solve entry-exit-only problems by delegating to portfolio.
    ///
    /// These problems have no predicates - all clauses are of the form:
    /// `constraint ⇒ false` (queries with no body predicates).
    ///
    /// Delegates to `PortfolioSolver` whose `try_solve_trivial()` handles
    /// predicate-free problems and routes Safe results through `validate_safe()`
    /// (#5794, #5745). Previously this method duplicated the SMT checking logic
    /// and returned Safe/Unsafe directly without portfolio validation.
    ///
    /// Reference: Golem's `solveTrivial()` in engine/Common.cc:6-36
    pub(crate) fn solve_entry_exit_only(&self, _features: &ProblemFeatures) -> PortfolioResult {
        // Route through portfolio which validates Safe results via try_solve_trivial().
        // Entry-exit-only problems are predicate-free: try_solve_trivial() handles
        // them directly with proper validate_safe() checks. Preprocessing is disabled
        // since the problem is already simple (no predicates to inline). One PDR engine
        // is included as fallback if try_solve_trivial() returns None (SMT Unknown).
        let config = PortfolioConfig {
            engines: vec![EngineConfig::Pdr(PdrConfig::default())],
            enable_preprocessing: false,
            verbose: self.config.verbose,
            validate: self.config.validate,
            parallel: false,
            timeout: None,
            parallel_timeout: None,
        };
        self.run_portfolio(config)
    }

    /// Solve trivial problems - fast path with minimal overhead.
    ///
    /// Uses failure-guided retry: if first PDR attempt returns Unknown,
    /// analyze the failure and retry with adjusted configuration.
    pub(crate) fn solve_trivial(
        &self,
        _features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> PortfolioResult {
        // Stage 0: Try structural synthesis (< 1ms overhead)
        let synth_start = Instant::now();
        if let Some(result) = self.try_synthesis() {
            if self.config.verbose {
                safe_eprintln!("Adaptive: Trivial problem solved by structural synthesis");
            }
            self.decision_log.log_decision(DecisionEntry {
                stage: "trivial_synthesis",
                gate_result: true,
                gate_reason: "pattern found".to_string(),
                budget_secs: 0.0,
                elapsed_secs: synth_start.elapsed().as_secs_f64(),
                result: Self::result_to_str(&result),
                lemmas_learned: 0,
                max_frame: 0,
            });
            return result;
        }
        self.decision_log.log_decision(DecisionEntry {
            stage: "trivial_synthesis",
            gate_result: false,
            gate_reason: "no pattern".to_string(),
            budget_secs: 0.0,
            elapsed_secs: synth_start.elapsed().as_secs_f64(),
            result: "skipped",
            lemmas_learned: 0,
            max_frame: 0,
        });

        if self.config.verbose {
            safe_eprintln!("Adaptive: Using trivial fast path (single-threaded PDR)");
        }

        // Single-threaded PDR with minimal config - no portfolio overhead
        let mut config = PdrConfig {
            max_frames: 50,
            max_iterations: 1000,
            verbose: self.config.verbose,
            ..PdrConfig::default()
        }
        .with_tla_trace_from_env();
        self.apply_user_hints(&mut config);

        // Use solve_with_stats for failure analysis (#1870)
        let pdr_start = Instant::now();
        let result_with_stats = PdrSolver::solve_problem_with_stats(&self.problem, config.clone());
        self.accumulate_stats(&result_with_stats.stats);
        let pdr_elapsed = pdr_start.elapsed().as_secs_f64();

        // If solved, validate before returning (#5549 soundness fix)
        if !matches!(result_with_stats.result, PdrResult::Unknown) {
            let validated = self.validate_adaptive_result(result_with_stats.result);
            if !matches!(validated, PdrResult::Unknown) {
                self.decision_log.log_decision(DecisionEntry {
                    stage: "trivial_pdr",
                    gate_result: true,
                    gate_reason: "initial PDR".to_string(),
                    budget_secs: 0.0,
                    elapsed_secs: pdr_elapsed,
                    result: Self::result_to_str(&validated),
                    lemmas_learned: result_with_stats.learned_lemmas.len(),
                    max_frame: result_with_stats.stats.max_frame,
                });
                return validated;
            }
        }
        self.decision_log.log_decision(DecisionEntry {
            stage: "trivial_pdr",
            gate_result: true,
            gate_reason: "initial PDR returned unknown".to_string(),
            budget_secs: 0.0,
            elapsed_secs: pdr_elapsed,
            result: "unknown",
            lemmas_learned: result_with_stats.learned_lemmas.len(),
            max_frame: result_with_stats.stats.max_frame,
        });

        // Budget check before retry stages (#7034)
        if self.budget_exhausted(deadline) {
            if self.config.verbose {
                safe_eprintln!("Adaptive: Budget exhausted after initial PDR, skipping retry");
            }
            return PortfolioResult::Unknown;
        }

        // Analyze failure and guide retry
        let analysis = FailureAnalysis::from_stats(&result_with_stats.stats);
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: PDR returned Unknown - {} (confidence {:.0}%)",
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

        // Budget check before PDR retry (#7034)
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
            let retry_start = Instant::now();
            let mut retry_config = guide.apply_to_config(config);
            retry_config
                .user_hints
                .extend(result_with_stats.learned_lemmas);
            let retry_result = PdrSolver::solve_problem_with_stats(&self.problem, retry_config);
            self.accumulate_stats(&retry_result.stats);
            let validated = self.validate_adaptive_result(retry_result.result);
            self.decision_log.log_decision(DecisionEntry {
                stage: "trivial_retry",
                gate_result: true,
                gate_reason: format!("{} adjustments", guide.adjustments.len()),
                budget_secs: 0.0,
                elapsed_secs: retry_start.elapsed().as_secs_f64(),
                result: Self::result_to_str(&validated),
                lemmas_learned: retry_result.learned_lemmas.len(),
                max_frame: retry_result.stats.max_frame,
            });
            return validated;
        }

        // No retry possible, return original Unknown
        PortfolioResult::Unknown
    }

    /// Try an alternative engine with budget-aware timeout (#7034).
    ///
    /// Caps the alternative engine's timeout to the remaining budget instead of
    /// using a hardcoded 10s. Returns `None` if the budget is exhausted.
    pub(crate) fn try_alternative_engine_budgeted(
        &self,
        engine: &crate::failure_analysis::AlternativeEngine,
        deadline: Option<Instant>,
    ) -> Option<PortfolioResult> {
        if self.budget_exhausted(deadline) {
            return None;
        }
        use crate::failure_analysis::AlternativeEngine;
        match engine {
            AlternativeEngine::Bmc { suggested_depth } => {
                let timeout = match self.remaining_budget(deadline) {
                    Some(remaining) => remaining.min(Duration::from_secs(10)),
                    None => Duration::from_secs(10),
                };
                if timeout.is_zero() {
                    return None;
                }
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Trying BMC (depth {}, budget {:.1}s) to verify deep CEX",
                        suggested_depth,
                        timeout.as_secs_f64()
                    );
                }
                let bmc_config = PortfolioConfig {
                    engines: vec![EngineConfig::Bmc(BmcConfig::with_engine_config(
                        *suggested_depth,
                        self.config.verbose,
                        None,
                    ))],
                    parallel: false,
                    timeout: None,
                    parallel_timeout: Some(timeout),
                    verbose: self.config.verbose,
                    validate: self.config.validate,
                    enable_preprocessing: true,
                };
                let result = self.run_portfolio(bmc_config);
                if matches!(
                    result,
                    PortfolioResult::Safe(_) | PortfolioResult::Unsafe(_)
                ) {
                    return Some(result);
                }
            }
        }
        None
    }

    /// Try K-Induction with forward and backward checks.
    ///
    /// K-Induction is a bounded model checking technique that:
    /// 1. Checks if bad state is reachable in ≤k steps (base case)
    /// 2. Checks if ¬bad is k-inductive (forward induction)
    /// 3. Checks if init is k-inductive backward (backward induction)
    ///
    /// For multi-predicate problems, applies SingleLoop encoding to produce
    /// a synthetic single-predicate transition system. Kind doesn't use
    /// interpolation during solving, so Bool location variables from
    /// SingleLoop are acceptable (unlike PDKind, #6500).
    ///
    /// This is Golem's approach per Kind.cc:44-133.
    pub(crate) fn try_kind(&self, budget: Duration) -> Option<PortfolioResult> {
        // #5877: BV problems use non-incremental mode where each query rebuilds
        // the entire formula. At k>=2, the forward induction formula grows large
        // enough that preprocessing (propagate_constants, convert_expr, Tseitin)
        // consumes the entire per-query timeout before DPLL starts. Cap max_k
        // at 1 for BV: k=0 and k=1 are fast (~10ms each), k=2 is catastrophic.
        let has_bv = self.problem.has_bv_sorts();
        let max_k = if has_bv { 1 } else { 20 };
        // Pure LIA needs a wider per-query budget than the BV lane here.
        // The direct Kind probe should stay close to the portfolio Kind
        // defaults: 8s per query for LIA gives the multi-predicate canary
        // enough room to finish without overcommitting the fallback path.
        // BV remains capped at 1s because larger per-query budgets mostly
        // inflate bit-blast preprocessing without improving robustness.
        let query_timeout = if has_bv {
            budget.min(Duration::from_secs(1))
        } else {
            budget.min(Duration::from_secs(8))
        };
        let kind_config = KindConfig::with_engine_config(
            max_k,
            query_timeout, // Per-query timeout (capped by remaining budget)
            budget,
            self.config.verbose,
            None,
        );

        // For multi-predicate problems, apply SingleLoop encoding so Kind
        // can operate on a synthetic single-predicate transition system.
        let problem = self.scalarized_problem();
        let (solver_problem, singleloop_ctx) = if problem.predicates().len() > 1 {
            let mut tx = SingleLoopTransformation::new(problem.clone());
            match tx.transform() {
                Some(sys) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: K-Induction using SingleLoop encoding ({} state vars)",
                            sys.state_vars.len()
                        );
                    }
                    let synthetic = sys.to_chc_problem();
                    let state_vars = sys.state_vars.clone();
                    (synthetic, Some((tx, state_vars)))
                }
                None => (problem.clone(), None),
            }
        } else {
            (problem.clone(), None)
        };

        let mut solver = KindSolver::new(solver_problem, kind_config);
        solver.maybe_enable_tla_trace_from_env();
        let result = solver.solve();

        match &result {
            KindResult::Safe(model) => {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: K-Induction found invariant with {} predicates",
                        model.len()
                    );
                }

                // If SingleLoop was used, back-translate to multi-predicate model.
                let final_model = if let Some((ref tx, ref state_vars)) = singleloop_ctx {
                    match crate::portfolio::singleloop_safe::SingleLoopSafeWitness::from_trl(
                        model, state_vars,
                    ) {
                        Some(witness) => {
                            crate::portfolio::singleloop_safe::translate_singleloop_safe(
                                problem, tx, &witness,
                            )
                        }
                        None => {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "Adaptive: K-Induction SingleLoop back-translation failed"
                                );
                            }
                            None
                        }
                    }
                } else {
                    Some(model.clone())
                };

                let Some(translated_model) = final_model else {
                    return None;
                };

                // Kind validates internally with extended BMC base case checks,
                // but apply external query-only validation for defense-in-depth (#5549).
                // Kind's invariants are k-inductive, not necessarily 1-inductive (#5211).
                // Only query clauses are checked — transition clause checks would reject
                // valid k-inductive invariants. (#5825: replaces Duration::ZERO convention
                // broken by #5745's budget-expiry rejection logic.)
                let candidate = PortfolioResult::Safe(translated_model);
                let validated = self.validate_kind_result_query_only(candidate);
                if matches!(validated, PortfolioResult::Unknown) {
                    None // Demoted — fall through to portfolio engines
                } else {
                    // SOUNDNESS AUDIT (#7912, Gap E): Kind uses query-only validation
                    // (not full validate_safe) because k-inductive invariants are not
                    // necessarily 1-inductive — transition clause checks would produce
                    // false rejections (#5211, #5825). Query-only validation confirms
                    // the invariant excludes bad states, which is soundness-critical.
                    debug_assert!(
                        matches!(validated, PortfolioResult::Safe(_)),
                        "BUG: Kind validated result should be Safe, got {:?}",
                        std::mem::discriminant(&validated),
                    );
                    Some(validated)
                }
            }
            KindResult::Unsafe(cex) => {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: K-Induction found counterexample ({} steps)",
                        cex.steps.len()
                    );
                }

                // SingleLoop encoding is an overapproximation of multi-predicate
                // problems. Counterexamples from the overapproximation are often
                // spurious — they represent paths through the synthetic merged
                // transition system that do not exist in the original multi-predicate
                // problem. Only Safe results transfer from overapproximation.
                //
                // Previously, spurious CEXs were returned as Unsafe, short-circuiting
                // the entire adaptive pipeline (non-inlined PDR, portfolio, retry).
                // Benchmarks like s_multipl_23, s_multipl_25, half_true_modif_m hit
                // this: Kind found a spurious CEX at k=2 in <0.1s, the final
                // validation rejected it, and the solver returned "unknown" with
                // 13+ seconds of unused budget.
                if singleloop_ctx.is_some() {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: Discarding Kind counterexample from SingleLoop overapproximation (spurious)"
                        );
                    }
                    None
                } else {
                    // Kind produces concrete counterexample traces via
                    // make_unsafe_with_trace (base case SAT + fresh cross-check).
                    // Return it as PortfolioResult::Unsafe for validation by
                    // finalize_verified_result. Part of #7897.
                    Some(PortfolioResult::Unsafe(cex.clone()))
                }
            }
            KindResult::Unknown => None,
            KindResult::NotApplicable => {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: K-Induction not applicable (not a transition system)"
                    );
                }
                None
            }
        }
    }

    /// Try structural synthesis for patterned problems.
    ///
    /// Returns Some(PortfolioResult::Safe) if synthesis succeeds and the adaptive
    /// validation path accepts the model, None otherwise.
    ///
    /// Unlike previous implementation that returned Safe without verification (#1949),
    /// we now route synthesized models through the same adaptive Safe-validation
    /// helper used by other direct-engine results.
    pub(crate) fn try_synthesis(&self) -> Option<PortfolioResult> {
        let synth = StructuralSynthesizer::new(&self.problem);
        match synth.try_synthesize() {
            SynthesisResult::Success(synthesized) => {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Structural synthesis succeeded with pattern: {}",
                        synthesized.pattern
                    );
                }

                // Build a TOTAL InvariantModel: all predicates get an interpretation.
                // Missing predicates are assigned `true` (universal relation), matching
                // synthesis inductiveness semantics (#1950).
                let mut model = InvariantModel::new();

                for pred in self.problem.predicates() {
                    // Build PDR canonical vars (__p{pred}_a{i}) instead of synthesis vars (x{i}).
                    // This matches the K-induction path and PDR's verify_model expectations.
                    let synth_vars: Vec<_> = pred
                        .arg_sorts
                        .iter()
                        .enumerate()
                        .map(|(i, sort)| ChcVar::new(format!("x{i}"), sort.clone()))
                        .collect();
                    let pdr_vars: Vec<_> = pred
                        .arg_sorts
                        .iter()
                        .enumerate()
                        .map(|(i, sort)| {
                            ChcVar::new(format!("__p{}_a{}", pred.id.index(), i), sort.clone())
                        })
                        .collect();

                    let formula = if let Some(expr) = synthesized.interpretations.get(&pred.id) {
                        // Substitute x{i} -> __p{pred}_a{i}
                        let subst: Vec<_> = synth_vars
                            .iter()
                            .cloned()
                            .zip(pdr_vars.iter().cloned().map(ChcExpr::var))
                            .collect();
                        expr.substitute(&subst)
                    } else {
                        // Missing predicate -> true (universal relation)
                        ChcExpr::bool_const(true)
                    };

                    let interp = PredicateInterpretation::new(pdr_vars, formula);
                    model.set(pred.id, interp);
                }

                match self.validate_adaptive_result(PdrResult::Safe(model)) {
                    PdrResult::Safe(model) => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "Adaptive: Structural synthesis model passed adaptive validation"
                            );
                        }
                        Some(PortfolioResult::Safe(model))
                    }
                    PdrResult::Unknown | PdrResult::NotApplicable => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "Adaptive: Structural synthesis model failed adaptive validation, ignoring"
                            );
                        }
                        None
                    }
                    PdrResult::Unsafe(_) => {
                        unreachable!("Safe synthesis candidate cannot validate to Unsafe")
                    }
                }
            }
            SynthesisResult::NotInductive => {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Structural synthesis found pattern but not inductive"
                    );
                }
                None
            }
            SynthesisResult::NoPattern => None,
        }
    }
}
