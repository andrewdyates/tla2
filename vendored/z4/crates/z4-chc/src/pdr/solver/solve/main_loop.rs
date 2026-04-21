// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    pub(in crate::pdr::solver) const BV_DISCOVERY_RERUN_BLOCKED_STATE_THRESHOLD: usize = 4;

    pub(super) fn verification_progress_signature(&self) -> VerificationProgressSignature {
        VerificationProgressSignature {
            lemma_count: self.frames.iter().map(|frame| frame.lemmas.len()).sum(),
            must_summary_count: self.reachability.must_summaries.entry_count(),
            reach_fact_count: self.reachability.reach_facts.len(),
        }
    }

    pub(super) fn note_model_verification_failure(&mut self, reason: &str) {
        let progress = self.verification_progress_signature();
        if self.verification.consecutive_unlearnable > 0
            && progress != self.verification.last_unlearnable_progress
        {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Resetting consecutive_unlearnable after learning progress ({reason}): {} -> 0 \
                     [lemmas {}->{}, must_summaries {}->{}, reach_facts {}->{}]",
                    self.verification.consecutive_unlearnable,
                    self.verification.last_unlearnable_progress.lemma_count,
                    progress.lemma_count,
                    self.verification.last_unlearnable_progress.must_summary_count,
                    progress.must_summary_count,
                    self.verification.last_unlearnable_progress.reach_fact_count,
                    progress.reach_fact_count,
                );
            }
            self.verification.consecutive_unlearnable = 0;
        }
        self.verification.last_unlearnable_progress = progress;
        self.verification.consecutive_unlearnable += 1;
        self.verification.total_model_failures += 1;
    }

    /// De-escalate generalization on near-convergence signal (#7911).
    fn maybe_de_escalate_on_convergence_signal(&mut self, old_level: usize) {
        if self.frames.len() < 3 || old_level < 2 {
            return;
        }
        if self.generalization_strategy == GeneralizationStrategy::Default
            || self.generalization_strategy == GeneralizationStrategy::Conservative
        {
            return;
        }
        let cur = self.frames[old_level].lemmas.len();
        let prev = self.frames[old_level - 1].lemmas.len();
        if cur.abs_diff(prev) <= 3 {
            self.de_escalate_generalization_strategy();
        }
    }

    /// Solve the CHC problem
    pub fn solve(&mut self) -> PdrResult {
        // Initialization: validate problem, check init safety, set up must-summaries,
        // run startup discovery. Returns early if any phase proves safe/unsafe.
        if let Some(result) = self.solve_init() {
            return result;
        }

        // Main PDR loop
        //
        // Apply a tighter per-query SMT timeout during the main blocking loop. Startup
        // discovery already has a 10s per-query cap (above). The 5s cap here prevents
        // individual blocking queries from stalling the portfolio for minutes.
        let _smt_timeout_guard =
            if self.config.cancellation_token.is_some() || self.config.solve_timeout.is_some() {
                Some(
                    self.smt
                        .scoped_check_timeout(Some(std::time::Duration::from_secs(5))),
                )
            } else {
                None
            };
        // Reset convergence monitor at solve-loop entry (startup discovery may
        // have consumed wall-clock time that shouldn't count against frame stall).
        self.convergence = ConvergenceMonitor::new();
        self.terminated_by_stagnation = false;
        self.lemma_quality.reset_all();
        let has_budget =
            self.config.cancellation_token.is_some() || self.config.solve_timeout.is_some();

        let mut spurious_count = 0usize;
        while self.frames.len() <= self.config.max_frames {
            // Check cancellation or memory budget (#2769)
            if self.is_cancelled() {
                if self.config.verbose {
                    safe_eprintln!("PDR: Cancelled by portfolio or memory limit");
                }
                self.pdr_trace_conservative_fail(
                    "solve_cancelled",
                    serde_json::json!({
                        "iterations": self.iterations,
                        "frames": self.frames.len(),
                    }),
                    None,
                );
                return self.finish_with_result_trace(PdrResult::Unknown);
            }

            self.iterations += 1;

            // Frame structure invariant: frames[0] is init, frames[k] for k >= 1
            // are PDR levels. Must have at least 2 frames. (#4757)
            debug_assert!(
                self.frames.len() >= 2,
                "BUG: Main loop requires at least 2 frames, got {}",
                self.frames.len()
            );
            // Iteration counter should match actual loop count.
            debug_assert!(
                self.iterations > 0,
                "BUG: iterations counter should be positive in main loop"
            );

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Iteration {}, {} frames",
                    self.iterations,
                    self.frames.len()
                );
            }
            // Convergence monitoring (#7906): graduated stagnation detection.
            let total_lemmas_now: usize = self.frames.iter().map(|f| f.lemmas.len()).sum();
            let problem_hint = self.problem_size_hint;
            let stagnation_response = self.convergence.check_stagnation_graduated(
                self.iterations,
                total_lemmas_now,
                self.frames.len(),
                has_budget,
                &problem_hint,
            );
            if stagnation_response != StagnationResponse::None {
                self.lemma_quality.check_quality();
            }
            let health = self
                .convergence
                .assess_health(stagnation_response, &self.lemma_quality);
            match health {
                ConvergenceHealth::Healthy => {}
                ConvergenceHealth::Slowing => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Convergence slowing at iteration {} ({}s elapsed, stagnant_windows={}, low_quality_windows={})",
                            self.iterations, self.convergence.elapsed().as_secs(),
                            self.convergence.consecutive_stagnant_windows,
                            self.lemma_quality.consecutive_low_quality_windows,
                        );
                    }
                    if !self.restart.stuck_hints_applied {
                        self.restart.stuck_hints_applied = true;
                        self.apply_lemma_hints(crate::lemma_hints::HintStage::Stuck);
                    }
                }
                ConvergenceHealth::Stagnating => {
                    if self.escalate_generalization_strategy() {
                        self.convergence.note_generalization_escalation(
                            self.iterations,
                            total_lemmas_now,
                            self.frames.len(),
                        );
                        self.lemma_quality.reset_all();
                    } else if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Stagnating at max escalation level {} iter {}",
                            self.generalization_escalation_level,
                            self.iterations,
                        );
                    }
                }
                ConvergenceHealth::Stuck => {
                    // Do NOT return Unknown early. The solve_timeout already
                    // enforces the total budget. Premature stagnation abort
                    // causes regressions under high system load where wall-clock
                    // stall detection fires before the solver has had enough
                    // CPU time. Log but continue — PDR may still converge
                    // once escalation strategies take effect.
                    self.terminated_by_stagnation = true;
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Convergence monitor reports stuck at iteration {} ({}s elapsed, {} stagnant windows) — continuing",
                            self.iterations, self.convergence.elapsed().as_secs(),
                            self.convergence.consecutive_stagnant_windows,
                        );
                    }
                    // Reset stagnation windows so we don't keep re-triggering
                    self.convergence.consecutive_stagnant_windows = 0;
                }
            }

            if self.iterations > self.config.max_iterations {
                if self.config.verbose {
                    safe_eprintln!("PDR: Exceeded max iterations");
                }
                self.pdr_trace_conservative_fail(
                    "solve_max_iterations_exceeded",
                    serde_json::json!({
                        "iterations": self.iterations,
                        "max_iterations": self.config.max_iterations,
                        "frames": self.frames.len(),
                    }),
                    None,
                );
                return self.finish_with_result_trace(PdrResult::Unknown);
            }

            // Luby restarts (#1270): when lemma growth stalls, restart to escape local minima
            if self.config.use_restarts
                && self.restart.lemmas_since_restart > self.restart.restart_threshold
            {
                // Pop queue until root (keep only level 0 obligations)
                // Z3 Spacer: while (!m_pob_queue.is_root(*m_pob_queue.top())) { m_pob_queue.pop(); }
                if self.config.use_level_priority {
                    // Priority heap: remove all non-root POBs
                    let root_pobs: Vec<_> = std::mem::take(&mut self.obligations.heap)
                        .into_vec()
                        .into_iter()
                        .filter(|p| p.0.level == 0)
                        .collect();
                    for pob in root_pobs {
                        self.obligations.heap.push(pob);
                    }
                } else {
                    // Deque: remove all non-root POBs
                    self.obligations.deque.retain(|pob| pob.level == 0);
                }

                // Update Luby index and threshold
                self.restart.luby_index += 1;
                self.restart.restart_threshold = (luby(self.restart.luby_index) as usize)
                    * self.config.restart_initial_threshold;
                self.restart.lemmas_since_restart = 0;
                self.restart.restart_count += 1;
                self.clear_restart_caches();

                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Restart #{} at iteration {} (next threshold: {})",
                        self.restart.restart_count,
                        self.iterations,
                        self.restart.restart_threshold
                    );
                }

                // #2393: On first restart, apply expanded Stuck-stage hints.
                // ModResidueHintProvider enumerates more residue values at Stuck
                // (20 vs 10 at Startup), which helps modular arithmetic benchmarks
                // like const_mod_3, dillig02_m, half_true_modif_m.
                if !self.restart.stuck_hints_applied {
                    self.restart.stuck_hints_applied = true;
                    self.apply_lemma_hints(crate::lemma_hints::HintStage::Stuck);
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Applied Stuck-stage lemma hints at restart #{}",
                            self.restart.restart_count
                        );
                    }
                }

                // Publish learned lemmas to cooperative blackboard (#7910).
                // At each restart, share our frame lemmas with other engines.
                self.publish_to_blackboard();
            }

            // Try to strengthen current frame
            let strengthen_result = self.strengthen();
            // Track strengthen outcome for convergence monitoring.
            let productive = matches!(
                strengthen_result,
                StrengthenResult::Safe | StrengthenResult::Continue
            );
            self.convergence.note_strengthen(productive);
            match strengthen_result {
                StrengthenResult::Safe => {
                    // Check for fixed point
                    if let Some(mut model) = self.check_fixed_point() {
                        // SOUNDNESS (#5745, #5970): Model verification before returning Safe.
                        //
                        // convergence_proven: Frame convergence proved inductiveness of the
                        // full frame conjunction. Use query-only verification (skip
                        // transition inductiveness, only check error blocking). Error
                        // blocking is NOT implied by convergence because
                        // propagate_tight_bound_constants can weaken the model formula
                        // by substituting away variables. (#5970, #7410)
                        //
                        // individually_inductive: Each lemma was verified self-inductive.
                        // Use query-only verification (checks error-blocking only). (#7410)
                        //
                        // Other models: full verify_model + verify_model_fresh.
                        let verified = if model.individually_inductive {
                            self.verify_model_query_only(&model)
                        } else {
                            self.verify_model(&model)
                        };
                        if !verified {
                            self.note_model_verification_failure("check_fixed_point verify_model");
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: check_fixed_point returned model that fails verify_model(); \
                                     consecutive_unlearnable={}, total_model_failures={}, continuing",
                                    self.verification.consecutive_unlearnable,
                                    self.verification.total_model_failures,
                                );
                            }
                            // Don't return Safe with invalid model - continue strengthening
                        } else if !{
                            if model.individually_inductive {
                                // #5970: query-only fresh verification for per-lemma proven models.
                                self.verify_model_fresh_query_only(&model)
                            } else {
                                // SOUNDNESS (#5922): Fresh-context confirmation.
                                self.verify_model_fresh(&model)
                            }
                        } {
                            self.note_model_verification_failure(
                                "check_fixed_point fresh-context verification",
                            );
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: model passes warm verify_model but fails fresh-context \
                                     verification (#5922); continuing"
                                );
                            }
                        } else {
                            // Reset consecutive counter on successful verification
                            self.verification.consecutive_unlearnable = 0;
                            // SOUNDNESS (#5922): Save verified model before simplification.
                            // The model was already verified at line 341. If simplification
                            // breaks it, we can fall back to this known-good version.
                            let verified_model = model.clone();
                            // Simplify the invariant (Z3 Spacer's unconditional solve-completion cleanup)
                            let simp = self.simplify_model(&mut model);
                            // Re-verify when simplification modified the model (#5805, #5922).
                            if simp.modified() && !self.verify_model(&model) {
                                if simp.free_vars_sanitized {
                                    // Free-var sanitization means the pre-simplification model
                                    // had undeclared variables — it may be fundamentally
                                    // invalid (#5805). Do NOT fall back; continue searching.
                                    self.note_model_verification_failure(
                                        "simplified fixed-point model free-var sanitization",
                                    );
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: simplified model fails re-verification after \
                                             free-variable sanitization; continuing"
                                        );
                                    }
                                } else {
                                    // Only redundancy removal — pre-simplification model is
                                    // known valid (verified at line 341). Fall back (#5922).
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: simplified model fails re-verification after \
                                             redundancy removal; falling back to pre-simplification model"
                                        );
                                    }
                                    return self
                                        .finish_with_result_trace(PdrResult::Safe(verified_model));
                                }
                            } else {
                                return self.finish_with_result_trace(PdrResult::Safe(model));
                            }
                        }
                    }

                    // Part of #2059: If check_fixed_point fails (frames don't converge due to
                    // non-pushable lemmas like scaled bounds), try direct safety proof.
                    // The frame[1] invariants may already prove all error states unreachable
                    // even without frame convergence.
                    if let Some(mut model) = self.try_main_loop_direct_safety_proof() {
                        // #5877: For strictly self-inductive models, skip fresh-context
                        // verification. Each lemma was individually verified via strict
                        // self-inductiveness (no frame strengthening). The conjunction
                        // of strictly self-inductive lemmas is inductive by construction.
                        // Fresh-context verification can fail on complex disjunctive
                        // transitions where the SMT solver struggles with the full
                        // conjunction (ITE case-split handles these per-lemma).
                        let skip_fresh = model.individually_inductive;
                        // SOUNDNESS (#5922): Fresh-context confirmation (unless strictly self-inductive).
                        if !skip_fresh && !self.verify_model_fresh(&model) {
                            self.note_model_verification_failure(
                                "direct-proof fresh-context verification",
                            );
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: direct-proof model passes warm verify but fails \
                                     fresh-context verification (#5922); continuing"
                                );
                            }
                        } else {
                            // SOUNDNESS (#5922): Save model before simplification.
                            let original_model = model.clone();
                            // Simplify the invariant (Z3 Spacer's unconditional solve-completion cleanup)
                            let simp = self.simplify_model(&mut model);
                            // Re-verify when simplification modified the model (#5805, #5922).
                            if simp.modified() && !self.verify_model(&model) {
                                if simp.free_vars_sanitized {
                                    // Free-var sanitization — pre-simplification model may be
                                    // fundamentally invalid (#5805). Continue searching.
                                    self.note_model_verification_failure(
                                        "simplified direct-proof model free-var sanitization",
                                    );
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: simplified direct-proof model fails re-verification \
                                             after free-variable sanitization; continuing"
                                        );
                                    }
                                } else {
                                    // Only redundancy removal — fall back to original (#5922).
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: simplified direct-proof model fails re-verification; \
                                             falling back to pre-simplification model"
                                        );
                                    }
                                    return self
                                        .finish_with_result_trace(PdrResult::Safe(original_model));
                                }
                            } else {
                                return self.finish_with_result_trace(PdrResult::Safe(model));
                            }
                        }
                    }
                    // Check if we're stuck in model verification failures without
                    // learning progress. This catches retry-without-learning loops
                    // while allowing continued search when frames/must-summaries keep
                    // growing between failed verification attempts.
                    const MAX_UNLEARNABLE_FAILURES: usize = 10;
                    if self.verification.consecutive_unlearnable >= MAX_UNLEARNABLE_FAILURES {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Giving up after {} consecutive unlearnable verification failures",
                                self.verification.consecutive_unlearnable
                            );
                        }
                        self.pdr_trace_conservative_fail(
                            "solve_consecutive_unlearnable_failures",
                            serde_json::json!({
                                "consecutive_unlearnable_failures": self.verification.consecutive_unlearnable,
                                "max_unlearnable_failures": MAX_UNLEARNABLE_FAILURES,
                                "iterations": self.iterations,
                                "frames": self.frames.len(),
                                "verification_progress": {
                                    "lemmas": self.verification.last_unlearnable_progress.lemma_count,
                                    "must_summaries": self.verification.last_unlearnable_progress.must_summary_count,
                                    "reach_facts": self.verification.last_unlearnable_progress.reach_fact_count,
                                },
                            }),
                            None,
                        );
                        return self.finish_with_result_trace(PdrResult::Unknown);
                    }
                    // Add new frame and continue
                    let old_level = self.frames.len() - 1;
                    self.push_frame();
                    self.convergence.note_frame_advance();
                    self.maybe_de_escalate_on_convergence_signal(old_level);
                    // Propagate must-summaries forward to the new level
                    self.propagate_must_summaries_forward(old_level - 1, old_level);
                    // Re-run kernel-based affine discovery after must-summaries accumulate.
                    //
                    // Some affine invariants are only visible after a few loop iterations
                    // (reachable states), not from degenerate init samples. (#1995)
                    if !self.is_quick_check_mode()
                        && old_level > 0
                        && old_level <= 5
                        && (old_level.is_multiple_of(3) || old_level == 5)
                    {
                        let max_check = old_level.min(5);
                        let has_reachable_summaries = (1..=max_check)
                            .any(|l| self.reachability.must_summaries.has_any_at_level(l));
                        if has_reachable_summaries {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Re-running affine kernel discovery after must-summary propagation to level {}",
                                    old_level
                                );
                            }
                            self.discover_affine_invariants_via_kernel(None);
                            self.propagate_affine_invariants_to_derived_predicates();
                        }
                    }
                    // Periodically re-run ITE constant propagation to leverage learned invariants
                    // This enables proving ITE branch constants using newly-learned predicate invariants
                    if self.iterations.is_multiple_of(5) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Re-running ITE constant propagation at iteration {}",
                                self.iterations
                            );
                        }
                        self.discover_ite_constant_propagation();
                    }
                }
                StrengthenResult::Unsafe(cex) => {
                    if self.config.verbose {
                        safe_eprintln!("PDR: Found counterexample with {} steps", cex.steps.len());
                    }
                    // Verify counterexample is forward-reachable (soundness-critical #1288)
                    match self.verify_counterexample(&cex) {
                        CexVerificationResult::Valid => {
                            return self.finish_with_result_trace(PdrResult::Unsafe(cex));
                        }
                        CexVerificationResult::Unknown => {
                            // SOUNDNESS FIX (#1288): Cannot return Unsafe when verification
                            // is inconclusive. Return Unknown to avoid unsound results.
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Counterexample verification inconclusive (Unknown)"
                                );
                            }
                            self.pdr_trace_conservative_fail(
                                "solve_cex_verification_inconclusive",
                                serde_json::json!({
                                    "cex_steps": cex.steps.len(),
                                    "iterations": self.iterations,
                                    "frames": self.frames.len(),
                                }),
                                None,
                            );
                            return self.finish_with_result_trace(PdrResult::Unknown);
                        }
                        CexVerificationResult::Spurious => {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Counterexample failed verification (spurious)"
                                );
                            }
                            // Spurious counterexample handling with Z3 Spacer-style weakness mechanism (#1664).
                            // Instead of a simple global counter, we track weakness per (predicate, state).
                            // This allows retrying the same spurious state with different abstraction levels
                            // before giving up, mirroring Z3's POB weakness bump on derivation failure.

                            // Extract root state from witness for weakness tracking
                            let root_info = cex.witness.as_ref().and_then(|w| {
                                w.entries
                                    .first()
                                    .map(|e| (e.predicate, e.state.structural_hash()))
                            });

                            // Check/bump weakness for this specific (predicate, state) pair
                            let should_give_up = if let Some((pred, state_hash)) = root_info {
                                let key = (pred, state_hash);
                                let weakness = self.bump_spurious_cex_weakness(key);
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Spurious CEX weakness for pred {} = {}",
                                        pred.index(),
                                        weakness
                                    );
                                }
                                // Give up on this (pred, state) after MAX_WEAKNESS retries
                                weakness > ProofObligation::MAX_WEAKNESS
                            } else {
                                // No witness info - fall back to global counter
                                true
                            };

                            if should_give_up {
                                spurious_count += 1;
                            }

                            // Global safety limit to prevent infinite loops
                            // Limit raised from 100 to 500 per designs/2026-01-31-chc-regression-root-cause.md
                            if spurious_count > 500 {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Too many spurious counterexamples ({}), giving up",
                                        spurious_count
                                    );
                                }
                                self.pdr_trace_conservative_fail(
                                    "solve_spurious_cex_limit",
                                    serde_json::json!({
                                        "spurious_count": spurious_count,
                                        "iterations": self.iterations,
                                        "frames": self.frames.len(),
                                    }),
                                    None,
                                );
                                return self.finish_with_result_trace(PdrResult::Unknown);
                            }

                            // Learn from the spurious CEX: bound negation, ITE blocking,
                            // affine discovery, concrete value blocking (see spurious_cex.rs).
                            self.learn_from_spurious_cex(&cex);
                            // Continue searching
                        }
                    }
                }
                StrengthenResult::Unknown => {
                    if self.config.verbose {
                        safe_eprintln!("PDR: Strengthen returned Unknown");
                    }
                    return self.finish_with_result_trace(PdrResult::Unknown);
                }
                StrengthenResult::Continue => {
                    // Increase the bound and continue. This is used when must-summary reachability
                    // is enabled and we can't block the root query state at the current level, but
                    // a concrete counterexample may appear at a deeper level.
                    let old_level = self.frames.len() - 1;
                    self.push_frame();
                    self.convergence.note_frame_advance();
                    self.maybe_de_escalate_on_convergence_signal(old_level);
                    self.propagate_must_summaries_forward(old_level - 1, old_level);
                    // Re-run kernel-based affine discovery after must-summaries accumulate
                    // (matches the `Safe` case).
                    if !self.is_quick_check_mode()
                        && old_level > 0
                        && old_level <= 5
                        && (old_level.is_multiple_of(3) || old_level == 5)
                    {
                        let max_check = old_level.min(5);
                        let has_reachable_summaries = (1..=max_check)
                            .any(|l| self.reachability.must_summaries.has_any_at_level(l));
                        if has_reachable_summaries {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Re-running affine kernel discovery after must-summary propagation to level {}",
                                    old_level
                                );
                            }
                            self.discover_affine_invariants_via_kernel(None);
                            self.propagate_affine_invariants_to_derived_predicates();
                        }
                    }
                    // Periodically re-run ITE constant propagation to leverage learned invariants
                    // (matches the `Safe` case).
                    if self.iterations.is_multiple_of(5) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Re-running ITE constant propagation at iteration {}",
                                self.iterations
                            );
                        }
                        self.discover_ite_constant_propagation();
                    }
                }
            }
        }

        if self.config.verbose {
            safe_eprintln!("PDR: Exceeded max frames");
        }
        self.pdr_trace_conservative_fail(
            "solve_max_frames_exceeded",
            serde_json::json!({
                "frames": self.frames.len(),
                "max_frames": self.config.max_frames,
                "iterations": self.iterations,
            }),
            None,
        );
        self.finish_with_result_trace(PdrResult::Unknown)
    }
}
