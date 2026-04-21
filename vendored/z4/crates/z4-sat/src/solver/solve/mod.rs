// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Main solve loop and proof finalization.
//!
//! Split into submodules for maintainability (#4933, #5142):
//! - `analyze`: Shared conflict-analysis skeleton (chrono BT + learn + enqueue)
//! - `theory_callback`: Theory/extension callback abstraction
//! - `theory_entry`: Theory closure entry points
//! - `extension_entry`: Extension-mode entry points and init
//! - `theory_backend`: Unified CDCL backend loop for theory/extension
//! - `diagnostics`: TLA tracing and diagnostic emission
//! - `inprocessing_schedule`: Inprocessing pass scheduling facade
//! - `inprocessing_maintenance`: Garbage drain and gate checks
//! - `inprocessing_equivalence`: Equivalence/probing front-half passes
//! - `inprocessing_elimination`: Elimination back-half passes
//! - `inprocessing_round_end`: Round-end invariant checks and telemetry
//! - `finalize`: Result declaration and proof finalization

mod analyze;
mod diagnostics;
mod ext_conflict;
mod extension_entry;
mod finalize;
mod finalize_sat;
mod finalize_unsat;
mod inprocessing_elimination;
mod inprocessing_maintenance;
mod inprocessing_schedule;
#[cfg(test)]
mod tests;
mod theory_backend;
mod theory_callback;
mod theory_entry;

use super::*;
use theory_callback::NullCallback;

impl Solver {
    /// Run one inprocessing pass with scoped diagnostic tracing and timing.
    #[inline]
    pub(super) fn run_timed_diagnostic_inprocessing_pass<T>(
        &mut self,
        pass: DiagnosticPass,
        run: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let start = std::time::Instant::now();
        self.set_diagnostic_pass(pass);
        let result = run(self);
        self.clear_diagnostic_pass();
        let elapsed_ns = start.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
        self.stats.record_inprocessing_time(pass, elapsed_ns);
        result
    }

    /// Convert an assumption-path model to a `SatResult`.
    ///
    /// Always-on model-length validation (#5749 Phase 5): if the model length
    /// does not match `user_num_vars`, returns `Unknown` with
    /// `InvalidSatModel` instead of producing a bogus `Sat`.
    /// The model has already been verified by `finalize_sat_model` inside
    /// `solve_with_assumptions_impl`, so a length mismatch here indicates a
    /// corruption bug in the type-conversion layer, not a solver bug.
    #[inline]
    fn sat_from_assume_model(&mut self, model: Vec<bool>, context: &'static str) -> SatResult {
        if model.len() != self.user_num_vars {
            tracing::error!(
                context,
                model_len = model.len(),
                user_num_vars = self.user_num_vars,
                "sat_from_assume_model: model length mismatch"
            );
            return self.declare_unknown_with_reason(SatUnknownReason::InvalidSatModel);
        }
        #[cfg(debug_assertions)]
        self.debug_assert_sat_result_model(&model, context);
        // #7912: verify the finalized external model against all original clauses.
        debug_assert!(
            self.verify_external_model(&model),
            "BUG: Invalid SAT model in sat_from_assume_model ({context})"
        );
        SatResult::Sat(model)
    }

    /// Convert an assumption-path model to an `AssumeResult`.
    ///
    /// Always-on model-length validation (#5749 Phase 5): if the model length
    /// does not match `user_num_vars`, returns `Unknown` instead of `Sat`.
    #[inline]
    pub(super) fn assume_sat_from_assume_model(
        &mut self,
        model: Vec<bool>,
        context: &'static str,
    ) -> AssumeResult {
        if model.len() != self.user_num_vars {
            tracing::error!(
                context,
                model_len = model.len(),
                user_num_vars = self.user_num_vars,
                "assume_sat_from_assume_model: model length mismatch"
            );
            return self.declare_assume_unknown_with_reason(SatUnknownReason::InvalidSatModel);
        }
        #[cfg(debug_assertions)]
        self.debug_assert_sat_result_model(&model, context);
        // #7912: verify the finalized external model against all original clauses.
        debug_assert!(
            self.verify_external_model(&model),
            "BUG: Invalid SAT model in assume_sat_from_assume_model ({context})"
        );
        AssumeResult::Sat(model)
    }

    /// Solve the formula
    pub fn solve(&mut self) -> VerifiedSatResult {
        VerifiedSatResult::from_validated(self.solve_raw())
    }

    /// Internal solve returning raw `SatResult`.
    fn solve_raw(&mut self) -> SatResult {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;
        self.cold.finalize_sat_fail_count = 0;

        if self.has_empty_clause {
            let result = self.declare_unsat();
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        if self.cold.scope_selectors.is_empty() {
            let result = self.solve_no_assumptions(|| false);
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        let assumptions = self.compose_scope_assumptions(&[]);

        let result =
            match self.solve_with_assumptions_impl(&assumptions, None::<&fn() -> bool>, None) {
                AssumeResult::Sat(model) => {
                    self.sat_from_assume_model(model, "solve() scope-selector path")
                }
                AssumeResult::Unsat(_) => SatResult::Unsat,
                AssumeResult::Unknown => SatResult::Unknown,
            };
        self.trace_sat_result(&result);
        self.finish_tla_trace();
        result
    }

    /// Solve the formula with an interrupt callback
    ///
    /// The callback is checked periodically (every ~100 conflicts). If it returns
    /// `true`, solving is interrupted and `SatResult::Unknown` is returned.
    ///
    /// This is useful for parallel portfolio solving where multiple solvers run
    /// concurrently and can be stopped when one finds a solution.
    pub fn solve_interruptible<F>(&mut self, should_stop: F) -> VerifiedSatResult
    where
        F: Fn() -> bool,
    {
        VerifiedSatResult::from_validated(self.solve_interruptible_raw(should_stop))
    }

    /// Internal interruptible solve returning raw `SatResult`.
    fn solve_interruptible_raw<F>(&mut self, should_stop: F) -> SatResult
    where
        F: Fn() -> bool,
    {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;
        self.cold.finalize_sat_fail_count = 0;

        if self.has_empty_clause {
            let result = self.declare_unsat();
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        if self.cold.scope_selectors.is_empty() {
            let result = self.solve_no_assumptions(should_stop);
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        let assumptions = self.compose_scope_assumptions(&[]);

        // Use the interruptible variant so should_stop is respected even
        // when scope_selectors produce assumptions (#3237).
        let result = match self.solve_with_assumptions_impl(&assumptions, Some(&should_stop), None)
        {
            AssumeResult::Sat(model) => {
                self.sat_from_assume_model(model, "solve_interruptible() scope-selector path")
            }
            AssumeResult::Unsat(_) => SatResult::Unsat,
            AssumeResult::Unknown => SatResult::Unknown,
        };
        self.trace_sat_result(&result);
        self.finish_tla_trace();
        result
    }

    /// Initialize solver state for a new solve call.
    ///
    /// Resets search state, sets up watches, processes initial unit clauses,
    /// and runs initial propagation. Returns `Some(result)` if the formula
    /// is trivially solved during initialization (empty formula, unit
    /// propagation conflict), `None` if the CDCL loop should proceed.
    fn init_solve(&mut self) -> Option<SatResult> {
        // Record wall-clock start time for progress reporting.
        if self.cold.progress_enabled {
            self.cold.solve_start_time = Some(std::time::Instant::now());
            self.cold.last_progress_time = None;
        }

        // On second+ solve, disable destructive inprocessing (#5031).
        if self.cold.has_solved_once {
            self.disable_destructive_inprocessing();
        }
        self.cold.has_solved_once = true;
        self.reset_search_state();
        // CaDiCaL: init_solve must start at decision level 0
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: init_solve entered at decision level {}",
            self.decision_level,
        );

        tracing::info!(
            num_vars = self.num_vars,
            num_clauses = self.arena.num_clauses(),
            proof_mode = self.proof_manager.is_some(),
            diagnostic_mode = self.cold.diagnostic_trace.is_some(),
            "solve: start"
        );

        self.tla_trace_step("PROPAGATING", None);

        if self.arena.is_empty() {
            self.tla_trace_step("SAT", Some("DeclareSat"));
            return Some(self.declare_sat_from_current_assignment());
        }

        self.num_original_clauses = self.arena.num_clauses();
        self.cold.original_clause_boundary = self.arena.len();
        self.initialize_watches();

        if let Some(conflict_ref) = self.process_initial_clauses() {
            // Contradictory unit clauses — collect LRAT resolution chain
            // from the conflict clause so the empty-clause step has proper hints.
            self.record_level0_conflict_chain(conflict_ref);
            return Some(self.declare_unsat());
        }

        let trail_before = self.trail.len();
        // Init-solve: no probing/vivify mode yet — use search variant.
        if let Some(conflict_ref) = self.search_propagate() {
            // Record the BCP resolution chain for proof reconstruction (#4176).
            // Standard analyze_conflict uses 1UIP which assumes decision_level > 0.
            // At level 0, use a dedicated chain recorder that just collects the
            // clause IDs involved in the BCP conflict.
            self.record_level0_conflict_chain(conflict_ref);
            return Some(self.declare_unsat());
        }
        if self.cold.tla_trace.is_some() && self.trail.len() > trail_before {
            self.tla_trace_step("PROPAGATING", Some("Propagate"));
        }

        None
    }

    pub(super) fn solve_no_assumptions<F>(&mut self, should_stop: F) -> SatResult
    where
        F: Fn() -> bool,
    {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;
        self.cold.finalize_sat_fail_count = 0;

        if let Some(result) = self.init_solve() {
            return result;
        }

        // Run initial preprocessing (BVE, probing, subsumption)
        // This can eliminate variables and simplify clauses before CDCL
        if self.cold.preprocess_enabled {
            let t0 = std::time::Instant::now();
            let unsat = self.preprocess();
            self.stats.preprocess_time_ns = t0.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
            if unsat {
                return self.declare_unsat();
            }
        }

        // Reinitialize watches after preprocessing (clauses may have been modified)
        // Must clear watches first to avoid duplicates from pre-preprocessing state.
        //
        // Optimization: when BVE ran and rebuilt watches as its last step, and no
        // subsequent pass modified clause literals in-place (e.g., quick-mode on
        // large instances), skip the redundant O(clauses) watch rebuild. On
        // shuffling-2 (4.7M clauses), this saves ~6 seconds of double watch init.
        if self.cold.preprocess_enabled {
            if !self.cold.preprocess_watches_valid {
                self.watches.clear();
                self.initialize_watches();
            }
            // Reset qhead so all level-0 assignments re-propagate through
            // current watches (#1818). Needed even when watches are valid
            // because backbone/BVE may have enqueued new units.
            self.qhead = 0;
            #[cfg(feature = "jit")]
            {
                self.jit_qhead = 0;
            }

            // Re-propagate after watch reinitialization (#1464)
            // BVE may have added resolvents that are unit/conflict under current assignment.
            // Without this propagation, the solver may miss conflicts or unit implications.
            {
                let trail_before = self.trail.len();
                // Post-preprocess: no probing/vivify — search variant.
                if let Some(conflict_ref) = self.search_propagate() {
                    self.record_level0_conflict_chain(conflict_ref);
                    return self.declare_unsat();
                }
                if self.cold.tla_trace.is_some() && self.trail.len() > trail_before {
                    self.tla_trace_step("PROPAGATING", Some("Propagate"));
                }
            }

            // Disable for subsequent calls — prevents double preprocessing if a
            // later call goes through solve_with_assumptions_impl().
            self.cold.preprocess_enabled = false;

            // Use the post-preprocessing irredundant count for scheduling.
            // arena.num_clauses() counts deleted slots left behind by BVE and
            // subsumption, which overstates the live problem size.
            self.num_original_clauses = self.arena.active_clause_count();
        }

        // JIT-compile static clauses into native propagation functions.
        // This happens once, after preprocessing, before the search loop.
        #[cfg(feature = "jit")]
        {
            match self.compile_static_clauses() {
                Ok(n) if n > 0 => {
                    tracing::info!("JIT: compiled {n} static clauses");

                    // After successful JIT compilation, remove 2WL watchers for
                    // compiled clauses. This prevents double-processing: JIT
                    // handles len 3-5 clauses, 2WL handles the rest.
                    //
                    // Only detach when budget was NOT exhausted. When exhausted,
                    // some compiled clause var-polarity pairs were skipped and
                    // still need 2WL — we can't cheaply determine which ones.
                    if self.has_compiled_formula()
                        && !self
                            .compiled_formula
                            .as_ref()
                            .is_some_and(|cf| cf.budget_exhausted())
                    {
                        let removed = self.watches.detach_irredundant_watches(|offset| {
                            // Keep learned clauses (not compiled by JIT)
                            if self.arena.is_learned(offset) {
                                return true;
                            }
                            // Keep clauses outside compiled range (binary + long)
                            let len = self.arena.len_of(offset);
                            len < 3 || len > 5
                        });
                        tracing::info!(removed, "JIT: detached compiled (len 3-5) watchers");
                    }
                }
                Ok(_) => {}
                Err(e) => {
                    tracing::warn!("JIT compilation failed, falling back to 2WL: {e}");
                }
            }
        }

        // CaDiCaL internal.cpp:487-489: init_search_limits.
        // Set the initial inprobe conflict limit proportional to formula size.
        // delta = log10(irredundant + 10)^2; lim.inprobe = conflicts + inprobeint * delta.
        // For shuffling-2 (4.9M clauses): delta=44.7, limit=4470 conflicts.
        // Without this, next_inprobe_conflict=0 causes inprocessing to fire at
        // conflict 1 on large post-BVE formulas, wasting time on passes that
        // CaDiCaL defers until the search has made progress (#6926).
        {
            let irredundant = self.num_original_clauses as f64;
            let delta = (irredundant + 10.0).log10();
            let delta = delta * delta;
            let limit = (INPROBE_INTERVAL as f64 * delta) as u64;
            self.cold.next_inprobe_conflict = self.num_conflicts.saturating_add(limit);
        }

        // Try lucky phases (CaDiCaL-style pre-solving)
        // This can quickly solve formulas with simple satisfying assignments
        {
            let t0 = std::time::Instant::now();
            let lucky_result = self.try_lucky_phases();
            self.stats.lucky_time_ns = t0.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
            if let Some(sat) = lucky_result {
                if sat {
                    // Lucky phase found satisfying assignment
                    self.tla_trace_step("SAT", Some("DeclareSat"));
                    return self.declare_sat_from_current_assignment();
                }
                // UNSAT proven at level 0 during lucky phase
                return self.declare_unsat();
            }
        }
        if self.is_interrupted() {
            return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
        }

        // Run warmup to initialize target phases before walk
        // Warmup uses propagation-based phase setting which is O(1) per propagation
        self.try_warmup();

        // Try walk-based phase initialization for larger formulas
        // Walk uses ProbSAT to find good initial phases by minimizing unsatisfied clauses
        let walk_start = std::time::Instant::now();
        let walk_found = self.try_walk();
        self.stats.walk_time_ns = walk_start.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
        if walk_found {
            // Walk found an assignment satisfying (some subset of) clauses.
            // Before returning SAT, verify the candidate model against *all* clauses
            // (including any learned clauses added during preprocessing) and
            // against reconstruction obligations from equisatisfiable transforms.
            //
            // `walk` is a heuristic; without this check, it can return a model that
            // does not satisfy the full clause database, which is an unsound SAT result.
            let candidate = self.get_model_from_phases();
            let mut reconstructed = candidate.clone();
            let reconstruction_ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                self.inproc.reconstruction.reconstruct(&mut reconstructed);
            }))
            .is_ok();
            if reconstruction_ok && self.verify_model(&reconstructed) {
                self.tla_trace_step("SAT", Some("DeclareSat"));
                return self.declare_sat_from_model(candidate);
            }
            if !reconstruction_ok {
                tracing::warn!("walk candidate reconstruction panicked");
            }
        }

        // Jeroslow-Wang initial phases: for any variable without a saved phase
        // (from walk/warmup), set phase to the polarity with higher JW score.
        // JW(l) = sum_{c containing l} 2^{-|c|}. Higher score means the literal
        // appears in more/shorter clauses, so assigning it true satisfies more
        // constraints. CaDiCaL computes this in phases.cpp for initial_phase=2.
        // Cost: O(total_literals), negligible even on 4M-clause formulas (~10ms).
        self.init_jw_phases();

        let mut callback = NullCallback;
        let t0 = std::time::Instant::now();
        let result = self.cdcl_loop(&mut callback, should_stop);
        self.stats.search_time_ns = t0.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
        result
    }
}

// Finalize section (declare_*, finalize_*, proof_writer, handle_ext_conflict)
// moved to finalize.rs (#4933).
