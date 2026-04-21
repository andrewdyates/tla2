// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extension-mode entry points and initialization for DPLL(T) solving.

use super::super::*;
use super::theory_callback::ExtensionCallback;

impl Solver {
    /// Solve with an extension extracted from the SAT clause database during the
    /// initial preprocess stage.
    ///
    /// The builder sees a snapshot of the current active irredundant clauses,
    /// may consume some of them into an extension, and may freeze variables
    /// before SAT preprocessing continues. The extension then joins the normal
    /// extension propagation loop for BCP/CDCL.
    pub fn solve_with_preprocessing_extension<E, B>(
        &mut self,
        build_extension: B,
    ) -> VerifiedSatResult
    where
        E: Extension,
        B: FnMut(&[Vec<Literal>]) -> Option<PreparedExtension<E>>,
    {
        VerifiedSatResult::from_validated(
            self.solve_with_preprocessing_extension_raw(build_extension),
        )
    }

    /// Interruptible variant of `solve_with_preprocessing_extension`.
    pub fn solve_interruptible_with_preprocessing_extension<E, B, F>(
        &mut self,
        build_extension: B,
        should_stop: F,
    ) -> VerifiedSatResult
    where
        E: Extension,
        B: FnMut(&[Vec<Literal>]) -> Option<PreparedExtension<E>>,
        F: Fn() -> bool,
    {
        VerifiedSatResult::from_validated(
            self.solve_interruptible_with_preprocessing_extension_raw(build_extension, should_stop),
        )
    }

    /// Solve with a theory extension for eager DPLL(T) integration
    ///
    /// The extension is called after each propagation phase to check for
    /// theory propagations. If the extension returns clauses, they are added
    /// to SAT and propagation continues. If the extension returns a conflict,
    /// SAT handles it like any other conflict.
    ///
    /// This is the recommended way to integrate theory solvers for eager
    /// DPLL(T) where theory propagation happens during SAT search.
    pub fn solve_with_extension(&mut self, ext: &mut dyn Extension) -> VerifiedSatResult {
        VerifiedSatResult::from_validated(self.solve_with_extension_raw(ext))
    }

    /// Solve with a theory extension AND an interrupt callback (#6296).
    ///
    /// Combines `solve_with_extension` (theory phase hints, propagation) with
    /// `solve_interruptible` (timeout/interrupt support). The `should_stop`
    /// closure is polled every 100 conflicts and every 1000 decisions.
    pub fn solve_interruptible_with_extension<F>(
        &mut self,
        ext: &mut dyn Extension,
        should_stop: F,
    ) -> VerifiedSatResult
    where
        F: Fn() -> bool,
    {
        VerifiedSatResult::from_validated(
            self.solve_interruptible_with_extension_raw(ext, should_stop),
        )
    }

    /// Internal interruptible extension solve returning raw `SatResult`.
    fn solve_interruptible_with_extension_raw<F>(
        &mut self,
        ext: &mut dyn Extension,
        should_stop: F,
    ) -> SatResult
    where
        F: Fn() -> bool,
    {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;

        if self.has_empty_clause {
            let result = self.declare_unsat();
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        if self.cold.scope_selectors.is_empty() {
            let result = self.solve_no_assumptions_with_extension_interruptible(ext, should_stop);
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        debug_assert!(
            self.cold.scope_selectors.is_empty(),
            "solve_interruptible_with_extension() with non-empty scope_selectors is not supported"
        );
        self.trace_sat_result(&SatResult::Unknown);
        self.finish_tla_trace();
        self.declare_unknown_with_reason(SatUnknownReason::UnsupportedConfig)
    }

    fn solve_interruptible_with_preprocessing_extension_raw<E, B, F>(
        &mut self,
        build_extension: B,
        should_stop: F,
    ) -> SatResult
    where
        E: Extension,
        B: FnMut(&[Vec<Literal>]) -> Option<PreparedExtension<E>>,
        F: Fn() -> bool,
    {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;

        if self.has_empty_clause {
            let result = self.declare_unsat();
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        if self.cold.scope_selectors.is_empty() {
            let result = self
                .solve_no_assumptions_with_preprocessing_extension(build_extension, should_stop);
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        debug_assert!(
            self.cold.scope_selectors.is_empty(),
            "solve_interruptible_with_preprocessing_extension() with non-empty \
             scope_selectors is not supported"
        );
        self.trace_sat_result(&SatResult::Unknown);
        self.finish_tla_trace();
        self.declare_unknown_with_reason(SatUnknownReason::UnsupportedConfig)
    }

    /// Internal extension solve returning raw `SatResult`.
    fn solve_with_extension_raw(&mut self, ext: &mut dyn Extension) -> SatResult {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;

        if self.has_empty_clause {
            let result = self.declare_unsat();
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        if self.cold.scope_selectors.is_empty() {
            let result = self.solve_no_assumptions_with_extension(ext);
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        // Extension callbacks require lifecycle management (init, backtrack, check)
        // that the assumption-based loop does not yet support.
        // In debug builds, keep the invariant loud; in release, fail closed.
        debug_assert!(
            self.cold.scope_selectors.is_empty(),
            "solve_with_extension() with non-empty scope_selectors is not supported: \
             Extension callbacks would be silently skipped. Use solve_with_theory() \
             for scoped theory integration, or pop all scopes before calling \
             solve_with_extension()."
        );
        self.trace_sat_result(&SatResult::Unknown);
        self.finish_tla_trace();
        self.declare_unknown_with_reason(SatUnknownReason::UnsupportedConfig)
    }

    fn solve_with_preprocessing_extension_raw<E, B>(&mut self, build_extension: B) -> SatResult
    where
        E: Extension,
        B: FnMut(&[Vec<Literal>]) -> Option<PreparedExtension<E>>,
    {
        self.solve_interruptible_with_preprocessing_extension_raw(build_extension, || false)
    }

    pub(super) fn solve_no_assumptions_with_extension(
        &mut self,
        ext: &mut dyn Extension,
    ) -> SatResult {
        let mut callback = ExtensionCallback { ext };
        self.solve_no_assumptions_with_theory_backend(&mut callback, || false)
    }

    /// Interruptible extension solve: combines extension callbacks with a
    /// `should_stop` closure for timeout/interrupt support (#6296).
    pub(super) fn solve_no_assumptions_with_extension_interruptible<F>(
        &mut self,
        ext: &mut dyn Extension,
        should_stop: F,
    ) -> SatResult
    where
        F: Fn() -> bool,
    {
        let mut callback = ExtensionCallback { ext };
        self.solve_no_assumptions_with_theory_backend(&mut callback, should_stop)
    }

    pub(super) fn solve_no_assumptions_with_preprocessing_extension<E, B, F>(
        &mut self,
        mut build_extension: B,
        should_stop: F,
    ) -> SatResult
    where
        E: Extension,
        B: FnMut(&[Vec<Literal>]) -> Option<PreparedExtension<E>>,
        F: Fn() -> bool,
    {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;

        if let Some(result) = self.init_solve() {
            return result;
        }

        let extension = if self.cold.has_been_incremental {
            None
        } else {
            self.prepare_preprocessing_extension(&mut build_extension)
        };

        if self.cold.preprocess_enabled && self.preprocess() {
            return self.declare_unsat();
        }

        if self.cold.preprocess_enabled {
            if !self.cold.preprocess_watches_valid {
                self.watches.clear();
                self.initialize_watches();
            }
            self.qhead = 0;
            #[cfg(feature = "jit")]
            {
                self.jit_qhead = 0;
            }

            let trail_before = self.trail.len();
            if let Some(conflict_ref) = self.search_propagate() {
                self.record_level0_conflict_chain(conflict_ref);
                return self.declare_unsat();
            }
            if self.cold.tla_trace.is_some() && self.trail.len() > trail_before {
                self.tla_trace_step("PROPAGATING", Some("Propagate"));
            }

            self.cold.preprocess_enabled = false;
            self.num_original_clauses = self.arena.active_clause_count();
        }

        // JIT-compile static clauses into native propagation functions.
        // This happens once, after preprocessing, before the search loop.
        // Mirrors solve/mod.rs to ensure extension/theory paths get JIT benefit.
        #[cfg(feature = "jit")]
        {
            match self.compile_static_clauses() {
                Ok(n) if n > 0 => {
                    tracing::info!("JIT: compiled {n} static clauses");

                    // After successful JIT compilation, remove 2WL watchers for
                    // compiled clauses. This prevents double-processing: JIT
                    // handles ternary clauses, 2WL handles the rest.
                    //
                    // Only detach when budget was NOT exhausted. When exhausted,
                    // some ternary clause var-polarity pairs were skipped and
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
                            // Keep non-ternary static clauses (not compiled, need 2WL)
                            let len = self.arena.len_of(offset);
                            len != 3
                        });
                        tracing::info!(removed, "JIT: detached ternary watchers");
                    }
                }
                Ok(_) => {}
                Err(e) => {
                    tracing::warn!("JIT compilation failed, falling back to 2WL: {e}");
                }
            }
        }

        if extension.is_none() {
            return self.solve_remaining_no_assumptions(should_stop);
        }

        self.disable_extension_inprocessing();

        {
            let irredundant = self.arena.active_clause_count() as f64;
            let delta = (irredundant + 10.0).log10();
            let delta = delta * delta;
            let limit = (INPROBE_INTERVAL as f64 * delta) as u64;
            self.cold.next_inprobe_conflict = self.num_conflicts.saturating_add(limit);
        }

        let mut extension = extension.expect("checked Some(extension) above");
        extension.extension.init();
        let mut callback = ExtensionCallback {
            ext: &mut extension.extension,
        };
        self.cdcl_loop(&mut callback, should_stop)
    }

    fn prepare_preprocessing_extension<E, B>(
        &mut self,
        build_extension: &mut B,
    ) -> Option<PreparedExtension<E>>
    where
        E: Extension,
        B: FnMut(&[Vec<Literal>]) -> Option<PreparedExtension<E>>,
    {
        let (clauses, clause_offsets) = self.snapshot_irredundant_clauses();
        let prepared = build_extension(&clauses)?;

        for var in &prepared.frozen_variables {
            if var.index() < self.num_vars {
                self.freeze(*var);
            }
        }

        for &position in &prepared.consumed_clause_positions {
            let Some(&clause_idx) = clause_offsets.get(position) else {
                debug_assert!(
                    false,
                    "prepared extension consumed out-of-range clause position {position}"
                );
                continue;
            };
            if self.arena.is_dead(clause_idx) {
                continue;
            }
            self.delete_clause_checked(clause_idx, mutate::ReasonPolicy::ClearLevel0);
        }

        // Mark that theory lemmas from this extension are trusted transforms
        // (derived from consumed original clauses) and should not block LRAT (#7913).
        self.cold.extension_trusted_lemmas = true;

        Some(prepared)
    }

    fn snapshot_irredundant_clauses(&self) -> (Vec<Vec<Literal>>, Vec<usize>) {
        let mut clauses = Vec::new();
        let mut clause_offsets = Vec::new();

        for clause_idx in self.arena.active_indices() {
            if self.arena.is_dead(clause_idx) || self.arena.is_learned(clause_idx) {
                continue;
            }
            clauses.push(self.arena.literals(clause_idx).to_vec());
            clause_offsets.push(clause_idx);
        }

        (clauses, clause_offsets)
    }

    fn solve_remaining_no_assumptions<F>(&mut self, should_stop: F) -> SatResult
    where
        F: Fn() -> bool,
    {
        {
            let irredundant = self.num_original_clauses as f64;
            let delta = (irredundant + 10.0).log10();
            let delta = delta * delta;
            let limit = (INPROBE_INTERVAL as f64 * delta) as u64;
            self.cold.next_inprobe_conflict = self.num_conflicts.saturating_add(limit);
        }

        if let Some(sat) = self.try_lucky_phases() {
            if sat {
                self.tla_trace_step("SAT", Some("DeclareSat"));
                return self.declare_sat_from_current_assignment();
            }
            return self.declare_unsat();
        }
        if self.is_interrupted() {
            return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
        }

        self.try_warmup();

        if self.try_walk() {
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

        let mut callback = super::theory_callback::NullCallback;
        self.cdcl_loop(&mut callback, should_stop)
    }

    /// Extension-specific solve initialization shared by the unified theory loop.
    pub(super) fn init_extension_loop(&mut self, ext: &mut dyn Extension) -> Option<SatResult> {
        // On second+ solve, disable destructive inprocessing (#5031).
        if self.cold.has_solved_once {
            self.disable_destructive_inprocessing();
        }
        self.cold.has_solved_once = true;
        // Allow calling `solve()` multiple times after adding clauses.
        self.reset_search_state();

        // TLA trace: emit initial state (step 0, no action).
        self.tla_trace_step("PROPAGATING", None);

        // Handle empty formula - but still check extension for theory constraints.
        if self.arena.is_empty() {
            if let Some(result) = self.handle_empty_formula_extension_init(ext) {
                return Some(result);
            }
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

        ext.init();

        // Propagate level-0 units before entering the unified loop.
        let trail_before = self.trail.len();
        if let Some(conflict_ref) = self.search_propagate() {
            // Record the BCP resolution chain for proof reconstruction (#6368).
            // Without this, the clause trace has no empty-clause entry with
            // resolution hints, causing SAT proof reconstruction (Phase 1)
            // to fail and fall through to trust-lemma fallback.
            self.record_level0_conflict_chain(conflict_ref);
            return Some(self.declare_unsat());
        }
        if self.cold.tla_trace.is_some() && self.trail.len() > trail_before {
            self.tla_trace_step("PROPAGATING", Some("Propagate"));
        }

        None
    }

    fn handle_empty_formula_extension_init(
        &mut self,
        ext: &mut dyn Extension,
    ) -> Option<SatResult> {
        ext.init();
        let result = ext.propagate(self);
        if let Some(conflict) = result.conflict {
            if conflict.is_empty() {
                // Empty conflict = theory proved UNSAT unconditionally.
                return Some(self.declare_unsat());
            }
            self.add_theory_lemma(conflict);
        }
        for (clause, propagated) in result.propagations {
            self.add_theory_propagation(clause, propagated);
        }
        for clause in result.clauses {
            self.add_theory_lemma(clause);
        }
        if self.has_empty_clause() {
            return Some(self.declare_unsat());
        }
        if result.stop {
            return Some(self.declare_unknown_with_reason(SatUnknownReason::TheoryStop));
        }
        if !self.arena.is_empty() {
            return None;
        }
        match ext.check(self) {
            ExtCheckResult::Sat => {
                self.tla_trace_step("SAT", Some("DeclareSat"));
                Some(self.declare_sat_from_current_assignment())
            }
            ExtCheckResult::Conflict(clause) => {
                if clause.is_empty() {
                    // Empty conflict = theory proved UNSAT unconditionally.
                    return Some(self.declare_unsat());
                }
                self.add_theory_lemma(clause);
                None
            }
            ExtCheckResult::Unknown => {
                Some(self.declare_unknown_with_reason(SatUnknownReason::ExtensionUnknown))
            }
            ExtCheckResult::AddClauses(clauses) => {
                // #6546: add theory lemmas and continue solving.
                for clause in clauses {
                    self.add_theory_lemma(clause);
                }
                None
            }
        }
    }
}
