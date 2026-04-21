// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Assumption-based solving with unsat core extraction.

use super::*;

impl Solver {
    /// Solve the formula with assumptions
    ///
    /// This performs assumption-based solving, where the given literals are
    /// treated as temporary unit clauses for this solve call only. The solver
    /// state (learned clauses, etc.) is preserved between calls.
    ///
    /// Returns:
    /// - `AssumeResult::Sat(model)` if satisfiable with the assumptions
    /// - `AssumeResult::Unsat(core)` if unsatisfiable, where `core` is a subset
    ///   of the assumptions that caused the conflict
    /// - `AssumeResult::Unknown` if the solver could not determine satisfiability
    ///
    /// The unsat core extraction follows the MiniSat approach: assumptions are
    /// assigned at decision levels 1, 2, ..., n. When a conflict occurs that
    /// requires backtracking past all assumptions (to level 0), the assumptions
    /// involved in the conflict analysis form the unsat core.
    pub fn solve_with_assumptions(&mut self, assumptions: &[Literal]) -> VerifiedAssumeResult {
        VerifiedAssumeResult::from_validated(self.solve_with_assumptions_raw(assumptions))
    }

    /// Internal assumption solve returning raw `AssumeResult`.
    fn solve_with_assumptions_raw(&mut self, assumptions: &[Literal]) -> AssumeResult {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;
        let combined = self.compose_scope_assumptions(assumptions);
        self.emit_diagnostic_assumption_batch(&combined, !self.cold.scope_selectors.is_empty());

        if self.has_empty_clause {
            let result = self.declare_unsat_assume(vec![]);
            self.emit_diagnostic_assumption_result(&result);
            self.trace_result(SolveOutcome::Unsat);
            self.finish_tla_trace();
            return result;
        }

        let result = if combined.is_empty() {
            match self.solve_no_assumptions(|| false) {
                SatResult::Sat(model) => self.assume_sat_from_assume_model(
                    model,
                    "solve_with_assumptions() empty-assumption fast path",
                ),
                SatResult::Unsat => AssumeResult::Unsat(vec![]),
                SatResult::Unknown => AssumeResult::Unknown,
            }
        } else {
            self.solve_with_assumptions_impl(&combined, None::<&fn() -> bool>, None)
        };

        let final_result = self.finalize_assumption_api_result(result);
        self.emit_diagnostic_assumption_result(&final_result);
        match final_result {
            AssumeResult::Sat(_) => self.trace_result(SolveOutcome::Sat),
            AssumeResult::Unsat(_) => self.trace_result(SolveOutcome::Unsat),
            AssumeResult::Unknown => self.trace_result(SolveOutcome::Unknown),
        }
        self.finish_tla_trace();
        final_result
    }

    /// Solve with assumptions and an interrupt callback.
    ///
    /// The callback is checked periodically (every ~100 conflicts). If it returns
    /// `true`, solving is interrupted and `AssumeResult::Unknown` is returned.
    ///
    /// This is useful for timeout enforcement and parallel solving.
    pub fn solve_with_assumptions_interruptible<F>(
        &mut self,
        assumptions: &[Literal],
        should_stop: F,
    ) -> VerifiedAssumeResult
    where
        F: Fn() -> bool,
    {
        VerifiedAssumeResult::from_validated(
            self.solve_with_assumptions_interruptible_raw(assumptions, should_stop),
        )
    }

    /// Internal interruptible assumption solve returning raw `AssumeResult`.
    fn solve_with_assumptions_interruptible_raw<F>(
        &mut self,
        assumptions: &[Literal],
        should_stop: F,
    ) -> AssumeResult
    where
        F: Fn() -> bool,
    {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;
        let combined = self.compose_scope_assumptions(assumptions);
        self.emit_diagnostic_assumption_batch(&combined, !self.cold.scope_selectors.is_empty());

        if self.has_empty_clause {
            let result = self.declare_unsat_assume(vec![]);
            self.emit_diagnostic_assumption_result(&result);
            self.trace_result(SolveOutcome::Unsat);
            self.finish_tla_trace();
            return result;
        }

        let result = if combined.is_empty() {
            match self.solve_no_assumptions(&should_stop) {
                SatResult::Sat(model) => self.assume_sat_from_assume_model(
                    model,
                    "solve_with_assumptions_interruptible() empty-assumption fast path",
                ),
                SatResult::Unsat => AssumeResult::Unsat(vec![]),
                SatResult::Unknown => AssumeResult::Unknown,
            }
        } else {
            self.solve_with_assumptions_impl(&combined, Some(&should_stop), None)
        };

        let final_result = self.finalize_assumption_api_result(result);
        self.emit_diagnostic_assumption_result(&final_result);
        match final_result {
            AssumeResult::Sat(_) => self.trace_result(SolveOutcome::Sat),
            AssumeResult::Unsat(_) => self.trace_result(SolveOutcome::Unsat),
            AssumeResult::Unknown => self.trace_result(SolveOutcome::Unknown),
        }
        self.finish_tla_trace();
        final_result
    }

    /// Unified assumption-based CDCL loop.
    ///
    /// When `should_stop` is `Some`, the callback is checked every 100 conflicts
    /// and every 1000 decisions to support interruptible solving. When `None`,
    /// the solver runs to completion.
    pub(super) fn solve_with_assumptions_impl<F>(
        &mut self,
        assumptions: &[Literal],
        should_stop: Option<&F>,
        mut theory_check: Option<&mut dyn FnMut(&mut Self) -> TheoryPropResult>,
    ) -> AssumeResult
    where
        F: Fn() -> bool,
    {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;

        // On second+ solve, disable destructive inprocessing (#5031).
        if self.cold.has_solved_once {
            self.disable_destructive_inprocessing();
        }
        self.cold.has_solved_once = true;

        // Reset search state but preserve learned clauses
        self.reset_search_state();
        // MiniSat assumption-based solving invariant: search must start at
        // level 0. Assumptions are assigned at levels 1..=n.
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: assumption solve starts at decision_level {} (expected 0)",
            self.decision_level,
        );

        // Handle empty formula
        if self.arena.is_empty() {
            // Even when there are no clauses, assumptions still constrain the model.
            // Satisfiable unless assumptions contain an immediate contradiction.
            let mut model = self.get_model();
            let mut first_lit_for_var: Vec<Option<Literal>> = vec![None; self.num_vars];

            for &lit in assumptions {
                let var_idx = lit.variable().index();
                if var_idx >= self.num_vars {
                    continue;
                }
                let desired = lit.is_positive();

                if let Some(prev) = first_lit_for_var[var_idx] {
                    if prev.is_positive() != desired {
                        return AssumeResult::Unsat(vec![prev, lit]);
                    }
                } else {
                    first_lit_for_var[var_idx] = Some(lit);
                    model[var_idx] = desired;
                    // #5571: Write to vals[] so finalize_sat_model (which rebuilds
                    // the external model from vals via e2i) sees assumption values.
                    // Without this, the empty-formula fast path sets model[] but
                    // finalize_sat_model ignores the passed-in model and reads vals[],
                    // producing a model where assumptions evaluate to false.
                    z4_prefetch::val_set(&mut self.vals, lit.index(), 1);
                    z4_prefetch::val_set(&mut self.vals, lit.negated().index(), -1);
                }
            }

            return self.declare_assume_sat_from_model(model);
        }

        // Track number of original clauses
        self.num_original_clauses = self.arena.num_clauses();
        self.cold.original_clause_boundary = self.arena.len();

        // Initialize watches
        self.initialize_watches();

        // CaDiCaL assume.cpp:83-85: state must be clean before initial processing
        debug_assert!(
            self.trail.is_empty(),
            "BUG: trail not empty ({} entries) after reset_search_state",
            self.trail.len(),
        );

        // Process initial unit clauses
        if let Some(conflict_ref) = self.process_initial_clauses() {
            self.record_level0_conflict_chain(conflict_ref);
            return self.declare_unsat_assume(vec![]);
        }

        // Run initial preprocessing (subsumption, probing, decompose, congruence, HTR).
        // DPLL(T) always uses assumptions, so without this, SMT/CHC solving never gets
        // preprocessing. BVE is already disabled for DPLL(T) (default_enabled=false).
        // Only run on first solve; subsequent calls (with new theory lemmas) skip.
        if self.cold.preprocess_enabled && !self.cold.has_been_incremental {
            // Freeze assumption variables so preprocessing won't eliminate them.
            // In DPLL(T), theory variables are already frozen (saturating_add is safe).
            // For direct solve_with_assumptions() callers, this prevents decompose,
            // congruence, sweep, etc. from substituting/removing assumption vars.
            for &lit in assumptions {
                let var = lit.variable();
                if var.index() < self.num_vars {
                    self.freeze(var);
                }
            }

            let preprocess_unsat = self.preprocess();

            // Melt assumption variables — the freeze was only needed during
            // preprocessing to prevent elimination. Melting restores the solver's
            // full inprocessing power for subsequent solve_with_assumptions() calls
            // where these variables may no longer be assumptions.
            // For DPLL(T), theory variables remain frozen (their own freeze_count
            // was incremented separately); our melt only reverses our increment.
            for &lit in assumptions {
                let var = lit.variable();
                if var.index() < self.num_vars {
                    self.melt(var);
                }
            }

            if preprocess_unsat {
                return self.declare_unsat_assume(vec![]);
            }

            // Reinitialize watches after preprocessing (clauses may have been modified)
            self.watches.clear();
            self.initialize_watches();
            self.qhead = 0;
            #[cfg(feature = "jit")]
            {
                self.jit_qhead = 0;
            }

            if let Some(conflict_ref) = self.search_propagate() {
                self.record_level0_conflict_chain(conflict_ref);
                return self.declare_unsat_assume(vec![]);
            }

            // Match solve_no_assumptions: scheduling should use the live
            // irredundant clause count after preprocessing shrink, not the
            // monotonic arena slot count captured before BVE/subsumption.
            self.num_original_clauses = self.arena.active_clause_count();

            // JIT-compile static clauses for assumption-based solving.
            // Mirrors solve_no_assumptions in solve/mod.rs.
            #[cfg(feature = "jit")]
            {
                match self.compile_static_clauses() {
                    Ok(n) if n > 0 => {
                        tracing::info!("JIT (assumptions): compiled {n} static clauses");
                        if self.has_compiled_formula()
                            && !self
                                .compiled_formula
                                .as_ref()
                                .is_some_and(|cf| cf.budget_exhausted())
                        {
                            let removed =
                                self.watches.detach_irredundant_watches(|offset| {
                                    if self.arena.is_learned(offset) {
                                        return true;
                                    }
                                    let len = self.arena.len_of(offset);
                                    len < 3 || len > 5
                                });
                            tracing::info!(removed, "JIT (assumptions): detached compiled (len 3-5) watchers");
                        }
                    }
                    Ok(_) => {}
                    Err(e) => {
                        tracing::warn!("JIT compilation failed in assumptions path: {e}");
                    }
                }
            }

            // Disable preprocessing for subsequent solve calls — DPLL(T) re-solves
            // with new theory lemmas; preprocessing should only run once.
            self.cold.preprocess_enabled = false;
        }

        // Track which variables are assumptions and which assumptions are "failed"
        let mut is_assumption = vec![false; self.num_vars];
        let mut assumption_lit = vec![None; self.num_vars];
        let mut failed_assumptions: Vec<Literal> = Vec::new();
        let mut is_failed: Vec<bool> = vec![false; self.num_vars];

        for &lit in assumptions {
            let var_idx = lit.variable().index();
            if var_idx < self.num_vars {
                is_assumption[var_idx] = true;
                assumption_lit[var_idx] = Some(lit);
            }
        }

        // Current assumption index we're trying to set
        let mut assumption_idx = 0;

        // Main CDCL loop with assumptions
        loop {
            // Parity with solve_no_assumptions in solve/mod.rs:322 —
            // honor external interrupt handle and process memory limit (#6552).
            if self.is_interrupted() {
                return self.declare_assume_unknown_with_reason(SatUnknownReason::Interrupted);
            }

            // Inprocessing/theory lemmas can discover UNSAT at decision level 0
            // by deriving an empty clause. Normal BCP does not see this (empty
            // clauses are tracked via `has_empty_clause`), so check it here.
            // Parity with solve_no_assumptions and
            // solve_no_assumptions_with_theory_backend in solve/mod.rs.
            if self.has_empty_clause {
                return self.declare_unsat_assume(failed_assumptions);
            }

            // Propagate — search-specialized BCP (no probe/vivify overhead).
            if let Some(conflict_ref) = self.search_propagate() {
                // Conflict found
                if self.decision_level == 0 {
                    self.record_level0_conflict_chain(conflict_ref);
                    return self.declare_unsat_assume(failed_assumptions);
                }

                self.conflicts_since_restart += 1;
                self.num_conflicts += 1;
                self.on_conflict_random_decision();

                // Check for interrupt every 100 conflicts
                if let Some(stop) = should_stop {
                    if self.num_conflicts.is_multiple_of(100) && stop() {
                        return self
                            .declare_assume_unknown_with_reason(SatUnknownReason::Interrupted);
                    }
                }

                // Wave 3 (#4791): use shared conflict-analysis skeleton instead
                // of inline duplicate. The before_backtrack hook updates
                // assumption_idx; the on_learned hook extracts the failed
                // assumption core from the learned clause while var levels
                // are still valid (pre-backtrack).
                let num_assumptions = assumptions.len() as u32;
                self.analyze_and_backtrack_with_core_hook(
                    conflict_ref,
                    "assumption loop",
                    |_solver, bt_level| {
                        if bt_level < num_assumptions {
                            assumption_idx = bt_level as usize;
                        }
                    },
                    |solver, learned_clause, _actual_bt_level| {
                        for &lit in learned_clause {
                            let var_idx = lit.variable().index();
                            let var_level = solver.var_data[var_idx].level;
                            if var_level > 0
                                && var_level <= num_assumptions
                                && is_assumption[var_idx]
                            {
                                if let Some(assump_lit) = assumption_lit[var_idx] {
                                    if !is_failed[var_idx] {
                                        is_failed[var_idx] = true;
                                        failed_assumptions.push(assump_lit);
                                    }
                                }
                            }
                        }
                    },
                );
            } else {
                // No conflict

                // First, try to set any remaining assumptions
                if assumption_idx < assumptions.len() {
                    // CaDiCaL decide.cpp:575: decision level must match assumption index
                    debug_assert!(
                        (self.decision_level as usize) <= assumption_idx,
                        "BUG: decision_level {} > assumption_idx {assumption_idx} \
                         — assumptions should advance monotonically",
                        self.decision_level,
                    );
                    let assump_lit = assumptions[assumption_idx];
                    let var = assump_lit.variable();
                    let var_idx = var.index();
                    // CaDiCaL assume.cpp:30: assumption literal must be valid (non-zero index)
                    debug_assert!(
                        var_idx < self.num_vars,
                        "BUG: assumption literal {assump_lit:?} refers to var {var_idx} >= num_vars {}",
                        self.num_vars,
                    );

                    // Check if this assumption is already assigned
                    if let Some(val) = self.var_value_from_vals(var_idx) {
                        let expected = assump_lit.is_positive();
                        if val != expected {
                            // Conflict with assumption - this assumption is failed
                            if !is_failed[var_idx] {
                                is_failed[var_idx] = true;
                                failed_assumptions.push(assump_lit);
                            }
                            // Also collect any other failed assumptions from the conflict
                            if let Some(reason_ref) = self.var_reason(var_idx) {
                                // CaDiCaL assume.cpp:133: every literal in reason must be assigned
                                for &lit in self.arena.literals(reason_ref.0 as usize) {
                                    debug_assert!(
                                        self.lit_val(lit) != 0,
                                        "BUG: reason literal {lit:?} for assumption conflict is unassigned",
                                    );
                                    let reason_var_idx = lit.variable().index();
                                    if is_assumption[reason_var_idx] {
                                        if let Some(a_lit) = assumption_lit[reason_var_idx] {
                                            if !is_failed[reason_var_idx] {
                                                is_failed[reason_var_idx] = true;
                                                failed_assumptions.push(a_lit);
                                            }
                                        }
                                    }
                                }
                            }
                            return self.declare_unsat_assume(failed_assumptions);
                        }
                        // Already assigned to correct value, move to next assumption
                        assumption_idx += 1;
                        continue;
                    }

                    // Make the assumption as a decision.
                    // The assumption level must match: decision_level (before
                    // decide increments it) should equal assumption_idx since
                    // each assumption gets its own level starting from 1.
                    debug_assert!(
                        self.decision_level as usize <= assumption_idx,
                        "BUG: assumption decide at decision_level {} but assumption_idx is {assumption_idx}",
                        self.decision_level,
                    );
                    assumption_idx += 1;
                    self.decide(assump_lit);
                    continue;
                }

                // All assumptions set — invoke theory callback before deciding (#3343)
                if let Some(ref mut tc) = theory_check {
                    match tc(self) {
                        TheoryPropResult::Continue => {}
                        TheoryPropResult::Propagate => {
                            continue;
                        }
                        TheoryPropResult::Conflict(clause) => {
                            // Must use add_theory_lemma (not add_clause) to
                            // set up watches for mid-solve BCP participation.
                            if clause.is_empty() {
                                return self.declare_unsat_assume(failed_assumptions);
                            }
                            self.add_theory_lemma(clause);
                            continue;
                        }
                        TheoryPropResult::Stop => {
                            return self
                                .declare_assume_unknown_with_reason(SatUnknownReason::TheoryStop);
                        }
                    }
                }

                // All assumptions set, continue with regular solving
                if self.should_restart() {
                    // For assumption-based solving, only restart back to assumption level
                    // Don't run inprocessing during assumption solving to preserve state
                    self.do_partial_restart(assumptions.len() as u32);
                    // Check if we should rephase (change phase selection strategy)
                    if self.should_rephase() {
                        self.rephase();
                    }
                } else if let Some(var) = self.pick_next_decision_variable() {
                    let lit = self.pick_phase(var);
                    self.decide(lit);

                    // Keep interrupt semantics consistent with solve_no_assumptions:
                    // SAT-leaning runs can make many decisions with no conflicts.
                    // Parity with solve/mod.rs:363 — check is_interrupted() in
                    // decision branch for memory limit and external handle (#6552).
                    if self.is_interrupted() {
                        return self
                            .declare_assume_unknown_with_reason(SatUnknownReason::Interrupted);
                    }
                    if let Some(stop) = should_stop {
                        if self.num_decisions.is_multiple_of(1000) && stop() {
                            return self
                                .declare_assume_unknown_with_reason(SatUnknownReason::Interrupted);
                        }
                    }
                } else {
                    // All variables assigned -> SAT
                    return self.declare_assume_sat_from_current_assignment();
                }
            }
        }
    }

    /// Partial restart - only restart back to a given level (for assumption-based solving)
    pub(super) fn do_partial_restart(&mut self, min_level: u32) {
        if self.decision_level <= min_level {
            return;
        }
        // Partial restart must not undo assumption assignments
        debug_assert!(
            min_level > 0,
            "BUG: partial restart to level 0 would undo assumptions",
        );
        // Decision level must be above min_level (checked above, but assert for clarity)
        debug_assert!(
            self.decision_level > min_level,
            "BUG: partial restart from level {} to min_level {min_level} — already at or below",
            self.decision_level,
        );

        // Backtrack to just above the minimum level
        self.backtrack(min_level);
        // Post-condition: decision level must be exactly min_level after backtrack
        debug_assert_eq!(
            self.decision_level, min_level,
            "BUG: after partial restart backtrack, decision_level {} != min_level {min_level}",
            self.decision_level,
        );
        self.conflicts_since_restart = 0;
        self.cold.restarts += 1;

        // Update Luby sequence
        self.cold.luby_idx += 1;
        self.complete_branch_heuristic_epoch_if_needed();
    }

    #[inline]
    pub(super) fn compose_scope_assumptions(&self, assumptions: &[Literal]) -> Vec<Literal> {
        let mut combined = Vec::with_capacity(self.cold.scope_selectors.len() + assumptions.len());
        combined.extend(
            self.cold
                .scope_selectors
                .iter()
                .copied()
                .map(Literal::negative),
        );
        combined.extend_from_slice(assumptions);
        combined
    }
}

#[cfg(test)]
#[path = "assumptions_tests.rs"]
mod tests;
