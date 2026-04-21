// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DPLL(T) solve entry points and incremental scope management.
//!
//! Extracted from `lib.rs` — contains the public `solve`, `solve_with_assumptions`,
//! `push`/`pop`/`reset_theory` methods and their internal helpers.

#[cfg(not(kani))]
use hashbrown::HashMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::{TermId, TheoryLit, TheorySolver};
use z4_sat::{AssumeResult, Literal, SatResult};

use crate::{proof_tracker, DpllError, DpllT};

impl<T: TheorySolver> DpllT<'_, T> {
    /// Pop the internal model-scope `push()` if one is active.
    ///
    /// Called before every return from a solve method and before any public
    /// scope-mutating operation (`push`, `pop`, `reset_theory`) to maintain
    /// the invariant that internal model scopes never leak past API boundaries (#4520).
    pub(crate) fn exit_model_scope_if_active(&mut self) {
        if self.model_scope_active {
            self.theory.pop();
            self.model_scope_active = false;
        }
    }

    /// Communicate SAT model to theory solver
    ///
    /// IMPORTANT: We use the model returned by the SAT solver, not the live assignment.
    /// The model has defaults applied for unassigned variables (via get_model()), whereas
    /// the live assignment may have None values. Using the model ensures the theory solver
    /// sees a complete, consistent assignment.
    ///
    /// Instead of calling `soft_reset()` (which discards all theory state), we use
    /// scope-based `push/pop` to undo only the model-level assertions from the
    /// previous round. This preserves learned theory state (e.g. simplex tableau
    /// structure, cached atom parses) across SAT model iterations (#4520).
    pub(crate) fn sync_theory(&mut self, model: &[bool]) {
        // Pop previous model scope if active, then push a fresh one.
        self.exit_model_scope_if_active();
        self.theory.push();
        self.model_scope_active = true;

        // For each theory atom, tell the theory solver about its value from the model.
        let debug = self.debug_sync;
        for &term in &self.theory_atoms {
            if let Some(var) = self.var_for_term(term) {
                let var_idx = var.index();
                // Use the model value (which already has defaults applied)
                let value = if var_idx < model.len() {
                    model[var_idx]
                } else {
                    // Variable not in model (shouldn't happen, but default to false)
                    false
                };
                if debug {
                    safe_eprintln!(
                        "[SYNC] term {:?} (var {:?}) = {} (from model)",
                        term,
                        var,
                        value
                    );
                }
                self.theory.assert_literal(term, value);
            }
        }
    }

    /// Solve the formula using DPLL(T)
    ///
    /// Note: This basic solve method returns Unknown if the theory requires
    /// splitting (branch-and-bound for LIA). The executor handles splits via
    /// `solve_step()` + `NeedSplit` return variant.
    ///
    /// Remains `pub` (not `pub(crate)`) because integration tests in `tests/`
    /// exercise this method directly. No production callers outside z4-dpll exist;
    /// the Executor layer (via `check_sat()`) is the validated entry point for
    /// external consumers. Part of #5793.
    /// Internal implementation shared by `solve` and `solve_with_proof_tracking`.
    fn solve_impl(
        &mut self,
        tracking: Option<(&mut proof_tracker::ProofTracker, &HashMap<TermId, TermId>)>,
    ) -> Result<SatResult, DpllError> {
        // Clear residual model scope before reset (#4520).
        self.exit_model_scope_if_active();
        self.theory.reset();

        let result = match self.solve_loop(None, tracking)? {
            AssumeResult::Sat(model) => SatResult::Sat(model),
            AssumeResult::Unsat(_) => SatResult::Unsat,
            AssumeResult::Unknown => SatResult::Unknown,
            #[allow(unreachable_patterns)]
            _ => return Err(DpllError::UnexpectedTheoryResult),
        };
        let summary = match &result {
            SatResult::Sat(_) => "sat",
            SatResult::Unsat => "unsat",
            SatResult::Unknown => "unknown",
            #[allow(unreachable_patterns)]
            _ => "unknown",
        };
        self.emit_solve_summary_event(summary);
        self.finish_dpll_tla_trace();
        Ok(result)
    }

    /// Solve using DPLL(T), returning the final result.
    ///
    /// Returns `Unknown` if the theory requires splitting (branch-and-bound for LIA).
    /// The executor handles splits via `solve_step()` + `NeedSplit`.
    #[must_use = "solve results must be checked — ignoring Sat/Unsat loses correctness"]
    pub fn solve(&mut self) -> Result<SatResult, DpllError> {
        self.solve_impl(None)
    }

    /// Solve while recording theory lemmas into a proof tracker.
    ///
    /// Records theory conflict clauses as `TheoryLemma` steps for Alethe export (#328).
    #[cfg(test)]
    pub(crate) fn solve_with_proof_tracking(
        &mut self,
        tracker: &mut proof_tracker::ProofTracker,
        negations: &HashMap<TermId, TermId>,
    ) -> Result<SatResult, DpllError> {
        self.solve_impl(Some((tracker, negations)))
    }

    /// Internal implementation shared by `solve_with_assumptions` and
    /// `solve_with_assumptions_and_proof_tracking`.
    fn solve_with_assumptions_impl(
        &mut self,
        assumptions: &[Literal],
        tracking: Option<(&mut proof_tracker::ProofTracker, &HashMap<TermId, TermId>)>,
    ) -> Result<AssumeResult, DpllError> {
        self.exit_model_scope_if_active();
        self.theory.reset();
        let assumptions = assumptions.to_vec();
        let result = self.solve_loop(Some(&assumptions), tracking)?;
        let summary = match &result {
            AssumeResult::Sat(_) => "sat",
            AssumeResult::Unsat(_) => "unsat",
            AssumeResult::Unknown => "unknown",
            #[allow(unreachable_patterns)]
            _ => "unknown",
        };
        self.emit_solve_summary_event(summary);
        self.finish_dpll_tla_trace();
        Ok(result)
    }

    /// Solve with assumptions using DPLL(T).
    ///
    /// Like `solve()` but activates only clauses whose selectors are in the
    /// positive assumptions. Returns `AssumeResult` with unsat core when UNSAT.
    pub(crate) fn solve_with_assumptions(
        &mut self,
        assumptions: &[Literal],
    ) -> Result<AssumeResult, DpllError> {
        self.solve_with_assumptions_impl(assumptions, None)
    }

    /// Solve with assumptions while tracking proofs.
    ///
    /// Used for `check-sat-assuming` when `:produce-proofs` is enabled.
    pub(crate) fn solve_with_assumptions_and_proof_tracking(
        &mut self,
        assumptions: &[Literal],
        tracker: &mut proof_tracker::ProofTracker,
        negations: &HashMap<TermId, TermId>,
    ) -> Result<AssumeResult, DpllError> {
        self.solve_with_assumptions_impl(assumptions, Some((tracker, negations)))
    }

    /// Solve one step, returning either a final result or a split request.
    ///
    /// This method is used for LIA where splits may be needed. The executor
    /// should call this in a loop, handling splits by calling `apply_split`
    /// and then calling `solve_step` again.
    ///
    /// Remains `pub` (not `pub(crate)`) because integration tests exercise
    /// this directly. No production callers outside z4-dpll. Part of #5793.
    ///
    /// # Example
    /// ```no_run
    /// use z4_core::{SplitRequest, TermId, TheoryPropagation, TheoryResult, TheorySolver};
    /// use z4_dpll::{DpllT, SolveStepResult};
    ///
    /// # #[derive(Clone, Copy)]
    /// # struct DummyTheory;
    /// # impl TheorySolver for DummyTheory {
    /// #     fn assert_literal(&mut self, _literal: TermId, _value: bool) {}
    /// #     fn check(&mut self) -> TheoryResult { TheoryResult::Sat }
    /// #     fn propagate(&mut self) -> Vec<TheoryPropagation> { Vec::new() }
    /// #     fn push(&mut self) {}
    /// #     fn pop(&mut self) {}
    /// #     fn reset(&mut self) {}
    /// # }
    /// # fn create_atoms(_split: &SplitRequest) -> (TermId, TermId) { todo!() }
    ///
    /// let mut dpll = DpllT::new(10, DummyTheory);
    ///
    /// let _result = loop {
    ///     match dpll.solve_step() {
    ///         Ok(SolveStepResult::Done(result)) => break result,
    ///         Ok(SolveStepResult::NeedBoundRefinements(_reqs)) => {
    ///             todo!("bound refinements")
    ///         }
    ///         Ok(SolveStepResult::NeedSplit(split)) => {
    ///             let (le_atom, ge_atom) = create_atoms(&split);
    ///             dpll.apply_split(le_atom, ge_atom);
    ///         }
    ///         Ok(SolveStepResult::NeedDisequalitySplit(_split)) => {
    ///             todo!("disequality splits")
    ///         }
    ///         Ok(SolveStepResult::NeedExpressionSplit(_split)) => {
    ///             todo!("expression splits")
    ///         }
    ///         Err(err) => panic!("solve_step failed: {err}"),
    ///         Ok(_) => todo!("future solve step variant"),
    ///     }
    /// };
    /// ```
    pub(crate) fn theory_clause_to_terms(
        &self,
        clause: &[TheoryLit],
        negations: &HashMap<TermId, TermId>,
    ) -> Option<Vec<TermId>> {
        clause
            .iter()
            .map(|lit| {
                if lit.value {
                    Some(lit.term)
                } else {
                    negations.get(&lit.term).copied()
                }
            })
            .collect()
    }

    /// Reset the theory solver. Call this before starting a new solve session.
    /// Uses soft_reset() to preserve learned state (e.g., HNF cuts in LIA).
    pub fn reset_theory(&mut self) {
        self.exit_model_scope_if_active();
        self.theory.soft_reset();
    }

    // ========================================================================
    // Incremental Solving (Push/Pop)
    // ========================================================================

    /// Push a new assertion scope.
    ///
    /// All clauses added after this push will be removed when `pop()` is called.
    /// This enables incremental solving where you can add temporary constraints,
    /// solve, and then restore the original state.
    ///
    /// # Example
    /// ```no_run
    /// use z4_core::{TermId, TheoryPropagation, TheoryResult, TheorySolver};
    /// use z4_dpll::DpllT;
    /// use z4_sat::Literal;
    ///
    /// # #[derive(Clone, Copy)]
    /// # struct DummyTheory;
    /// # impl TheorySolver for DummyTheory {
    /// #     fn assert_literal(&mut self, _literal: TermId, _value: bool) {}
    /// #     fn check(&mut self) -> TheoryResult { TheoryResult::Sat }
    /// #     fn propagate(&mut self) -> Vec<TheoryPropagation> { Vec::new() }
    /// #     fn push(&mut self) {}
    /// #     fn pop(&mut self) {}
    /// #     fn reset(&mut self) {}
    /// # }
    ///
    /// let mut dpll = DpllT::new(10, DummyTheory);
    /// let base_clause: Vec<Literal> = vec![]; // Permanent
    /// let temp_clause: Vec<Literal> = vec![]; // Will be removed by pop()
    ///
    /// dpll.add_clause(base_clause);
    /// dpll.push();
    /// dpll.add_clause(temp_clause);
    /// let _result = dpll.solve();
    /// dpll.pop(); // temp_clause is now inactive
    /// ```
    ///
    /// # Invariants
    /// - INV-PUSH-1: After push(), scope depth increases by 1
    /// - INV-PUSH-2: SAT solver and theory solver scopes are synchronized
    pub fn push(&mut self) {
        self.exit_model_scope_if_active();
        self.sat.push();
        self.theory.push();
        if let Some(ref diag) = self.diagnostic_trace {
            let level = u32::try_from(self.scope_depth()).unwrap_or(u32::MAX);
            diag.emit_push(level);
        }
    }

    /// Pop the most recent assertion scope.
    ///
    /// Removes all clauses added since the last `push()` and restores the
    /// theory solver state. Returns `false` if there is no active scope to pop.
    ///
    /// # Invariants
    /// - INV-POP-1: After pop(), scope depth decreases by 1 (if > 0)
    /// - INV-POP-2: SAT solver and theory solver scopes remain synchronized
    /// - INV-POP-3: Learned clauses that depend only on base assertions are preserved
    pub fn pop(&mut self) -> bool {
        self.exit_model_scope_if_active();
        let from_level = self.scope_depth();
        if !self.sat.pop() {
            return false;
        }
        self.theory.pop();
        if let Some(ref diag) = self.diagnostic_trace {
            let from_level = u32::try_from(from_level).unwrap_or(u32::MAX);
            let to_level = u32::try_from(self.scope_depth()).unwrap_or(u32::MAX);
            diag.emit_pop(from_level, to_level);
        }
        true
    }

    /// Get the current scope depth.
    ///
    /// Returns 0 when no push() calls are active.
    #[must_use]
    pub fn scope_depth(&self) -> usize {
        self.sat.scope_depth()
    }

    /// Extract learned clauses from the SAT solver.
    ///
    /// Used in branch-and-bound to preserve learned clauses across solver recreations.
    #[must_use]
    pub fn get_learned_clauses(&self) -> Vec<Vec<Literal>> {
        self.sat.get_learned_clauses()
    }

    /// Add learned clauses from a previous solve session.
    ///
    /// Used in branch-and-bound to restore learned clauses after recreating the solver.
    /// Automatically expands the solver's variable count if learned clauses reference
    /// variables beyond the current `num_vars` (#4797).
    pub fn add_learned_clauses(&mut self, clauses: Vec<Vec<Literal>>) {
        // Find the maximum variable referenced across all learned clauses.
        // The previous solver may have allocated more variables (e.g., from
        // split atoms applied during solving) than the current solver has after
        // re-applying accumulated splits. Expand to accommodate.
        let max_var = clauses
            .iter()
            .flat_map(|c| c.iter())
            .map(|l| l.variable().index())
            .max();
        if let Some(max_var) = max_var {
            self.sat.ensure_num_vars(max_var + 1);
        }
        for clause in clauses {
            self.sat.add_preserved_learned(clause);
        }
    }
}
