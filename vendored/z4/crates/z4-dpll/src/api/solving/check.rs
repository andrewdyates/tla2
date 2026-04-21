// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core `check_sat` and `check_sat_assuming` entrypoints with shared
//! preflight and result-classification helpers.

use std::sync::atomic::Ordering;
use std::time::Instant;

use crate::api::types::{SolveResult, Term, VerifiedSolveResult};
use crate::api::Solver;
use crate::UnknownReason;

impl Solver {
    /// Reset last-solve state fields before a new check-sat call.
    fn clear_last_solve_state(&mut self, clear_assumptions: bool) {
        if clear_assumptions {
            self.last_assumptions = None;
        }
        self.last_unknown_reason = None;
        self.last_executor_error = None;
    }

    /// Pre-check interrupt, memory, and deadline before entering the executor.
    /// Returns `Some(Unknown)` with the appropriate reason if a preflight
    /// condition fires, or `None` if the solve should proceed.
    fn preflight_check(&mut self, deadline: Option<Instant>) -> Option<VerifiedSolveResult> {
        if self.interrupt.load(Ordering::Relaxed) {
            self.last_unknown_reason = Some(UnknownReason::Interrupted);
            return Some(VerifiedSolveResult::from_validated(
                SolveResult::Unknown,
                false,
            ));
        }

        if crate::memory::memory_exceeded(self.memory_limit) || z4_sys::process_memory_exceeded() {
            self.last_unknown_reason = Some(UnknownReason::MemoryLimit);
            return Some(VerifiedSolveResult::from_validated(
                SolveResult::Unknown,
                false,
            ));
        }

        // Per-instance term memory check (#6563): prevents cross-instance
        // budget interference when multiple solvers run in the same process.
        if let Some(limit) = self.term_memory_limit {
            if self.terms().instance_memory_exceeded(limit) {
                self.last_unknown_reason = Some(UnknownReason::MemoryLimit);
                return Some(VerifiedSolveResult::from_validated(
                    SolveResult::Unknown,
                    false,
                ));
            }
        }

        if let Some(dl) = deadline {
            if Instant::now() >= dl {
                self.last_unknown_reason = Some(UnknownReason::Timeout);
                return Some(VerifiedSolveResult::from_validated(
                    SolveResult::Unknown,
                    false,
                ));
            }
        }

        None
    }

    /// Forward solve-control limits to the executor and install the interrupt
    /// handle and deadline.
    fn install_solve_controls(&mut self, deadline: Option<Instant>) {
        self.executor
            .set_learned_clause_limit(self.learned_clause_limit);
        self.executor
            .set_clause_db_bytes_limit(self.clause_db_bytes_limit);
        self.executor
            .set_solve_controls(Some(self.interrupt.clone()), deadline);
    }

    /// Classify an `Unknown` result that has no reason yet, using executor
    /// state, interrupt flag, deadline, and memory limit.
    fn classify_unknown_reason(&mut self, deadline: Option<Instant>) {
        if let Some(reason) = self.executor.unknown_reason() {
            self.last_unknown_reason = Some(reason);
        } else if self.interrupt.load(Ordering::Relaxed) {
            self.last_unknown_reason = Some(UnknownReason::Interrupted);
        } else if deadline.is_some_and(|d| Instant::now() >= d) {
            self.last_unknown_reason = Some(UnknownReason::Timeout);
        } else if crate::memory::memory_exceeded(self.memory_limit)
            || z4_sys::process_memory_exceeded()
            || self
                .term_memory_limit
                .is_some_and(|limit| self.terms().instance_memory_exceeded(limit))
        {
            self.last_unknown_reason = Some(UnknownReason::MemoryLimit);
        } else {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
        }
    }

    // =========================================================================
    // Solving
    // =========================================================================

    /// Check satisfiability of the current assertions.
    ///
    /// Returns a `VerifiedSolveResult` where Sat results carry validation
    /// provenance. Use [`was_model_validated()`](VerifiedSolveResult::was_model_validated)
    /// to check whether model validation actually ran. Part of #5748, #5973.
    pub fn check_sat(&mut self) -> VerifiedSolveResult {
        self.clear_last_solve_state(true);

        let deadline = self.timeout.map(|d| Instant::now() + d);
        if let Some(early) = self.preflight_check(deadline) {
            return early;
        }

        self.install_solve_controls(deadline);
        let exec_result = self.executor.check_sat();
        self.executor.clear_solve_controls();

        let result = match exec_result {
            Ok(r) => r,
            Err(e) => {
                self.last_unknown_reason = Some(UnknownReason::InternalError);
                self.last_executor_error = Some(e.to_string());
                SolveResult::Unknown
            }
        };

        if result == SolveResult::Unknown && self.last_unknown_reason.is_none() {
            self.classify_unknown_reason(deadline);
        }

        VerifiedSolveResult::from_validated(result, self.executor.was_model_validated())
    }

    /// Check satisfiability under temporary assumptions
    ///
    /// Unlike `assert_term()`, assumptions are temporary - they only apply to this
    /// single check-sat call and do not affect the assertion stack.
    ///
    /// After an UNSAT result, call `get_unsat_assumptions()` to get the subset
    /// of assumptions that contributed to unsatisfiability.
    ///
    /// # Example
    ///
    /// ```
    /// use z4_dpll::api::{Solver, Sort, SolveResult, Logic};
    ///
    /// let mut solver = Solver::new(Logic::QfLia);
    /// let x = solver.declare_const("x", Sort::Int);
    /// let zero = solver.int_const(0);
    /// let one = solver.int_const(1);
    ///
    /// // Assert x >= 0 permanently
    /// let x_ge_0 = solver.ge(x, zero);
    /// solver.assert_term(x_ge_0);
    ///
    /// // Check with temporary assumption x < 0 - should be UNSAT
    /// let x_lt_0 = solver.lt(x, zero);
    /// assert_eq!(solver.check_sat_assuming(&[x_lt_0]), SolveResult::Unsat);
    ///
    /// // Original assertion still holds, without the assumption
    /// let x_eq_1 = solver.eq(x, one);
    /// assert_eq!(solver.check_sat_assuming(&[x_eq_1]), SolveResult::Sat);
    /// ```
    pub fn check_sat_assuming(&mut self, assumptions: &[Term]) -> VerifiedSolveResult {
        self.clear_last_solve_state(false);

        let deadline = self.timeout.map(|d| Instant::now() + d);
        if let Some(early) = self.preflight_check(deadline) {
            return early;
        }

        self.install_solve_controls(deadline);

        let assumption_ids: Vec<_> = assumptions.iter().map(|t| t.0).collect();
        self.last_assumptions = Some(assumptions.iter().map(|t| (t.0, *t)).collect());

        let exec_result = self.executor.check_sat_assuming(&assumption_ids);
        self.executor.clear_solve_controls();

        let result = match exec_result {
            Ok(r) => r,
            Err(e) => {
                self.last_unknown_reason = Some(UnknownReason::InternalError);
                self.last_executor_error = Some(e.to_string());
                SolveResult::Unknown
            }
        };

        if result == SolveResult::Unknown && self.last_unknown_reason.is_none() {
            self.classify_unknown_reason(deadline);
        }

        VerifiedSolveResult::from_validated(result, self.executor.was_model_validated())
    }
}
