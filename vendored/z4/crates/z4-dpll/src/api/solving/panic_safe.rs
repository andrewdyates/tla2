// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Panic-safe wrappers for `check_sat` and `check_sat_assuming`.

use z4_core::panic_payload_to_string;

use crate::api::types::{
    AssumptionSolveDetails, SolveDetails, SolverError, Term, VerifiedSolveResult,
};
use crate::api::Solver;

impl Solver {
    /// Check satisfiability, catching any internal panics.
    ///
    /// This is a panic-safe wrapper around [`check_sat`]. If the solver panics
    /// during solving, the panic is caught and returned as
    /// [`SolverError::SolverPanic`] instead of unwinding the caller's stack.
    ///
    /// Downstream consumers (sunder, certus, zani) can use this instead of
    /// independently implementing `catch_unwind(AssertUnwindSafe(...))` wrappers.
    ///
    /// # Example
    ///
    /// ```
    /// use z4_dpll::api::{Solver, Logic, SolveResult};
    ///
    /// let mut solver = Solver::new(Logic::QfLia);
    /// let x = solver.declare_const("x", z4_dpll::api::Sort::Int);
    /// let zero = solver.int_const(0);
    /// let gt = solver.gt(x, zero);
    /// solver.assert_term(gt);
    ///
    /// let result = solver.try_check_sat();
    /// assert!(result.is_ok());
    /// assert_eq!(result.unwrap(), SolveResult::Sat);
    /// ```
    ///
    /// [`check_sat`]: Solver::check_sat
    pub fn try_check_sat(&mut self) -> Result<VerifiedSolveResult, SolverError> {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.check_sat()))
            .map_err(|e| SolverError::SolverPanic(panic_payload_to_string(&*e)))
    }

    /// Check satisfiability under temporary assumptions, catching any internal panics.
    ///
    /// This is a panic-safe wrapper around [`check_sat_assuming`]. If the solver
    /// panics during solving, the panic is caught and returned as
    /// [`SolverError::SolverPanic`].
    ///
    /// # Example
    ///
    /// ```
    /// use z4_dpll::api::{Solver, Logic, SolveResult, Sort};
    ///
    /// let mut solver = Solver::new(Logic::QfLia);
    /// let x = solver.declare_const("x", Sort::Int);
    /// let zero = solver.int_const(0);
    /// let x_gt_0 = solver.gt(x, zero);
    /// solver.assert_term(x_gt_0);
    ///
    /// let x_lt_0 = solver.lt(x, zero);
    /// let result = solver.try_check_sat_assuming(&[x_lt_0]);
    /// assert!(result.is_ok());
    /// assert_eq!(result.unwrap(), SolveResult::Unsat);
    /// ```
    ///
    /// [`check_sat_assuming`]: Solver::check_sat_assuming
    pub fn try_check_sat_assuming(
        &mut self,
        assumptions: &[Term],
    ) -> Result<VerifiedSolveResult, SolverError> {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.check_sat_assuming(assumptions)
        }))
        .map_err(|e| SolverError::SolverPanic(panic_payload_to_string(&*e)))
    }

    /// Check satisfiability and return atomic result details, catching panics.
    ///
    /// Panic-safe wrapper around [`check_sat_with_details`]. On panic, returns
    /// [`SolverError::SolverPanic`] instead of unwinding.
    ///
    /// [`check_sat_with_details`]: Solver::check_sat_with_details
    pub fn try_check_sat_with_details(&mut self) -> Result<SolveDetails, SolverError> {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.check_sat_with_details()
        }))
        .map_err(|e| SolverError::SolverPanic(panic_payload_to_string(&*e)))
    }

    /// Check satisfiability under assumptions and return atomic result details
    /// including unsat assumptions, catching panics.
    ///
    /// Panic-safe wrapper around [`check_sat_assuming_with_details`]. On panic,
    /// returns [`SolverError::SolverPanic`] instead of unwinding.
    ///
    /// [`check_sat_assuming_with_details`]: Solver::check_sat_assuming_with_details
    pub fn try_check_sat_assuming_with_details(
        &mut self,
        assumptions: &[Term],
    ) -> Result<AssumptionSolveDetails, SolverError> {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.check_sat_assuming_with_details(assumptions)
        }))
        .map_err(|e| SolverError::SolverPanic(panic_payload_to_string(&*e)))
    }
}
