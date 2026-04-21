// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native Rust API for Z4 SMT Solver
//!
//! This module provides a programmatic interface for building and solving SMT
//! constraints directly in Rust, without parsing SMT-LIB text.
//!
//! # Example
//!
//! ```
//! use num_bigint::BigInt;
//! use z4_dpll::api::{Logic, ModelValue, SolveResult, Solver, Sort};
//!
//! let mut solver = Solver::try_new(Logic::QfLia).expect("valid logic");
//!
//! // Declare variables
//! let x = solver.declare_const("x", Sort::Int);
//! let y = solver.declare_const("y", Sort::Int);
//!
//! // Assert constraints: x > 0 and y = x + 1
//! let zero = solver.int_const(0);
//! let one = solver.int_const(1);
//! let x_gt_zero = solver.try_gt(x, zero).expect("int > int");
//! solver.try_assert_term(x_gt_zero).expect("boolean assertion");
//! let x_plus_one = solver.try_add(x, one).expect("int + int");
//! let y_eq_x_plus_one = solver.try_eq(y, x_plus_one).expect("matching sorts");
//! solver
//!     .try_assert_term(y_eq_x_plus_one)
//!     .expect("boolean assertion");
//!
//! // Check satisfiability with the atomic solve envelope
//! let details = solver.check_sat_with_details();
//! match details.accept_for_consumer() {
//!     Ok(SolveResult::Sat) => {
//!         let x_val = match solver.value(x) {
//!             Some(ModelValue::Int(value)) => value,
//!             _ => unreachable!("expected Int model value for x"),
//!         };
//!         let y_val = match solver.value(y) {
//!             Some(ModelValue::Int(value)) => value,
//!             _ => unreachable!("expected Int model value for y"),
//!         };
//!         assert!(x_val > BigInt::from(0));
//!         assert_eq!(y_val, x_val + BigInt::from(1));
//!     }
//!     Ok(SolveResult::Unsat) => { /* unsatisfiable */ }
//!     Ok(SolveResult::Unknown) | Err(_) => {
//!         let _reason = details.unknown_reason;
//!     }
//!     Ok(_) => { /* future solve result variant */ }
//! }
//! ```

mod bitvectors;
mod floating_point;
mod floating_point_conv;
mod introspect;
mod model_parse;
mod model_parse_compound;
mod proofs;
mod sequences;
mod solving;
mod strings;
mod terms;
pub mod types;

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

// Re-export all public types for backwards compatibility
pub use introspect::TermKind;
pub use proofs::{
    FarkasCertificate, ProofAcceptanceError, ProofAcceptanceMode, StrictProofVerdict,
    UnsatProofArtifact,
};
pub use solving::SolverScope;
pub use types::*;
// Re-export proof types used in public API signatures
pub use z4_proof::{PartialProofCheck, ProofCheckError, ProofQuality};
// Re-export Sort types from z4_core (#1437 - Sort type consolidation)
pub use z4_core::{ArraySort, BitVecSort, DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
// Re-export deprecated term introspection types for backwards compatibility
#[allow(deprecated)]
pub use terms::AstKind;

use std::collections::HashMap;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::time::Duration;

use z4_core::{TermId, TermStore};
use z4_frontend::Command;

use crate::{Executor, UnknownReason};

/// Native Rust API for Z4 SMT solver
///
/// Provides a programmatic interface for building SMT constraints
/// and checking satisfiability without parsing SMT-LIB text.
pub struct Solver {
    executor: Executor,
    /// Variable names for model extraction
    var_names: HashMap<TermId, String>,
    /// Variable sorts for model extraction
    var_sorts: HashMap<TermId, Sort>,
    /// Last assumptions from check_sat_assuming (TermId -> Term mapping)
    last_assumptions: Option<HashMap<TermId, Term>>,
    /// Interrupt flag for cancelling solve from another thread
    interrupt: Arc<AtomicBool>,
    /// Timeout duration for check_sat calls (None = no timeout)
    timeout: Option<Duration>,
    /// Memory limit in bytes for check_sat calls (None = no limit)
    memory_limit: Option<usize>,
    /// Maximum learned clauses for SAT solver (None = no limit)
    learned_clause_limit: Option<usize>,
    /// Maximum clause DB size (bytes) for SAT solver (None = no limit)
    clause_db_bytes_limit: Option<usize>,
    /// Current push/pop scope depth (incremented by push, decremented by pop)
    scope_level: u32,
    /// Reason for last Unknown result
    last_unknown_reason: Option<UnknownReason>,
    /// Detail message from the last executor error (when reason is InternalError)
    last_executor_error: Option<String>,
    /// Per-instance term memory limit in bytes (None = no limit).
    /// Unlike `memory_limit` (process RSS), this caps term allocation for
    /// THIS solver only, preventing cross-instance budget interference (#6563).
    term_memory_limit: Option<usize>,
}

impl Solver {
    /// Create a new solver for the specified logic
    ///
    /// # Panics
    ///
    /// Panics if the logic is not supported. Use [`try_new`] for a fallible
    /// version that returns an error instead.
    ///
    /// # Example
    ///
    /// ```
    /// use z4_dpll::api::{Logic, Solver};
    ///
    /// let _solver = Solver::new(Logic::QfLia);
    /// ```
    ///
    /// [`try_new`]: Solver::try_new
    /// # Panics
    ///
    /// Panics if the solver cannot be created for the given logic. Use
    /// [`try_new`](Solver::try_new) for a fallible alternative.
    #[deprecated(note = "use try_new() which returns Result instead of panicking")]
    #[must_use]
    #[allow(clippy::panic)]
    pub fn new(logic: Logic) -> Self {
        Self::try_new(logic)
            .unwrap_or_else(|e| panic!("Failed to create solver for logic {logic:?}: {e}"))
    }

    /// Try to create a new solver for the specified logic.
    ///
    /// Fallible version of [`new`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns an error if the logic is not supported.
    ///
    /// # Example
    ///
    /// ```
    /// use z4_dpll::api::{Solver, Logic, SolverError};
    ///
    /// // Create solver with fallible constructor
    /// let solver = Solver::try_new(Logic::QfLia);
    /// assert!(solver.is_ok());
    /// ```
    ///
    /// [`new`]: Solver::new
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_new(logic: Logic) -> Result<Self, SolverError> {
        let mut executor = Executor::new();
        // Set the logic and propagate errors
        executor.execute(&Command::SetLogic(logic.as_str().to_string()))?;
        Ok(Self {
            executor,
            var_names: HashMap::new(),
            var_sorts: HashMap::new(),
            last_assumptions: None,
            interrupt: Arc::new(AtomicBool::new(false)),
            timeout: None,
            memory_limit: None,
            learned_clause_limit: None,
            clause_db_bytes_limit: None,
            scope_level: 0,
            last_unknown_reason: None,
            last_executor_error: None,
            term_memory_limit: None,
        })
    }

    /// Access the internal term store
    fn terms(&self) -> &TermStore {
        &self.executor.context().terms
    }

    /// Access the internal term store mutably
    fn terms_mut(&mut self) -> &mut TermStore {
        &mut self.executor.context_mut().terms
    }

    fn expect_bitvec(&self, operation: &'static str, t: Term) -> Result<(), SolverError> {
        let sort = self.terms().sort(t.0).clone();
        match sort {
            Sort::BitVec(_) => Ok(()),
            other => Err(SolverError::SortMismatch {
                operation,
                expected: "BitVec",
                got: vec![other],
            }),
        }
    }

    fn expect_int(&self, operation: &'static str, t: Term) -> Result<(), SolverError> {
        let sort = self.terms().sort(t.0).clone();
        match sort {
            Sort::Int => Ok(()),
            other => Err(SolverError::SortMismatch {
                operation,
                expected: "Int",
                got: vec![other],
            }),
        }
    }

    fn expect_real(&self, operation: &'static str, t: Term) -> Result<(), SolverError> {
        let sort = self.terms().sort(t.0).clone();
        match sort {
            Sort::Real => Ok(()),
            other => Err(SolverError::SortMismatch {
                operation,
                expected: "Real",
                got: vec![other],
            }),
        }
    }

    fn expect_bitvec_width(&self, operation: &'static str, t: Term) -> Result<u32, SolverError> {
        let sort = self.terms().sort(t.0).clone();
        match sort {
            Sort::BitVec(bv) => Ok(bv.width),
            other => Err(SolverError::SortMismatch {
                operation,
                expected: "BitVec",
                got: vec![other],
            }),
        }
    }

    fn expect_bitvec_width2(
        &self,
        operation: &'static str,
        a: Term,
        b: Term,
    ) -> Result<(u32, u32), SolverError> {
        let a_sort = self.terms().sort(a.0).clone();
        let b_sort = self.terms().sort(b.0).clone();
        match (&a_sort, &b_sort) {
            (Sort::BitVec(a_bv), Sort::BitVec(b_bv)) => Ok((a_bv.width, b_bv.width)),
            _ => Err(SolverError::SortMismatch {
                operation,
                expected: "BitVec, BitVec",
                got: vec![a_sort, b_sort],
            }),
        }
    }

    fn expect_same_bitvec_width(
        &self,
        operation: &'static str,
        a: Term,
        b: Term,
    ) -> Result<u32, SolverError> {
        let a_sort = self.terms().sort(a.0).clone();
        let b_sort = self.terms().sort(b.0).clone();
        match (&a_sort, &b_sort) {
            (Sort::BitVec(a_bv), Sort::BitVec(b_bv)) if a_bv.width == b_bv.width => Ok(a_bv.width),
            _ => Err(SolverError::SortMismatch {
                operation,
                expected: "BitVec(w), BitVec(w)",
                got: vec![a_sort, b_sort],
            }),
        }
    }

    /// Check that a term has an arithmetic sort (Int or Real).
    fn expect_arith(&self, operation: &'static str, a: Term) -> Result<Sort, SolverError> {
        let sort = self.terms().sort(a.0).clone();
        match &sort {
            Sort::Int | Sort::Real => Ok(sort),
            _ => Err(SolverError::SortMismatch {
                operation,
                expected: "Int or Real",
                got: vec![sort],
            }),
        }
    }

    /// Check that two terms have the same arithmetic sort (both Int or both Real).
    fn expect_same_arith_sort(
        &self,
        operation: &'static str,
        a: Term,
        b: Term,
    ) -> Result<Sort, SolverError> {
        let a_sort = self.terms().sort(a.0).clone();
        let b_sort = self.terms().sort(b.0).clone();
        match (&a_sort, &b_sort) {
            (Sort::Int, Sort::Int) => Ok(Sort::Int),
            (Sort::Real, Sort::Real) => Ok(Sort::Real),
            _ => Err(SolverError::SortMismatch {
                operation,
                expected: "same arithmetic sort (Int,Int) or (Real,Real)",
                got: vec![a_sort, b_sort],
            }),
        }
    }

    /// Check that two terms are both Int.
    fn expect_both_int(
        &self,
        operation: &'static str,
        a: Term,
        b: Term,
    ) -> Result<(), SolverError> {
        let a_sort = self.terms().sort(a.0).clone();
        let b_sort = self.terms().sort(b.0).clone();
        match (&a_sort, &b_sort) {
            (Sort::Int, Sort::Int) => Ok(()),
            _ => Err(SolverError::SortMismatch {
                operation,
                expected: "Int, Int",
                got: vec![a_sort, b_sort],
            }),
        }
    }

    /// Check that two terms are both Real.
    fn expect_both_real(
        &self,
        operation: &'static str,
        a: Term,
        b: Term,
    ) -> Result<(), SolverError> {
        let a_sort = self.terms().sort(a.0).clone();
        let b_sort = self.terms().sort(b.0).clone();
        match (&a_sort, &b_sort) {
            (Sort::Real, Sort::Real) => Ok(()),
            _ => Err(SolverError::SortMismatch {
                operation,
                expected: "Real, Real",
                got: vec![a_sort, b_sort],
            }),
        }
    }

    /// Check that a term has Bool sort.
    fn expect_bool(&self, operation: &'static str, t: Term) -> Result<(), SolverError> {
        let sort = self.terms().sort(t.0).clone();
        match sort {
            Sort::Bool => Ok(()),
            other => Err(SolverError::SortMismatch {
                operation,
                expected: "Bool",
                got: vec![other],
            }),
        }
    }

    /// Check that two terms have the same sort (any sort, but matching).
    fn expect_same_sort(
        &self,
        operation: &'static str,
        a: Term,
        b: Term,
    ) -> Result<(), SolverError> {
        let a_sort = self.terms().sort(a.0).clone();
        let b_sort = self.terms().sort(b.0).clone();
        if a_sort == b_sort {
            Ok(())
        } else {
            Err(SolverError::SortMismatch {
                operation,
                expected: "same sort for both arguments",
                got: vec![a_sort, b_sort],
            })
        }
    }

    /// Check that a term has String sort.
    fn expect_string(&self, operation: &'static str, t: Term) -> Result<(), SolverError> {
        let sort = self.terms().sort(t.0).clone();
        if sort == Sort::String {
            Ok(())
        } else {
            Err(SolverError::SortMismatch {
                operation,
                expected: "String",
                got: vec![sort],
            })
        }
    }

    /// Check that a term has RegLan sort.
    fn expect_reglan(&self, operation: &'static str, t: Term) -> Result<(), SolverError> {
        let sort = self.terms().sort(t.0).clone();
        if sort == Sort::RegLan {
            Ok(())
        } else {
            Err(SolverError::SortMismatch {
                operation,
                expected: "RegLan",
                got: vec![sort],
            })
        }
    }
}
