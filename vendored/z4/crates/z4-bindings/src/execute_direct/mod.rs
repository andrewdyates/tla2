// Copyright 2026 Andrew Yates.
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Direct Z4 Program Execution.
//!
//! This module provides direct execution of `Z4Program` against the
//! `z4_dpll::api::Solver` without SMT-LIB2 serialization and parsing.
//!
//! Decomposed into submodules per #1056.
//!
//! ## Architecture
//!
//! Old path (SMT-LIB text file):
//! ```text
//! Z4Program → Display::fmt → .smt2 file → Parser → Executor
//! ```
//!
//! New path (direct execution):
//! ```text
//! Z4Program → execute_direct → z4_dpll::api::Solver → result
//! ```
//!
//! ## Fallback
//!
//! Some constructs are not yet supported by direct execution (and will trigger fallback):
//! - CHC commands (DeclareRel, Rule, Query)
//! - Soft assertions (MaxSAT)
//!
//! When these are detected, `execute` returns `ExecuteResult::NeedsFallback`
//! and the caller should use the SMT-LIB file-based path.
//!
//! The following are now handled directly (no fallback):
//! - CheckSatAssuming (#5456)
//! - Bv2Int, Int2Bv, IntToReal, RealToInt, IsInt (#5406)
//! - Quantifiers (Forall/Exists) and function application (#5406)
//! - Datatypes (constructors, selectors, testers) (#5406)
//! - Integer/real constants of arbitrary size (via BigInt API)
//! - FP comparisons, classification, constants, unary ops, conversions (#5774)
//! - FP arithmetic (add, sub, mul, div, fma, sqrt, rem, roundToIntegral) (#6128)
//! - Optimization objectives (maximize/minimize/get-objectives) via OMT bridge (#6702)
//!
//! ## GetValue Support (#1977)
//!
//! GetValue commands are now supported via direct execution. Terms are collected
//! during constraint processing and evaluated after check-sat returns SAT.
//! Results are included in `ExecuteResult::Counterexample::values`.
//!
//! ## Panic Handling (#1044, #6329)
//!
//! All phases — constraint translation, check_sat, and model extraction — use
//! `z4_core::catch_z4_panics` to distinguish z4-internal panics from
//! programmer errors. z4-classified panics (sort mismatches, conflict
//! verification failures, etc.) degrade to `ExecuteResult::Unknown`.
//! Non-z4 panics (index out of bounds, assertion failures) propagate via
//! `resume_unwind` so programmer errors are not silently swallowed.
//!
//! ## Usage
//!
//! ```rust,no_run
//! use z4_bindings::{Z4Program, execute_direct::{execute, ExecuteResult}};
//!
//! fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     let program = Z4Program::qf_bv();
//!     // ... add constraints ...
//!
//!     match execute(&program)? {
//!         ExecuteResult::Verified => println!("All properties verified"),
//!         ExecuteResult::Counterexample { .. } => println!("Found counterexample"),
//!         ExecuteResult::NeedsFallback(reason) => {
//!             println!("Fallback needed: {}", reason);
//!             // Use SMT-LIB file-based path
//!         }
//!         ExecuteResult::Unknown(reason) => println!("Unknown: {}", reason),
//!         _ => {} // future ExecuteResult variants
//!     }
//!     Ok(())
//! }
//! ```
//!
//! See issue #513 for context.

mod constraints;
mod context;
mod driver;
mod extract;
mod fallback;
mod logic;
mod omt;
mod translate;
mod translate_bridge;
mod types;

use crate::program::Z4Program;
use driver::{execute_typed_with_details_impl, into_untyped_details};

pub use types::{
    ExecuteCounterexample, ExecuteDegradation, ExecuteDegradationKind, ExecuteDetails,
    ExecuteError, ExecuteFallback, ExecuteFallbackKind, ExecuteResult, ExecuteTypedDetails,
    ExecuteTypedResult,
};
pub use z4_dpll::api::ModelValue;

/// Execute a Z4Program directly using z4_dpll's native API.
///
/// # Returns
///
/// - `Ok(ExecuteResult::Verified)` if all assertions hold (UNSAT)
/// - `Ok(ExecuteResult::Counterexample { .. })` if a counterexample exists (SAT)
/// - `Ok(ExecuteResult::NeedsFallback(reason))` if direct execution not supported
/// - `Ok(ExecuteResult::Unknown(reason))` if solver returns unknown or panics (#1044)
/// - `Err(ExecuteError)` on execution failure
///
/// # Fallback Conditions
///
/// Returns `NeedsFallback` when the program contains unsupported constructs:
/// - CHC commands (DeclareRel, Rule, Query)
/// - Soft assertions (MaxSAT)
/// - Integer/real/bitvector constants that exceed i64
///
/// Unsupported logics (e.g., `HORN`) return
/// `Err(ExecuteError::UnsupportedLogic(..))` and should use the fallback path.
///
/// See module-level documentation for the complete list.
#[must_use = "execute returns a Result that must be used"]
pub fn execute(program: &Z4Program) -> Result<ExecuteResult, ExecuteError> {
    Ok(execute_with_details(program)?.result)
}

/// Execute a Z4Program directly and return the untyped result plus provenance.
#[must_use = "execute_with_details returns a Result that must be used"]
pub fn execute_with_details(program: &Z4Program) -> Result<ExecuteDetails, ExecuteError> {
    Ok(into_untyped_details(execute_typed_with_details(program)?))
}

/// Execute a Z4Program directly and preserve typed model values.
#[must_use = "execute_typed returns a Result that must be used"]
pub fn execute_typed(program: &Z4Program) -> Result<ExecuteTypedResult, ExecuteError> {
    Ok(execute_typed_with_details(program)?.result)
}

/// Execute a Z4Program directly with typed values and detailed provenance.
#[must_use = "execute_typed_with_details returns a Result that must be used"]
pub fn execute_typed_with_details(
    program: &Z4Program,
) -> Result<ExecuteTypedDetails, ExecuteError> {
    execute_typed_with_details_impl(program)
}

/// Check if direct execution is available (compile-time feature gate).
#[must_use]
pub fn is_available() -> bool {
    true
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
