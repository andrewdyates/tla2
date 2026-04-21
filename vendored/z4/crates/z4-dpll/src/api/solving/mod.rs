// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Assertion, solving, and model extraction for Z4 Solver API.
//!
//! This module is split by solver lifecycle stage:
//!
//! - [`assertions`]: Assert, push, pop, scopes, reset
//! - [`controls`]: Verification level, counterexample style, timeout/memory/clause limits,
//!   interrupt, unknown reason, statistics
//! - [`check`]: `check_sat`, `check_sat_assuming`, shared preflight/epilogue helpers
//! - [`panic_safe`]: `try_check_sat`, `try_check_sat_assuming`
//! - [`cross_check`]: script-first replay API for logic/seed differential checks
//! - [`model`]: Unsat assumptions, model/value extraction, declared variables
//! - [`proofs`]: Proof production controls and access
//! - [`parse`]: SMT-LIB2 parsing bridge
//! - [`scope`]: RAII `SolverScope` helper for balanced push/pop lifetimes

mod assertions;
mod check;
mod controls;
mod cross_check;
mod model;
mod panic_safe;
mod parse;
mod proofs;
mod scope;

pub use scope::SolverScope;
