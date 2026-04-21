// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Equality invariant discovery for PDR solver.
//!
//! This module contains methods for discovering and verifying equality invariants
//! of the form `var_i = var_j` (two variables are always equal) or `var_i = var_j + k`
//! (variables differ by a constant offset).
//!
//! ## Key Methods
//!
//! - [`PdrSolver::discover_equality_invariants`] - Main discovery entry point
//! - [`PdrSolver::is_equality_preserved_by_transitions_with_entry`] - Check if equality
//!   is preserved across all self-loop transitions
//!
//! ## Algorithm
//!
//! 1. For each predicate, enumerate all pairs of integer variables
//! 2. Check if equality is implied by fact clauses (initialization)
//! 3. Verify equality is preserved by all transition clauses
//! 4. If both hold, add `var_i = var_j` as a discovered invariant
//!
//! The preservation check uses SMT to verify: `pre_i = pre_j ∧ constraint ⇒ post_i = post_j`

use super::super::PdrSolver;
use super::MAX_PAIRWISE_DISCOVERY_VARS;

use rustc_hash::FxHashMap;

use crate::pdr::types::VarOffset;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};

mod discovery;
mod preservation;
mod transition;
mod transition_utils;

#[cfg(test)]
mod tests;
