// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Init-state predicate solving.
//!
//! TLC alignment: `ModelChecker.DoInitFunctor` (init-state production from predicate).
//!
//! Both `solve_predicate_for_states` (Vec-based) and `solve_predicate_for_states_to_bulk`
//! (streaming BulkStateStorage) share operator resolution, constraint extraction, z4
//! enumeration, and type-candidate discovery via helpers defined here.

mod bulk_solve;
mod precheck;
mod resolve;
mod vec_solve;

use super::super::BulkStateStorage;
use crate::enumerate::{BulkConstraintEnumerationStats, Constraint};
// Re-export for child modules (resolve.rs, precheck.rs) that import via `super::`.
// Uses crate-absolute paths because `super::super::` traverses private modules,
// which blocks `pub(crate) use` re-exports (E0365).
pub(crate) use crate::check::CheckError;
#[cfg(feature = "z4")]
pub(crate) use crate::state::State;
pub(crate) use crate::{ConfigCheckError, EvalCheckError};

/// Results from resolving an init predicate and extracting constraints.
///
/// Stores the resolved operator name (owned) rather than a reference to the body
/// so callers can later borrow `self.ctx` mutably without conflicting with the
/// immutable borrow of `self.module`.
pub(super) struct InitPredResolved {
    /// The resolved operator name (after config replacements).
    pub(super) resolved_name: String,
    /// Extracted constraint branches (None if extraction failed).
    pub(super) extracted_branches: Option<Vec<Vec<Constraint>>>,
    /// Variables without constraints.
    pub(super) unconstrained_vars: Vec<String>,
    /// Whether constraint extraction succeeded.
    pub(super) constraint_extraction_succeeded: bool,
}

/// Bulk init states plus the pre-dedup counts needed for progress reporting.
pub(in crate::check) struct BulkInitStates {
    pub storage: BulkStateStorage,
    pub enumeration: BulkConstraintEnumerationStats,
}
