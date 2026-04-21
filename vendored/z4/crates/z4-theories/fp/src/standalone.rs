// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use z4_core::term::TermId;
use z4_core::CnfClause;

/// Standalone FP solver placeholder.
pub struct FpSolverStandalone {
    pub(crate) clauses: Vec<CnfClause>,
    pub(crate) next_var: u32,
    pub(crate) trail: Vec<TermId>,
    pub(crate) trail_stack: Vec<usize>,
}

impl FpSolverStandalone {
    /// Create a new standalone FP solver.
    #[must_use]
    pub fn new() -> Self {
        Self {
            clauses: Vec::new(),
            next_var: 1,
            trail: Vec::new(),
            trail_stack: Vec::new(),
        }
    }
}

impl Default for FpSolverStandalone {
    fn default() -> Self {
        Self::new()
    }
}
