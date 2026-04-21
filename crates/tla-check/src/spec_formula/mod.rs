// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SPECIFICATION formula extraction
//!
//! Extracts Init and Next predicates from TLA+ temporal formulas like:
//! - `Init /\ [][Next]_vars`
//! - `Init /\ [][Next]_vars /\ WF_vars(Next)`
//!
//! TLC allows SPECIFICATION directive to reference a temporal formula
//! instead of separate INIT/NEXT directives.
//!
//! Split into domain modules (Part of #1643):
//! - `types`: Data type definitions (SpecFormula, FairnessConstraint)
//! - `conjunct`: Conjunction extraction and classification
//! - `subscript`: Action/subscript CST parsing
//! - `fairness`: Fairness constraint extraction
//! - `cst_helpers`: Shared CST utility functions

mod conjunct;
mod cst_helpers;
mod fairness;
mod subscript;
mod types;

#[cfg(test)]
mod tests;

// Public API (unchanged from original spec_formula.rs)
pub use types::{FairnessConstraint, SpecFormula};

// Crate-internal API
pub(crate) use fairness::extract_all_fairness;

use tla_core::SyntaxNode;

/// Extract Init and Next from a SPECIFICATION temporal formula.
///
/// Supports common patterns:
/// - `Init /\ [][Next]_vars`
/// - `Init /\ [][Next]_<<v1,v2>>`
/// - `Init /\ [][Next]_vars /\ WF_vars(Next)`
/// - `/\ Init /\ [][Next]_vars` (conjunction list style)
///
/// Returns None if the formula doesn't match any known pattern.
pub fn extract_spec_formula(spec_body: &SyntaxNode) -> Option<SpecFormula> {
    // Try different extraction patterns
    conjunct::extract_and_pattern(spec_body)
        .or_else(|| conjunct::extract_conjunction_list(spec_body))
}
