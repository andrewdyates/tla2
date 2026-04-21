// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CHC/PDR result types and formatting helpers

use std::collections::HashMap;

use z4_chc::{Counterexample, InvariantModel};

/// Result of PDR safety checking
#[derive(Debug)]
pub enum PdrCheckResult {
    /// Proven safe with synthesized invariant
    Safe {
        /// String representation of the invariant
        invariant: String,
    },
    /// Found counterexample trace
    Unsafe {
        /// Counterexample trace (each step is a state assignment)
        trace: Vec<PdrState>,
    },
    /// Inconclusive (resource limits reached)
    Unknown {
        /// Reason for unknown result
        reason: String,
    },
}

/// A state in the PDR counterexample trace
#[derive(Debug, Clone)]
pub struct PdrState {
    /// Variable assignments: name -> value
    pub assignments: HashMap<String, i64>,
}

/// Format invariant model for display
pub(super) fn format_invariant(model: &InvariantModel) -> String {
    format!("{model:?}")
}

/// Format counterexample trace
pub(super) fn format_counterexample(cex: &Counterexample) -> Vec<PdrState> {
    cex.steps
        .iter()
        .map(|step| {
            let assignments = step
                .assignments
                .iter()
                .map(|(name, val)| (name.clone(), *val))
                .collect();
            PdrState { assignments }
        })
        .collect()
}
