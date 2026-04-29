// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Coverage Statistics for Model Checking
//!
//! This module provides coverage tracking to help users understand which parts
//! of their specification were exercised during model checking.
//!
//! Coverage includes:
//! - **Action coverage**: Which disjuncts of Next generated transitions
//! - **Dead action detection**: Actions that never fired (potential spec issues)
//! - **Per-action statistics**: States and transitions per action
//! - **Coverage-guided exploration**: Priority-based frontier that directs
//!   exploration toward uncovered actions (enabled via `--coverage-guided`)

mod action_detection;
pub(crate) mod frontier;
pub(crate) mod guided;
mod stats;

pub use action_detection::{detect_actions, DetectedAction, DetectedActionId};
pub use stats::{ActionStats, CoverageStats};

#[cfg(test)]
mod tests;
