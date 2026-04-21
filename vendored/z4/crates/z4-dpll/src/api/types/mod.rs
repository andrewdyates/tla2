// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Type definitions for the Z4 Solver API.
//!
//! This module re-exports all public API types from focused submodules.
//! The public surface is source-compatible with the former single-file layout.

mod cross_check;
mod error;
mod handles;
mod logic;
mod model;
mod model_value;
mod model_value_display;
mod results;
mod verification;

// Re-export all public types to preserve the existing `types::*` surface.
pub use cross_check::{CrossCheckDisagreement, CrossCheckReport, CrossCheckRun, CrossCheckVariant};
pub use error::SolverError;
pub use handles::{FuncDecl, Term};
pub use logic::{Logic, SortExt};
pub use model::{Model, VerifiedModel};
pub use model_value::{FpSpecialKind, ModelValue};
pub use results::{ConsumerAcceptanceError, SolveResult, VerifiedSolveResult};
pub use verification::{
    AssumptionSolveDetails, SolveDetails, VerificationLevel, VerificationSummary,
};
