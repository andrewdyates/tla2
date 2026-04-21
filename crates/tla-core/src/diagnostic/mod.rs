// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Beautiful error rendering using ariadne
//!
//! This module provides rich, colorful diagnostic output for TLA+ errors.
//! It converts various error types to ariadne Reports for display.

// Many pub(crate) diagnostic helpers are defined but not yet wired into the
// main error pipeline. Suppress dead_code until LSP/diagnostic integration.
#![allow(dead_code)]

mod constructors;
mod render;
mod types;

#[cfg(test)]
mod tests;

// Public API re-exports (stable surface used by lib.rs and downstream crates)
pub use constructors::{lower_error_diagnostic, parse_error_diagnostic};
pub use types::{Diagnostic, DiagnosticLabel, DiagnosticSpan, LabelColor, Severity};

// Internal constructors and SourceCache are module-private — accessed
// by tests via `use super::constructors::*` or `use super::render::*`.
