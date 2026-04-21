// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Capture-aware substitution utilities for TLA+ expressions.
//!
//! This module provides centralized utilities for:
//! - Tracking bound variable names during AST traversal
//! - Computing free variables in expressions
//! - Checking if a substitution would cause variable capture
//!
//! These utilities are used by compiled guards, evaluation, and other
//! subsystems that need to perform capture-safe AST rewrites.
//!
//! Design: `designs/2026-01-30-centralize-capture-aware-substitution-utilities.md`

mod bound_name_stack;
mod capture;
pub(crate) mod free_vars;

#[cfg(test)]
mod tests;

pub use bound_name_stack::BoundNameStack;
pub use capture::{inlining_is_capture_safe, substitution_would_capture};
pub use free_vars::free_vars;
