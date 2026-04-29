// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for SetPred (set filter) handling in the model checker.
//!
//! SetPred values arise from `{x \in S : P(x)}` expressions where `S` is a lazy
//! set (e.g., `SUBSET`, `FuncSet`). These tests verify that SetPred values are
//! correctly materialized throughout the model checker pipeline:
//! - Enumeration (unified.rs, symbolic_assignments.rs)
//! - Membership checks (eval_membership.rs)
//! - Fingerprint identity (UNCHANGED, state comparison)
//! - Invariant evaluation
//! - Init constraint extraction

use super::*;

mod enumeration;
mod guard_and_errors;
mod materialization;
mod state_values;
