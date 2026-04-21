// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared preparation helpers for sequential and parallel model checkers.
//!
//! This module is the stable re-export surface for checker setup operations.
//! Both checker paths call these functions to prevent parity drift (the same
//! class of bug that caused #2787).
//!
//! Internal responsibilities are split into child modules:
//! - `operator_setup`: scalar setup helpers (VIEW, expand, inline NEXT, ASSUME)
//! - `module_graph`: import traversal and canonical ops/vars/ASSUME collection
//! - `load`: canonical `EvalCtx` module loading order
//!
//! Part of #810: shared checker setup pipeline.

mod load;
mod module_graph;
mod operator_setup;

pub(crate) use load::load_modules_into_ctx;
pub(crate) use module_graph::collect_ops_vars_and_assumes;
pub(crate) use operator_setup::{
    check_assumes, expand_operator_body, expand_operator_body_with_primes, lower_inline_next,
    validate_view_operator,
};
