// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Liveness checker tests — split from monolithic tests.rs (5012 lines, 109 tests)
//!
//! Split into 16 themed files — Part of #2779

use super::*;

mod helpers;

mod basic_operations;
mod build_edges;
mod check_masks;
mod check_masks_batched;
mod check_masks_inline_cache;
mod collect_enabled_nodes;
mod enabled;
mod enabled_error_suppression;
mod enabled_symmetry;
mod eval_checks;
mod eval_enabled_array_fast;
mod eval_enabled_cached;
mod frontier_fast;
mod grouped;
mod grouped_ea_signature;
mod nested_extraction;
mod scc;
mod scc_ae_satisfaction;
