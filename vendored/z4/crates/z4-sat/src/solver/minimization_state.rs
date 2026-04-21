// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause minimization and LRAT chain work arrays (#5090).
//!
//! Groups conflict analysis minimization state into a single struct to
//! separate it from the Solver's hot BCP fields. These arrays are only
//! accessed during conflict analysis (per-conflict, not per-propagation).

/// Clause minimization and LRAT chain work arrays (reused per-conflict).
///
/// Contains the packed minimize flags, per-level tracking arrays, and
/// LRAT chain support. All accessed only during conflict analysis and
/// clause minimization, never during BCP.
///
/// Reference: CaDiCaL `minimize.cpp`, `level.hpp` (seen tracking).
pub(crate) struct MinimizationState {
    /// Packed minimize flags per variable. Access via `MIN_*` constants.
    /// Bits: poison(0x01), removable(0x02), visited(0x04), keep(0x08),
    /// LRAT_A(0x10), LRAT_B(0x20).
    pub minimize_flags: Vec<u8>,
    /// List of variable indices to clear after minimization.
    pub minimize_to_clear: Vec<usize>,
    /// Per-level count of seen literals during conflict analysis
    /// (CaDiCaL level.hpp:seen.count). Used by minimize early-abort.
    pub level_seen_count: Vec<u32>,
    /// Per-level minimum trail position among seen literals
    /// (CaDiCaL level.hpp:seen.trail). Used by minimize early-abort.
    pub level_seen_trail: Vec<usize>,
    /// Dirty list of decision levels touched during analysis (for cleanup).
    pub level_seen_to_clear: Vec<u32>,
    /// Sparse cleanup list for LRAT bits in minimize_flags.
    pub lrat_to_clear: Vec<usize>,
    /// Maximum recursion depth for minimization.
    pub minimize_depth_limit: u32,
    /// Per-level count of seen literals in the learned clause
    /// (CaDiCaL l.seen.count).
    pub minimize_level_count: Vec<u32>,
    /// Per-level earliest trail position of a seen literal
    /// (CaDiCaL l.seen.trail).
    pub minimize_level_trail: Vec<usize>,
    /// Sparse cleanup list for minimize_level_count/trail.
    pub minimize_levels_to_clear: Vec<u32>,
}

impl MinimizationState {
    /// Create minimization state for `num_vars` variables.
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            minimize_flags: vec![0u8; num_vars],
            minimize_to_clear: Vec::with_capacity(num_vars),
            level_seen_count: Vec::new(),
            level_seen_trail: Vec::new(),
            level_seen_to_clear: Vec::new(),
            lrat_to_clear: Vec::with_capacity(num_vars),
            minimize_depth_limit: 1000, // CaDiCaL default
            minimize_level_count: vec![0; num_vars + 1],
            minimize_level_trail: vec![usize::MAX; num_vars + 1],
            minimize_levels_to_clear: Vec::with_capacity(64),
        }
    }
}
