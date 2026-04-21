// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared scratch buffers and counters for the BVE body helpers.

use super::super::super::*;

#[derive(Default)]
pub(super) struct BveBodyStats {
    pub total_eliminations: usize,
    pub bw_subsumed_total: u64,
    pub bw_strengthened_total: u64,
    pub bw_checks_total: u64,
    pub resolvents_total: u64,
}

#[derive(Default)]
pub(super) struct BveBodyScratch {
    pub pos_occs: Vec<usize>,
    pub neg_occs: Vec<usize>,
    pub kept_strengthened: Vec<usize>,
    pub sat_buf: Vec<usize>,
    pub old_lits_buf: Vec<Literal>,
    pub new_lits_buf: Vec<Literal>,
    pub add_buf: Vec<Literal>,
    pub otfs_old_clauses: Vec<(usize, Literal, Vec<Literal>)>,
}
