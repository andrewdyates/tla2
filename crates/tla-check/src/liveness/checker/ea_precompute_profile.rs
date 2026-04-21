// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Profiling output for populate_node_check_masks sub-phases (#3065).
//!
//! Gated behind `TLA2_LIVENESS_PROFILE=1`. Extracted from ea_precompute.rs
//! for code quality (eprintln waiver scope) and file size limits.

use std::time::Instant;

/// Profiling measurements collected during populate_node_check_masks.
pub(super) struct PopulateMasksProfile {
    pub(super) phase_start: Instant,
    pub(super) state_check_start: Instant,
    pub(super) action_check_start: Instant,
    pub(super) subscript_start: Instant,
    pub(super) eval_loop_start: Instant,
    pub(super) node_count: usize,
    pub(super) unique_state_count: usize,
    pub(super) state_used_count: usize,
    pub(super) state_total_count: usize,
    pub(super) unique_transition_count: usize,
    pub(super) by_from_group_count: usize,
    pub(super) subscript_skipped: bool,
    pub(super) cache_hit_transitions: usize,
    pub(super) fresh_eval_transitions: usize,
    pub(super) enabled_info_count: usize,
}

impl PopulateMasksProfile {
    pub(super) fn new() -> Self {
        let now = Instant::now();
        Self {
            phase_start: now,
            state_check_start: now,
            action_check_start: now,
            subscript_start: now,
            eval_loop_start: now,
            node_count: 0,
            unique_state_count: 0,
            state_used_count: 0,
            state_total_count: 0,
            unique_transition_count: 0,
            by_from_group_count: 0,
            subscript_skipped: false,
            cache_hit_transitions: 0,
            fresh_eval_transitions: 0,
            enabled_info_count: 0,
        }
    }

    /// Print profiling summary to stderr.
    pub(super) fn print(&self) {
        eprintln!(
            "    populate_masks: snapshot: {:.3}s (nodes={}, unique_states={})",
            self.state_check_start
                .duration_since(self.phase_start)
                .as_secs_f64(),
            self.node_count,
            self.unique_state_count,
        );
        eprintln!(
            "    populate_masks: state_checks: {:.3}s (used={}/{})",
            self.action_check_start
                .duration_since(self.state_check_start)
                .as_secs_f64(),
            self.state_used_count,
            self.state_total_count,
        );
        eprintln!(
            "    populate_masks: subscript_precompute: {:.3}s (skipped={}, transitions={}, groups={})",
            self.eval_loop_start.duration_since(self.subscript_start).as_secs_f64(),
            self.subscript_skipped,
            self.unique_transition_count,
            self.by_from_group_count,
        );
        eprintln!(
            "    populate_masks: eval_loop: {:.3}s (cache_hit={}, fresh_eval={}, enabled={})",
            self.eval_loop_start.elapsed().as_secs_f64(),
            self.cache_hit_transitions,
            self.fresh_eval_transitions,
            self.enabled_info_count,
        );
        eprintln!(
            "    populate_masks: total_action: {:.3}s",
            self.action_check_start.elapsed().as_secs_f64(),
        );
    }
}
