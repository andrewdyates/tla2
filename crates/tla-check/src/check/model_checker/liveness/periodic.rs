// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::debug::liveness_profile;
use super::super::{CheckResult, ModelChecker};

impl<'a> ModelChecker<'a> {
    /// Attempt periodic liveness checking during BFS exploration.
    ///
    /// Part of #2752: Replicates TLC's `doPeriodicWork()` pattern. Called from
    /// the BFS loop at regular intervals. Delegates gating to the shared
    /// `PeriodicLivenessState::should_run()` which checks three conditions
    /// (matching TLC): minimum interval, growth threshold, and time budget.
    ///
    /// Soundness: SCC analysis on a partial graph is sound (no false positives)
    /// because `liveness_cache.successors` only contains fully-explored states
    /// with complete successor lists. Frontier states appear as sinks (no outgoing
    /// edges), so any cycle found is real. Incomplete (may miss violations until
    /// more states are explored), but the final post-BFS check catches those.
    ///
    /// **Critical invariant (#2929):** The `get_successors` callback in
    /// `check_liveness_property` must NOT add stuttering self-loops to frontier
    /// states (those without an entry in `cached_successors`). Adding stuttering
    /// to a frontier state creates a spurious single-node SCC where ENABLED
    /// evaluates against only the stuttering successor, causing false violations
    /// for specs with WF/SF fairness constraints.
    ///
    /// Returns `Some(CheckResult)` on liveness violation, `None` otherwise.
    pub(in crate::check::model_checker) fn maybe_periodic_liveness(
        &mut self,
        bfs_start_time: &std::time::Instant,
    ) -> Option<CheckResult> {
        // Fast exit: no liveness properties or caching disabled.
        if !self.liveness_cache.cache_for_liveness {
            return None;
        }

        let now = std::time::Instant::now();
        // Part of #3175: Use seen_fps.len() which works in both full and fp-only modes.
        let current_states = self.state_storage.seen_fps.len();

        // Part of #2752: Delegate gating to shared PeriodicLivenessState so
        // sequential and parallel paths use identical budget/interval/growth logic.
        if !self
            .periodic_liveness
            .should_run(now, *bfs_start_time, current_states)
        {
            return None;
        }

        // All gates passed — run liveness checking on the partial graph.
        let check_start = std::time::Instant::now();

        if liveness_profile() {
            let growth_pct = self
                .periodic_liveness
                .growth_since_last_check(current_states)
                * 100.0;
            eprintln!(
                "[periodic-liveness] Running mid-BFS liveness check ({current_states} states, growth {growth_pct:.1}% since last check)"
            );
        }

        let result = self.run_liveness_checking(true);

        // Part of #2752: Delegate state update to shared record_run().
        let finished_at = std::time::Instant::now();
        let duration = finished_at.saturating_duration_since(check_start);
        self.periodic_liveness
            .record_run(finished_at, current_states, duration);

        if liveness_profile() {
            let total_elapsed = now.saturating_duration_since(*bfs_start_time);
            let budget_pct = self.periodic_liveness.budget_ratio(total_elapsed) * 100.0;
            eprintln!(
                "[periodic-liveness] Check completed in {:.3}s (cumulative: {:.1}s, budget: {budget_pct:.1}%)",
                duration.as_secs_f64(),
                self.periodic_liveness.cumulative_check_time_ms as f64 / 1000.0,
            );
        }

        result
    }
}
