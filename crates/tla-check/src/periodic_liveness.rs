// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared TLC-style periodic liveness gating state.
//!
//! Used by both the sequential BFS loop and the parallel finalize loop so the
//! growth/interval/runtime-budget policy stays identical across both paths.

use std::time::{Duration, Instant};

/// TLC-style periodic liveness checking state.
#[derive(Clone, Debug)]
pub(crate) struct PeriodicLivenessState {
    /// Number of seen states at the time of the last periodic liveness check.
    pub(crate) states_at_last_check: usize,
    /// Cumulative wall-clock time (milliseconds) spent on periodic liveness checks.
    pub(crate) cumulative_check_time_ms: u64,
    /// Wall-clock time of the last periodic liveness check attempt.
    pub(crate) last_check_time: Option<Instant>,
    /// Minimum growth fraction required since the last check.
    pub(crate) growth_threshold: f64,
    /// Maximum fraction of total runtime periodic liveness may consume.
    pub(crate) time_budget_ratio: f64,
    /// Minimum interval between periodic liveness checks.
    pub(crate) check_interval_ms: u64,
}

impl Default for PeriodicLivenessState {
    fn default() -> Self {
        Self {
            states_at_last_check: 0,
            cumulative_check_time_ms: 0,
            last_check_time: None,
            // TLC defaults: 10% growth threshold, 20% time budget, 60s interval.
            growth_threshold: 0.1,
            time_budget_ratio: 0.2,
            check_interval_ms: 60_000,
        }
    }
}

impl PeriodicLivenessState {
    pub(crate) fn should_run(
        &self,
        now: Instant,
        bfs_start: Instant,
        current_states: usize,
    ) -> bool {
        if current_states == 0 {
            return false;
        }

        let since_last = self.last_check_time.map_or_else(
            || now.saturating_duration_since(bfs_start),
            |last| now.saturating_duration_since(last),
        );
        if since_last.as_millis() < u128::from(self.check_interval_ms) {
            return false;
        }

        if self.states_at_last_check > 0
            && self.growth_since_last_check(current_states) < self.growth_threshold
        {
            return false;
        }

        let total_elapsed = now.saturating_duration_since(bfs_start);
        self.budget_ratio(total_elapsed) <= self.time_budget_ratio
    }

    pub(crate) fn growth_since_last_check(&self, current_states: usize) -> f64 {
        if self.states_at_last_check == 0 {
            return 1.0;
        }
        current_states.saturating_sub(self.states_at_last_check) as f64
            / self.states_at_last_check as f64
    }

    pub(crate) fn budget_ratio(&self, total_elapsed: Duration) -> f64 {
        let total_elapsed_ms = total_elapsed.as_millis();
        if total_elapsed_ms == 0 {
            return 0.0;
        }
        self.cumulative_check_time_ms as f64 / total_elapsed_ms as f64
    }

    pub(crate) fn record_run(
        &mut self,
        finished_at: Instant,
        current_states: usize,
        duration: Duration,
    ) {
        let duration_ms = u64::try_from(duration.as_millis()).unwrap_or(u64::MAX);
        self.cumulative_check_time_ms = self.cumulative_check_time_ms.saturating_add(duration_ms);
        self.states_at_last_check = current_states;
        self.last_check_time = Some(finished_at);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn periodic_liveness_first_run_respects_interval() {
        let start = Instant::now();
        let state = PeriodicLivenessState::default();
        assert!(!state.should_run(start, start, 10));
    }

    #[test]
    fn periodic_liveness_requires_growth_after_first_run() {
        let start = Instant::now();
        let mut state = PeriodicLivenessState {
            check_interval_ms: 0,
            ..Default::default()
        };
        assert!(state.should_run(start, start, 100));

        state.record_run(start, 100, Duration::from_millis(10));
        assert!(!state.should_run(start, start, 105));
        assert!(state.should_run(start, start, 111));
    }

    #[test]
    fn periodic_liveness_budget_blocks_over_limit() {
        let start = Instant::now();
        let state = PeriodicLivenessState {
            cumulative_check_time_ms: 300,
            time_budget_ratio: 0.2,
            check_interval_ms: 0,
            ..Default::default()
        };
        assert!(!state.should_run(
            start,
            start
                .checked_sub(Duration::from_millis(1_000))
                .unwrap_or(start),
            100
        ));
    }
}
