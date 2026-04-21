// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! BFS convergence tracking for oracle routing decisions.
//!
//! Records how many new (unique) states BFS discovers at each depth level.
//! When the rate of new state discovery drops, BFS is approaching the
//! fixed point and the oracle can route more work to symbolic engines.

/// Tracks BFS convergence rate for oracle routing decisions.
///
/// Records how many new (unique) states BFS discovers at each depth level.
/// When the rate of new state discovery drops, BFS is approaching the
/// fixed point and the oracle can route more work to symbolic engines.
///
/// Part of #3785.
pub(crate) struct ConvergenceTracker {
    /// (depth, new_states_at_depth, total_states_at_depth) tuples.
    /// Kept in order of increasing depth.
    history: Vec<(usize, u64, u64)>,
}

impl ConvergenceTracker {
    pub(crate) fn new() -> Self {
        Self {
            history: Vec::new(),
        }
    }

    /// Record new and total state counts at a BFS depth boundary.
    pub(crate) fn record(&mut self, depth: usize, new_states: u64, total_states: u64) {
        self.history.push((depth, new_states, total_states));
    }

    /// Compute the convergence rate from the most recent depth level.
    ///
    /// Returns the ratio of new states to total states at the most recent
    /// recorded depth. Returns `1.0` (fully productive) if no data exists.
    pub(crate) fn recent_convergence_rate(&self) -> f64 {
        if let Some(&(_depth, new_states, total_states)) = self.history.last() {
            if total_states == 0 {
                return 1.0;
            }
            new_states as f64 / total_states as f64
        } else {
            1.0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_convergence_tracker_no_data_returns_one() {
        let tracker = ConvergenceTracker::new();
        assert!(
            (tracker.recent_convergence_rate() - 1.0).abs() < f64::EPSILON,
            "empty tracker should return 1.0 convergence rate"
        );
    }

    #[test]
    fn test_convergence_tracker_records_and_computes_rate() {
        let mut tracker = ConvergenceTracker::new();
        tracker.record(1, 100, 100); // 100% new
        assert!((tracker.recent_convergence_rate() - 1.0).abs() < f64::EPSILON);
        tracker.record(2, 50, 150); // 50/150 = 0.333...
        let rate = tracker.recent_convergence_rate();
        assert!(
            (rate - 50.0 / 150.0).abs() < 1e-10,
            "expected ~0.333, got {rate}"
        );
        tracker.record(3, 5, 10000); // 5/10000 = 0.0005
        let rate = tracker.recent_convergence_rate();
        assert!((rate - 0.0005).abs() < 1e-10, "expected 0.0005, got {rate}");
    }

    #[test]
    fn test_convergence_tracker_zero_total_returns_one() {
        let mut tracker = ConvergenceTracker::new();
        tracker.record(1, 0, 0);
        assert!(
            (tracker.recent_convergence_rate() - 1.0).abs() < f64::EPSILON,
            "zero total should return 1.0 to avoid division by zero"
        );
    }
}
