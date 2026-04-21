// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adaptive lane timeout budgets for the fused orchestrator.
//!
//! Each lane (BFS, BMC, PDR) gets an independent time budget that adapts
//! based on observed progress. Lanes making progress get 25% more budget;
//! stalled lanes lose 50%. This prevents resource waste on stuck engines
//! while letting productive engines run longer.
//!
//! Part of #3841, Epic #3830 (Perfection Plan).

use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

/// Identifies one of the three cooperative verification lanes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Lane {
    Bfs,
    Bmc,
    Pdr,
}

/// Manages per-lane adaptive time budgets for the fused orchestrator.
///
/// Budget adjustment policy:
/// - **Progress detected**: increase budget by 25% (capped at `max_budget`)
/// - **No progress**: decrease budget by 50% (floored at `min_budget`)
///
/// Progress is measured by comparing current metric snapshots against
/// previous values:
/// - BFS: number of distinct states discovered
/// - BMC: maximum bounded depth reached
/// - PDR: number of inductive lemmas learned
pub(crate) struct LaneBudgetManager {
    bfs_budget_ms: AtomicU64,
    bmc_budget_ms: AtomicU64,
    pdr_budget_ms: AtomicU64,
    min_budget: Duration,
    max_budget: Duration,
    eval_interval: Duration,
    last_eval: Instant,
    // Snapshots for progress detection
    last_bfs_states: u64,
    last_bmc_depth: u64,
    last_pdr_lemmas: u64,
}

/// Growth factor applied when a lane shows progress (1.25x).
const PROGRESS_GROWTH_FACTOR: f64 = 1.25;

/// Decay factor applied when a lane shows no progress (0.5x).
const STALL_DECAY_FACTOR: f64 = 0.5;

impl LaneBudgetManager {
    /// Create a new budget manager with the given parameters.
    ///
    /// Defaults: `initial_budget` = 30s, `min_budget` = 5s,
    /// `max_budget` = 300s, `eval_interval` = 10s.
    pub(crate) fn new(
        initial_budget: Duration,
        min_budget: Duration,
        max_budget: Duration,
        eval_interval: Duration,
    ) -> Self {
        let initial_ms = initial_budget.as_millis() as u64;
        Self {
            bfs_budget_ms: AtomicU64::new(initial_ms),
            bmc_budget_ms: AtomicU64::new(initial_ms),
            pdr_budget_ms: AtomicU64::new(initial_ms),
            min_budget,
            max_budget,
            eval_interval,
            last_eval: Instant::now(),
            last_bfs_states: 0,
            last_bmc_depth: 0,
            last_pdr_lemmas: 0,
        }
    }

    /// Create a budget manager with reasonable default parameters.
    ///
    /// - Initial budget: 30 seconds per lane
    /// - Minimum budget: 5 seconds (prevents total starvation)
    /// - Maximum budget: 300 seconds (prevents unbounded growth)
    /// - Evaluation interval: 10 seconds between budget adjustments
    #[must_use]
    pub(crate) fn with_defaults() -> Self {
        Self::new(
            Duration::from_secs(30),
            Duration::from_secs(5),
            Duration::from_secs(300),
            Duration::from_secs(10),
        )
    }

    /// Read the current budget for the given lane.
    #[must_use]
    pub(crate) fn budget_for(&self, lane: Lane) -> Duration {
        let ms = match lane {
            Lane::Bfs => self.bfs_budget_ms.load(Ordering::Relaxed),
            Lane::Bmc => self.bmc_budget_ms.load(Ordering::Relaxed),
            Lane::Pdr => self.pdr_budget_ms.load(Ordering::Relaxed),
        };
        Duration::from_millis(ms)
    }

    /// Update budgets based on observed progress metrics.
    ///
    /// Compares current values against the last snapshot. If any metric
    /// increased, the corresponding lane budget grows by 25%. If a metric
    /// is unchanged, the budget shrinks by 50%.
    ///
    /// Returns `true` if an update was performed (enough time has elapsed
    /// since the last evaluation), `false` if skipped.
    pub(crate) fn update(&mut self, bfs_states: u64, bmc_depth: u64, pdr_lemmas: u64) -> bool {
        let now = Instant::now();
        if now.duration_since(self.last_eval) < self.eval_interval {
            return false;
        }
        self.last_eval = now;

        let min_ms = self.min_budget.as_millis() as u64;
        let max_ms = self.max_budget.as_millis() as u64;

        // BFS lane
        self.adjust_lane(
            &self.bfs_budget_ms,
            bfs_states > self.last_bfs_states,
            min_ms,
            max_ms,
        );
        self.last_bfs_states = bfs_states;

        // BMC lane
        self.adjust_lane(
            &self.bmc_budget_ms,
            bmc_depth > self.last_bmc_depth,
            min_ms,
            max_ms,
        );
        self.last_bmc_depth = bmc_depth;

        // PDR lane
        self.adjust_lane(
            &self.pdr_budget_ms,
            pdr_lemmas > self.last_pdr_lemmas,
            min_ms,
            max_ms,
        );
        self.last_pdr_lemmas = pdr_lemmas;

        true
    }

    /// Override the budget for a specific lane, clamping to [min, max].
    pub(crate) fn force_budget(&self, lane: Lane, budget: Duration) {
        let ms = (budget.as_millis() as u64).clamp(
            self.min_budget.as_millis() as u64,
            self.max_budget.as_millis() as u64,
        );
        let atomic = match lane {
            Lane::Bfs => &self.bfs_budget_ms,
            Lane::Bmc => &self.bmc_budget_ms,
            Lane::Pdr => &self.pdr_budget_ms,
        };
        atomic.store(ms, Ordering::Relaxed);
    }

    /// Adjust a single lane's budget based on whether progress was detected.
    fn adjust_lane(&self, budget_ms: &AtomicU64, made_progress: bool, min_ms: u64, max_ms: u64) {
        let current = budget_ms.load(Ordering::Relaxed);
        let new_ms = if made_progress {
            let grown = (current as f64 * PROGRESS_GROWTH_FACTOR) as u64;
            grown.min(max_ms)
        } else {
            let decayed = (current as f64 * STALL_DECAY_FACTOR) as u64;
            decayed.max(min_ms)
        };
        budget_ms.store(new_ms, Ordering::Relaxed);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lane_budget_defaults() {
        let mgr = LaneBudgetManager::with_defaults();
        assert_eq!(mgr.budget_for(Lane::Bfs), Duration::from_secs(30));
        assert_eq!(mgr.budget_for(Lane::Bmc), Duration::from_secs(30));
        assert_eq!(mgr.budget_for(Lane::Pdr), Duration::from_secs(30));
    }

    #[test]
    fn test_lane_budget_custom_initial() {
        let mgr = LaneBudgetManager::new(
            Duration::from_secs(10),
            Duration::from_secs(1),
            Duration::from_secs(60),
            Duration::from_secs(5),
        );
        assert_eq!(mgr.budget_for(Lane::Bfs), Duration::from_secs(10));
        assert_eq!(mgr.budget_for(Lane::Bmc), Duration::from_secs(10));
        assert_eq!(mgr.budget_for(Lane::Pdr), Duration::from_secs(10));
    }

    #[test]
    fn test_lane_budget_progress_increases_budget() {
        let mut mgr = LaneBudgetManager::new(
            Duration::from_millis(1000),
            Duration::from_millis(100),
            Duration::from_millis(10000),
            Duration::from_millis(0), // zero interval so update always fires
        );
        let updated = mgr.update(100, 0, 0);
        assert!(updated);
        // BFS made progress: 1000 * 1.25 = 1250
        assert_eq!(mgr.budget_for(Lane::Bfs), Duration::from_millis(1250));
        // BMC and PDR stalled: 1000 * 0.5 = 500
        assert_eq!(mgr.budget_for(Lane::Bmc), Duration::from_millis(500));
        assert_eq!(mgr.budget_for(Lane::Pdr), Duration::from_millis(500));
    }

    #[test]
    fn test_lane_budget_stall_decreases_budget() {
        let mut mgr = LaneBudgetManager::new(
            Duration::from_millis(1000),
            Duration::from_millis(100),
            Duration::from_millis(10000),
            Duration::from_millis(0),
        );
        // First call with no progress
        mgr.update(0, 0, 0);
        assert_eq!(mgr.budget_for(Lane::Bfs), Duration::from_millis(500));
        // Second call still no progress
        mgr.update(0, 0, 0);
        assert_eq!(mgr.budget_for(Lane::Bfs), Duration::from_millis(250));
    }

    #[test]
    fn test_lane_budget_respects_minimum() {
        let mut mgr = LaneBudgetManager::new(
            Duration::from_millis(200),
            Duration::from_millis(100),
            Duration::from_millis(10000),
            Duration::from_millis(0),
        );
        // 200 * 0.5 = 100 (at minimum)
        mgr.update(0, 0, 0);
        assert_eq!(mgr.budget_for(Lane::Bfs), Duration::from_millis(100));
        // Should not go below minimum
        mgr.update(0, 0, 0);
        assert_eq!(mgr.budget_for(Lane::Bfs), Duration::from_millis(100));
    }

    #[test]
    fn test_lane_budget_respects_maximum() {
        let mut mgr = LaneBudgetManager::new(
            Duration::from_millis(9000),
            Duration::from_millis(100),
            Duration::from_millis(10000),
            Duration::from_millis(0),
        );
        // 9000 * 1.25 = 11250, clamped to 10000
        mgr.update(100, 0, 0);
        assert_eq!(mgr.budget_for(Lane::Bfs), Duration::from_millis(10000));
        // Still capped
        mgr.update(200, 0, 0);
        assert_eq!(mgr.budget_for(Lane::Bfs), Duration::from_millis(10000));
    }

    #[test]
    fn test_lane_budget_eval_interval_throttle() {
        let mut mgr = LaneBudgetManager::new(
            Duration::from_millis(1000),
            Duration::from_millis(100),
            Duration::from_millis(10000),
            Duration::from_secs(60), // 60s interval — won't fire in test
        );
        let updated = mgr.update(100, 0, 0);
        assert!(!updated);
        // Budget should be unchanged
        assert_eq!(mgr.budget_for(Lane::Bfs), Duration::from_millis(1000));
    }

    #[test]
    fn test_lane_budget_force_override() {
        let mgr = LaneBudgetManager::new(
            Duration::from_millis(1000),
            Duration::from_millis(100),
            Duration::from_millis(10000),
            Duration::from_millis(0),
        );
        mgr.force_budget(Lane::Bmc, Duration::from_millis(5000));
        assert_eq!(mgr.budget_for(Lane::Bmc), Duration::from_millis(5000));
        // Other lanes unaffected
        assert_eq!(mgr.budget_for(Lane::Bfs), Duration::from_millis(1000));
    }

    #[test]
    fn test_lane_budget_force_clamps_to_min() {
        let mgr = LaneBudgetManager::new(
            Duration::from_millis(1000),
            Duration::from_millis(100),
            Duration::from_millis(10000),
            Duration::from_millis(0),
        );
        mgr.force_budget(Lane::Pdr, Duration::from_millis(10));
        assert_eq!(mgr.budget_for(Lane::Pdr), Duration::from_millis(100));
    }

    #[test]
    fn test_lane_budget_force_clamps_to_max() {
        let mgr = LaneBudgetManager::new(
            Duration::from_millis(1000),
            Duration::from_millis(100),
            Duration::from_millis(10000),
            Duration::from_millis(0),
        );
        mgr.force_budget(Lane::Bfs, Duration::from_millis(99999));
        assert_eq!(mgr.budget_for(Lane::Bfs), Duration::from_millis(10000));
    }

    #[test]
    fn test_lane_budget_independent_lanes() {
        let mut mgr = LaneBudgetManager::new(
            Duration::from_millis(1000),
            Duration::from_millis(100),
            Duration::from_millis(10000),
            Duration::from_millis(0),
        );
        // BFS progresses, BMC progresses, PDR stalls
        mgr.update(100, 5, 0);
        assert_eq!(mgr.budget_for(Lane::Bfs), Duration::from_millis(1250));
        assert_eq!(mgr.budget_for(Lane::Bmc), Duration::from_millis(1250));
        assert_eq!(mgr.budget_for(Lane::Pdr), Duration::from_millis(500));

        // Now BFS stalls, BMC stalls, PDR progresses
        mgr.update(100, 5, 3);
        assert_eq!(mgr.budget_for(Lane::Bfs), Duration::from_millis(625));
        assert_eq!(mgr.budget_for(Lane::Bmc), Duration::from_millis(625));
        assert_eq!(mgr.budget_for(Lane::Pdr), Duration::from_millis(625));
    }

    #[test]
    fn test_lane_budget_all_lanes_progress() {
        let mut mgr = LaneBudgetManager::new(
            Duration::from_millis(1000),
            Duration::from_millis(100),
            Duration::from_millis(10000),
            Duration::from_millis(0),
        );
        mgr.update(50, 3, 2);
        assert_eq!(mgr.budget_for(Lane::Bfs), Duration::from_millis(1250));
        assert_eq!(mgr.budget_for(Lane::Bmc), Duration::from_millis(1250));
        assert_eq!(mgr.budget_for(Lane::Pdr), Duration::from_millis(1250));
    }
}
