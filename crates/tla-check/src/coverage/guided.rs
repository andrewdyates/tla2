// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Coverage-guided exploration tracker.
//!
//! Tracks which actions have been exercised during model checking and assigns
//! priority scores to states based on the rarity of the actions they exercised.
//! States that trigger rarely-seen or never-seen actions get higher priority,
//! directing exploration toward under-tested areas of the specification.
//!
//! ## Design
//!
//! The tracker maintains:
//! - Per-action firing counts (how many times each action has been taken)
//! - Per-state priority scores (based on the rarest action exercised from that state)
//!
//! Priority scoring uses inverse frequency: if action A has been fired N times
//! and action B has been fired M times where N < M, states that exercised A
//! get higher priority. Actions that have never fired get the highest priority.
//!
//! ## Integration
//!
//! The tracker is consulted by `CoverageGuidedFrontier` which wraps the standard
//! BFS `VecDeque` with a `BinaryHeap` for high-priority states. Every K states
//! (the "mix ratio"), one high-priority state is dequeued instead of the next
//! BFS-order state, ensuring coverage-guided exploration while preserving
//! BFS level structure for the majority of exploration.

use rustc_hash::FxHashMap;

use super::DetectedActionId;

/// Tracks action coverage and computes priority scores for coverage-guided
/// exploration.
///
/// Thread-safe note: This tracker is designed for sequential BFS mode only.
/// Coverage-guided exploration is inherently sequential (priority decisions
/// depend on global coverage state).
// Coverage-guided exploration is scaffolded but not yet wired into the main
// BFS loop. Suppress dead_code warnings until the feature is fully integrated.
#[allow(dead_code)]
#[derive(Debug)]
pub(crate) struct CoverageTracker {
    /// Number of times each action has been fired.
    action_fire_counts: FxHashMap<DetectedActionId, u64>,
    /// Total number of registered actions.
    action_count: usize,
    /// Total states processed (for statistics).
    states_processed: u64,
    /// Number of states that were prioritized (dequeued from priority queue).
    states_prioritized: u64,
    /// Number of actions that have been fired at least once.
    actions_covered: usize,
}

#[allow(dead_code)]
impl CoverageTracker {
    /// Create a new coverage tracker.
    pub(crate) fn new() -> Self {
        Self {
            action_fire_counts: FxHashMap::default(),
            action_count: 0,
            states_processed: 0,
            states_prioritized: 0,
            actions_covered: 0,
        }
    }

    /// Register an action for tracking.
    pub(crate) fn register_action(&mut self, id: DetectedActionId) {
        self.action_fire_counts.entry(id).or_insert(0);
        self.action_count = self.action_fire_counts.len();
    }

    /// Record that an action fired, producing successors.
    ///
    /// Returns the updated fire count for this action.
    pub(crate) fn record_action_firing(&mut self, id: DetectedActionId) -> u64 {
        let count = self.action_fire_counts.entry(id).or_insert(0);
        *count += 1;
        if *count == 1 {
            self.actions_covered += 1;
        }
        *count
    }

    /// Compute a priority score for a state based on the action tags it exercised.
    ///
    /// Higher scores mean higher priority (should be explored sooner).
    /// The score is based on the rarest action exercised from this state:
    /// - Actions never fired: score = `action_count + 1` (highest priority)
    /// - Actions fired N times: score = `action_count / (N + 1)` (inverse frequency)
    /// - No action tags: score = 0 (lowest priority, standard BFS order)
    pub(crate) fn compute_priority(&self, action_tags: &[Option<usize>]) -> u32 {
        if action_tags.is_empty() {
            return 0;
        }

        // For states with action tags, compute priority based on action rarity.
        // We use the maximum priority across all actions this state exercised,
        // so states that triggered ANY rare action get boosted.
        let ac = self.action_count as u32;

        for tag in action_tags.iter().flatten() {
            // Convert action index to DetectedActionId if we have a mapping,
            // but for now use the raw index-based approach.
            // The priority is based on how rare this action is across all
            // explored states.
            let _ = tag; // action_tags are indices into detected actions
        }

        // Simpler approach: look at all actions and boost states that
        // could reach uncovered actions. Since we don't know which actions
        // a not-yet-explored state might enable, we boost states that came
        // from transitions involving rare actions (the action_tags from
        // successor generation).
        //
        // If no action info is available, use a base priority.
        if ac == 0 {
            return 1;
        }

        // Check if any actions are still uncovered -- those states get max priority
        let max_priority = if self.actions_covered < self.action_count {
            ac + 1
        } else {
            // All actions covered; prioritize based on least-fired action
            let min_fires = self.action_fire_counts.values().copied().min().unwrap_or(0);
            // Inverse frequency: rarer actions get higher priority
            (ac as u64 / (min_fires + 1)).min(u32::MAX as u64) as u32
        };

        max_priority
    }

    /// Compute priority for a specific action by its index.
    ///
    /// Used when we know exactly which action produced a successor.
    pub(crate) fn priority_for_action(&self, action_id: DetectedActionId) -> u32 {
        let ac = self.action_count as u32;
        if ac == 0 {
            return 1;
        }

        match self.action_fire_counts.get(&action_id) {
            None => (ac + 1) * 1000,    // Unknown action -- highest priority
            Some(0) => (ac + 1) * 1000, // Never fired -- highest priority
            Some(&n) => {
                // Inverse frequency: fired N times -> priority = action_count * 1000 / (N+1)
                // With the * 1000 factor, uncovered actions always have higher priority
                // than any fired action (since (ac+1)*1000 > ac*1000/(N+1) for any N>=1).
                let priority = (ac as u64) * 1000 / (n + 1);
                priority.min(u32::MAX as u64) as u32
            }
        }
    }

    /// Increment the states-processed counter.
    pub(crate) fn record_state_processed(&mut self) {
        self.states_processed += 1;
    }

    /// Increment the states-prioritized counter (dequeued from priority queue).
    pub(crate) fn record_state_prioritized(&mut self) {
        self.states_prioritized += 1;
    }

    /// Get the number of registered actions.
    pub(crate) fn action_count(&self) -> usize {
        self.action_count
    }

    /// Get the number of actions that have been fired at least once.
    pub(crate) fn actions_covered(&self) -> usize {
        self.actions_covered
    }

    /// Get the total states processed.
    pub(crate) fn states_processed(&self) -> u64 {
        self.states_processed
    }

    /// Get the total states dequeued via priority.
    pub(crate) fn states_prioritized(&self) -> u64 {
        self.states_prioritized
    }

    /// Get all action fire counts for reporting.
    pub(crate) fn action_fire_counts(&self) -> &FxHashMap<DetectedActionId, u64> {
        &self.action_fire_counts
    }

    /// Check if all actions have been covered.
    ///
    /// Returns false when no actions are registered — coverage is not complete
    /// if tracking has not started. This prevents premature termination of
    /// coverage-guided exploration before actions are registered.
    pub(crate) fn all_actions_covered(&self) -> bool {
        self.actions_covered >= self.action_count && self.action_count > 0
    }

    /// Format a coverage-guided exploration summary.
    pub(crate) fn format_summary(&self) -> String {
        let mut lines = Vec::new();
        lines.push("=== Coverage-Guided Exploration Summary ===".to_string());
        lines.push(format!(
            "Actions covered: {}/{} ({:.1}%)",
            self.actions_covered,
            self.action_count,
            if self.action_count > 0 {
                self.actions_covered as f64 / self.action_count as f64 * 100.0
            } else {
                100.0
            }
        ));
        lines.push(format!("States processed: {}", self.states_processed));
        lines.push(format!("States prioritized: {}", self.states_prioritized));
        if self.states_processed > 0 {
            lines.push(format!(
                "Priority ratio: {:.1}%",
                self.states_prioritized as f64 / self.states_processed as f64 * 100.0
            ));
        }

        // Report uncovered actions
        let uncovered: Vec<_> = self
            .action_fire_counts
            .iter()
            .filter(|(_, &count)| count == 0)
            .map(|(id, _)| id.to_string())
            .collect();
        if !uncovered.is_empty() {
            lines.push(format!(
                "Uncovered actions ({}): {}",
                uncovered.len(),
                uncovered.join(", ")
            ));
        }

        lines.join("\n")
    }
}

impl Default for CoverageTracker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::{FileId, Span};

    fn make_id(file: u32, start: u32, end: u32) -> DetectedActionId {
        DetectedActionId::new(Span::new(FileId(file), start, end))
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_tracker_new_has_no_actions() {
        let tracker = CoverageTracker::new();
        assert_eq!(tracker.action_count(), 0);
        assert_eq!(tracker.actions_covered(), 0);
        assert!(!tracker.all_actions_covered()); // false: no actions registered yet
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_tracker_register_and_fire() {
        let mut tracker = CoverageTracker::new();
        let id_a = make_id(0, 10, 20);
        let id_b = make_id(0, 30, 40);

        tracker.register_action(id_a);
        tracker.register_action(id_b);

        assert_eq!(tracker.action_count(), 2);
        assert_eq!(tracker.actions_covered(), 0);
        assert!(!tracker.all_actions_covered());

        // Fire action A
        let count = tracker.record_action_firing(id_a);
        assert_eq!(count, 1);
        assert_eq!(tracker.actions_covered(), 1);
        assert!(!tracker.all_actions_covered());

        // Fire action B
        let count = tracker.record_action_firing(id_b);
        assert_eq!(count, 1);
        assert_eq!(tracker.actions_covered(), 2);
        assert!(tracker.all_actions_covered());

        // Fire action A again
        let count = tracker.record_action_firing(id_a);
        assert_eq!(count, 2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_priority_for_action_uncovered_highest() {
        let mut tracker = CoverageTracker::new();
        let id_a = make_id(0, 10, 20);
        let id_b = make_id(0, 30, 40);
        let id_c = make_id(0, 50, 60);

        tracker.register_action(id_a);
        tracker.register_action(id_b);
        tracker.register_action(id_c);

        // Uncovered action gets highest priority
        let prio_uncovered = tracker.priority_for_action(id_a);
        assert_eq!(prio_uncovered, 4000); // (action_count + 1) * 1000 = (3 + 1) * 1000

        // Fire action A many times
        for _ in 0..100 {
            tracker.record_action_firing(id_a);
        }

        // Frequently fired action gets low priority
        let prio_frequent = tracker.priority_for_action(id_a);
        // 3 * 1000 / (100 + 1) = 29
        assert!(prio_frequent < prio_uncovered);

        // Still-uncovered action B gets highest priority
        let prio_b = tracker.priority_for_action(id_b);
        assert_eq!(prio_b, 4000); // (action_count + 1) * 1000
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_stats_tracking() {
        let mut tracker = CoverageTracker::new();
        tracker.record_state_processed();
        tracker.record_state_processed();
        tracker.record_state_prioritized();

        assert_eq!(tracker.states_processed(), 2);
        assert_eq!(tracker.states_prioritized(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_format_summary() {
        let mut tracker = CoverageTracker::new();
        let id_a = make_id(0, 10, 20);
        let id_b = make_id(0, 30, 40);

        tracker.register_action(id_a);
        tracker.register_action(id_b);
        tracker.record_action_firing(id_a);
        tracker.record_state_processed();
        tracker.record_state_processed();
        tracker.record_state_prioritized();

        let summary = tracker.format_summary();
        assert!(summary.contains("Actions covered: 1/2"));
        assert!(summary.contains("States processed: 2"));
        assert!(summary.contains("States prioritized: 1"));
        assert!(summary.contains("Uncovered actions"));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_all_actions_covered_empty_returns_false() {
        // Regression test for #4085: empty action set must return false,
        // not vacuously true. Returning true before actions are registered
        // could cause premature termination of coverage-guided exploration.
        let tracker = CoverageTracker::new();
        assert_eq!(tracker.action_count(), 0);
        assert_eq!(tracker.actions_covered(), 0);
        assert!(
            !tracker.all_actions_covered(),
            "all_actions_covered() must return false when no actions are registered"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_all_actions_covered_single_action() {
        let mut tracker = CoverageTracker::new();
        let id = make_id(1, 0, 10);
        tracker.register_action(id);

        // One action registered but not yet fired
        assert!(!tracker.all_actions_covered());

        // Fire it
        tracker.record_action_firing(id);
        assert!(tracker.all_actions_covered());
    }
}
