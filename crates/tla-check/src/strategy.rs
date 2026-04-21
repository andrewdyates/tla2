// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adaptive strategy selection types and heuristics.
//!
//! Contains the pure logic for deciding between sequential and parallel
//! model checking based on pilot-phase analysis of spec characteristics.

/// Thresholds for adaptive parallelism decisions
pub(crate) const PARALLEL_THRESHOLD: usize = 20_000; // Use parallel if estimated states > this
pub(crate) const MEDIUM_SPEC_THRESHOLD: usize = 200_000; // Use 2 workers if estimated < this
pub(crate) const LARGE_SPEC_THRESHOLD: usize = 1_000_000; // Use 4 workers if estimated < this
pub(crate) const PILOT_SAMPLE_SIZE: usize = 50; // Number of states to sample in pilot phase

/// Strategy selected by adaptive checker
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Strategy {
    /// Use sequential checker (no parallelism overhead)
    Sequential,
    /// Use parallel checker with specified worker count
    Parallel(usize),
}

impl std::fmt::Display for Strategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Strategy::Sequential => write!(f, "sequential"),
            Strategy::Parallel(n) => write!(f, "parallel ({} workers)", n),
        }
    }
}

/// Result of pilot phase analysis
#[derive(Debug, Clone)]
pub struct PilotAnalysis {
    /// Number of initial states
    pub initial_states: usize,
    /// Average branching factor (successors per state)
    pub avg_branching_factor: f64,
    /// Estimated total state space size
    pub estimated_states: usize,
    /// Selected execution strategy
    pub strategy: Strategy,
    /// Number of states sampled during pilot
    pub states_sampled: usize,
}

/// Estimate total state space size based on initial states and branching factor
///
/// Part of #617: Uses exponential growth model for medium+ branching factors.
/// The estimate assumes ~8 levels of BFS exploration, which is typical for
/// model checking specs. For low branching factors (b ≈ 1), we use a high
/// fixed multiplier since depth is unknown but could be arbitrarily large.
pub(crate) fn estimate_state_space(initial_states: usize, branching_factor: f64) -> usize {
    if branching_factor < 0.5 {
        // Mostly terminal states, spec is likely small
        return (initial_states as f64 * 10.0) as usize;
    }

    if branching_factor < 1.5 {
        // Part of #617: Sequential/linear growth - could be arbitrarily deep.
        // A counter from 0 to 1M has b≈1 but needs parallel mode.
        // Use high estimate to ensure parallel is considered.
        return (initial_states as f64 * 50000.0) as usize;
    }

    // For b >= 1.5, use exponential estimate: initial * b^depth
    // Assume typical depth of 8 levels for BFS exploration.
    // This gives:
    //   b=2: 2^8 = 256
    //   b=6: 6^8 = 1,679,616 (matches SimpleCounter_huge ~1.77M states)
    //   b=10: 10^8 = 100,000,000
    let depth_estimate = 8.0;
    let growth = branching_factor.powf(depth_estimate);
    let estimate = initial_states as f64 * growth;

    // Cap at 10^9 to avoid overflow and unrealistic estimates
    estimate.min(1e9) as usize
}

/// Select execution strategy based on estimated state space.
///
/// Part of #2955: Caps at 8 workers by default.
///
/// Re: #3202 (2026-03-14 Category C scaling matrix):
/// - MCKVSSafetySmall: TLA2 parallel scaling is weak (~1.4x at 8 workers,
///   vs TLC ~3.5x). Single-worker gap is ~0.65x TLC.
/// - MCBoulanger: parallel mode degrades at 2+ workers (timeout/crash).
/// - Thresholds kept unchanged. The parallel bottleneck must be resolved
///   before adjusting the selector. See:
///   reports/perf/issue-3202-category-c-parallel-scaling-current.md
pub(crate) fn select_strategy(estimated_states: usize, available_cores: usize) -> Strategy {
    // Cap at 8 workers. #3202 shows even 8 workers provides only ~1.4x
    // speedup on MCKVSSafetySmall — the bottleneck is not the cap.
    let max_workers = 8.min(available_cores);
    if estimated_states < PARALLEL_THRESHOLD {
        Strategy::Sequential
    } else if estimated_states < MEDIUM_SPEC_THRESHOLD {
        Strategy::Parallel(2.min(available_cores))
    } else if estimated_states < LARGE_SPEC_THRESHOLD {
        Strategy::Parallel(4.min(available_cores))
    } else {
        Strategy::Parallel(max_workers)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_estimate_state_space() {
        // Very low branching factor (b < 0.5) - mostly terminal states
        let estimate = estimate_state_space(10, 0.3);
        assert_eq!(estimate, 100); // 10 * 10

        // Low branching factor (0.5 <= b < 1.5) - sequential specs may be deep
        // Part of #617: Use 50000 multiplier to ensure parallel is considered
        let estimate = estimate_state_space(10, 1.0);
        assert_eq!(estimate, 500000); // 10 * 50000

        // Part of #617: For b >= 1.5, use exponential formula: initial * b^8
        // Medium branching factor (b = 2.0): 10 * 2^8 = 10 * 256 = 2560
        let estimate = estimate_state_space(10, 2.0);
        assert_eq!(estimate, 2560);

        // Higher branching factor (b = 5.0): 10 * 5^8 = 10 * 390625 = 3,906,250
        let estimate = estimate_state_space(10, 5.0);
        assert_eq!(estimate, 3906250);

        // Very high branching factor (b = 15.0): 10 * 15^8 = 25.6B → capped at 1B
        let estimate = estimate_state_space(10, 15.0);
        assert_eq!(estimate, 1_000_000_000);
    }

    #[test]
    fn test_estimate_state_space_boundary_conditions() {
        // Boundary: b = 0.5 exactly falls into the linear multiplier branch
        let at_boundary = estimate_state_space(10, 0.5);
        assert_eq!(at_boundary, 500000); // 10 * 50000 (0.5 >= 0.5, enters second branch)

        // Just below boundary: b = 0.499 stays in terminal branch
        let below = estimate_state_space(10, 0.499);
        assert_eq!(below, 100); // 10 * 10 (< 0.5, enters first branch)

        // Boundary: b = 1.5 exactly falls into exponential branch
        let at_exp = estimate_state_space(10, 1.5);
        // 10 * 1.5^8 = 10 * 25.628... = 256
        assert_eq!(at_exp, 256); // 1.5 >= 1.5, enters third branch

        // Just below: b = 1.499 stays in linear branch
        let below_exp = estimate_state_space(10, 1.499);
        assert_eq!(below_exp, 500000); // < 1.5, stays in second branch

        // Edge case: initial_states = 0
        assert_eq!(estimate_state_space(0, 5.0), 0);

        // Edge case: initial_states = 1
        assert_eq!(estimate_state_space(1, 2.0), 256); // 1 * 2^8
    }

    #[test]
    fn test_select_strategy() {
        // Small specs get sequential
        assert_eq!(select_strategy(500, 8), Strategy::Sequential);

        // Medium specs get 2 workers
        assert_eq!(select_strategy(30000, 8), Strategy::Parallel(2));

        // Large specs get 4 workers
        assert_eq!(select_strategy(300000, 8), Strategy::Parallel(4));

        // Very large specs get up to 8 workers (capped per #2955)
        assert_eq!(select_strategy(1500000, 8), Strategy::Parallel(8));

        // Respect available cores limit
        assert_eq!(select_strategy(1500000, 2), Strategy::Parallel(2));

        // Cap at 8 even when more cores available (Part of #2955)
        assert_eq!(select_strategy(1500000, 16), Strategy::Parallel(8));
    }

    #[test]
    fn test_select_strategy_boundary_conditions() {
        // At PARALLEL_THRESHOLD exactly: should switch to Parallel
        assert_eq!(
            select_strategy(PARALLEL_THRESHOLD, 8),
            Strategy::Parallel(2)
        );
        // Just below: still Sequential
        assert_eq!(
            select_strategy(PARALLEL_THRESHOLD - 1, 8),
            Strategy::Sequential
        );

        // At MEDIUM_SPEC_THRESHOLD exactly: should switch to 4 workers
        assert_eq!(
            select_strategy(MEDIUM_SPEC_THRESHOLD, 8),
            Strategy::Parallel(4)
        );
        // Just below: still 2 workers
        assert_eq!(
            select_strategy(MEDIUM_SPEC_THRESHOLD - 1, 8),
            Strategy::Parallel(2)
        );

        // At LARGE_SPEC_THRESHOLD exactly: should switch to max workers (capped at 8)
        assert_eq!(
            select_strategy(LARGE_SPEC_THRESHOLD, 8),
            Strategy::Parallel(8)
        );
        // Just below: still 4 workers
        assert_eq!(
            select_strategy(LARGE_SPEC_THRESHOLD - 1, 8),
            Strategy::Parallel(4)
        );

        // Edge case: 0 estimated states
        assert_eq!(select_strategy(0, 8), Strategy::Sequential);

        // Edge case: 1 available core clamps parallel to 1
        assert_eq!(
            select_strategy(PARALLEL_THRESHOLD, 1),
            Strategy::Parallel(1)
        );
    }
}
