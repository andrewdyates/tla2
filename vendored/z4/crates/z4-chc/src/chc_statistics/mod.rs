// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Public CHC solver statistics.
//!
//! Exposes PDR/IC3 counters for external consumers (z4 binary `--stats` flag)
//! without leaking internal `SolverStats` or failure-analysis details.
//!
//! Part of #4710 — CHC/portfolio mode observability.

use crate::failure_analysis::SolverStats;

/// Statistics collected during a CHC solve attempt.
///
/// Returned by [`PdrSolver::solve_problem_with_statistics`] and
/// [`AdaptivePortfolio::solve_with_statistics`]. All fields are counters
/// accumulated during the solve; none are rates or derived metrics.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct ChcStatistics {
    /// Total PDR iterations (blocking + propagation rounds).
    pub iterations: u64,
    /// Number of inductive lemmas learned across all frames.
    pub lemmas_learned: u64,
    /// Maximum PDR frame depth reached.
    pub max_frame: u64,
    /// Number of PDR restarts triggered.
    pub restarts: u64,
    /// Number of SMT queries that returned Unknown.
    pub smt_unknowns: u64,
    /// Implication-cache hits (exact result reused, no solver call).
    pub cache_hits: u64,
    /// Implication-cache model rejections (fast rejection via cached model).
    pub cache_model_rejections: u64,
    /// Total SMT solver calls recorded by the implication cache.
    pub cache_solver_calls: u64,
}

impl From<SolverStats> for ChcStatistics {
    fn from(s: SolverStats) -> Self {
        Self {
            iterations: s.iterations as u64,
            lemmas_learned: s.lemmas_learned as u64,
            max_frame: s.max_frame as u64,
            restarts: s.restart_count as u64,
            smt_unknowns: s.smt_unknowns as u64,
            cache_hits: s.implication_cache_hits as u64,
            cache_model_rejections: s.implication_model_rejections as u64,
            cache_solver_calls: s.implication_solver_calls as u64,
        }
    }
}

impl ChcStatistics {
    /// Merge another `ChcStatistics` into this one (additive).
    ///
    /// Used by portfolio mode to aggregate stats across multiple engine runs.
    /// Uses saturating arithmetic to avoid overflow panics/wraparound on long runs.
    pub fn merge(&mut self, other: &Self) {
        self.iterations = self.iterations.saturating_add(other.iterations);
        self.lemmas_learned = self.lemmas_learned.saturating_add(other.lemmas_learned);
        self.max_frame = self.max_frame.max(other.max_frame);
        self.restarts = self.restarts.saturating_add(other.restarts);
        self.smt_unknowns = self.smt_unknowns.saturating_add(other.smt_unknowns);
        self.cache_hits = self.cache_hits.saturating_add(other.cache_hits);
        self.cache_model_rejections = self
            .cache_model_rejections
            .saturating_add(other.cache_model_rejections);
        self.cache_solver_calls = self
            .cache_solver_calls
            .saturating_add(other.cache_solver_calls);
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
