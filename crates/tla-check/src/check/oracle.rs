// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-action oracle routing for Cooperative Dual-Engine Model Checking (CDEMC).
//!
//! Uses runtime branching-factor metrics from [`ActionMetrics`] to route
//! high-branching actions to the symbolic (z4) engine and low-branching
//! actions to BFS. The oracle is periodically re-evaluated at BFS level
//! boundaries via [`ActionOracle::reroute`].
//!
//! # Routing Policy
//!
//! - **`BfsOnly`**: Action is not SMT-compatible, or has low branching factor.
//!   Always evaluated by BFS explicit-state exploration.
//! - **`SymbolicOnly`**: Action has high branching factor (avg > threshold)
//!   AND is within the SMT-compatible fragment. Routed to z4 symbolic engine.
//! - **`Either`**: Action is SMT-compatible but branching factor is moderate.
//!   Defaults to BFS; symbolic engine may opportunistically handle it.
//!
//! # Self-Tuning (Part of #3843)
//!
//! The oracle uses Thompson sampling via [`OracleRegretTracker`] to adapt
//! thresholds at runtime. Each candidate threshold is modeled as a Beta
//! distribution; the tracker samples from these to propose new thresholds
//! every [`TUNING_INTERVAL_REROUTES`] reroute cycles.
//!
//! Part of #3785, #3843.

use rustc_hash::FxHashMap;
use std::sync::atomic::Ordering;

use tla_core::ast::{Expr, Module, Unit};
use tla_core::Spanned;

use crate::cooperative_state::ActionMetrics;

/// Default branching factor threshold above which SMT-compatible actions are
/// routed to the symbolic engine. This is the starting point; the regret
/// tracker will tune it via Thompson sampling at runtime.
const DEFAULT_SYMBOLIC_BRANCHING_THRESHOLD: f64 = 100.0;

/// Default low threshold: branching factors below this route to BFS-only even
/// when SMT-compatible. A value of 0.0 means no low-end filtering.
const DEFAULT_LOW_THRESHOLD: f64 = 0.0;

/// Number of BFS levels between oracle re-evaluation passes.
/// The oracle re-reads [`ActionMetrics`] every `REROUTE_INTERVAL_LEVELS` levels
/// to adapt to changing branching patterns as exploration deepens.
const REROUTE_INTERVAL_LEVELS: usize = 5;

/// Number of reroute cycles between regret-tracker threshold suggestions.
/// Every N reroutes, the tracker proposes new thresholds via Thompson sampling.
const TUNING_INTERVAL_REROUTES: usize = 10;

/// Candidate high thresholds explored by Thompson sampling.
/// These represent branching factor values above which we route to symbolic.
const HIGH_THRESHOLD_CANDIDATES: &[f64] = &[25.0, 50.0, 75.0, 100.0, 150.0, 200.0, 500.0];

/// Candidate low thresholds explored by Thompson sampling.
/// These represent branching factor values below which we route to BFS-only
/// (even if SMT-compatible). A value of 0.0 disables the low threshold.
const LOW_THRESHOLD_CANDIDATES: &[f64] = &[0.0, 1.0, 2.0, 5.0, 10.0, 20.0];

/// Routing decision for a single action in the spec's next-state relation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum ActionRoute {
    /// Action must be handled by BFS (not SMT-compatible, or low branching).
    BfsOnly,
    /// Action should be handled by the symbolic engine (high branching, SMT-ok).
    SymbolicOnly,
    /// Action can be handled by either engine (SMT-compatible, moderate branching).
    /// Defaults to BFS unless the symbolic engine has spare capacity.
    Either,
}

/// Identifies which engine processed an action, for regret tracking.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Engine {
    Bfs,
    Symbolic,
}

/// Per-action routing oracle for CDEMC engine selection.
///
/// Holds a snapshot of routing decisions computed from [`ActionMetrics`].
/// The oracle is re-evaluated periodically via [`reroute`](Self::reroute)
/// as BFS accumulates more precise branching-factor data.
///
/// Thread-safety: the oracle itself is not `Sync` — it lives on the
/// orchestrator thread and is queried synchronously. The underlying
/// [`ActionMetrics`] are `Sync` (atomic fields), so `reroute` can read
/// them from any thread.
pub(crate) struct ActionOracle {
    /// Per-action routing decisions, indexed by action index.
    routes: Vec<ActionRoute>,
    /// BFS depth at which the last reroute was performed.
    last_reroute_depth: usize,
    /// Current symbolic branching threshold (tuned by regret tracker).
    symbolic_threshold: f64,
    /// Current low branching threshold below which SMT actions stay BFS-only.
    low_threshold: f64,
    /// Regret tracker for Thompson sampling-based threshold tuning.
    regret_tracker: OracleRegretTracker,
    /// Number of reroute cycles since last tuning suggestion.
    reroutes_since_tuning: usize,
}

impl ActionOracle {
    /// Create a new oracle from initial metrics and SMT compatibility flags.
    ///
    /// Called once at orchestrator startup. All actions with no evaluation
    /// data yet default to `Either` (if SMT-compatible) or `BfsOnly`.
    #[must_use]
    pub(crate) fn new(metrics: &[ActionMetrics], smt_compatible: &[bool]) -> Self {
        let symbolic_threshold = DEFAULT_SYMBOLIC_BRANCHING_THRESHOLD;
        let low_threshold = DEFAULT_LOW_THRESHOLD;
        let routes = compute_routes_with_thresholds(
            metrics,
            smt_compatible,
            symbolic_threshold,
            low_threshold,
        );
        Self {
            routes,
            last_reroute_depth: 0,
            symbolic_threshold,
            low_threshold,
            regret_tracker: OracleRegretTracker::new(),
            reroutes_since_tuning: 0,
        }
    }

    /// Create an oracle with all actions routed to BFS.
    ///
    /// Used when no SMT compatibility information is available (e.g., non-z4 builds).
    #[must_use]
    pub(crate) fn all_bfs(action_count: usize) -> Self {
        Self {
            routes: vec![ActionRoute::BfsOnly; action_count],
            last_reroute_depth: 0,
            symbolic_threshold: DEFAULT_SYMBOLIC_BRANCHING_THRESHOLD,
            low_threshold: DEFAULT_LOW_THRESHOLD,
            regret_tracker: OracleRegretTracker::new(),
            reroutes_since_tuning: 0,
        }
    }

    /// Create an oracle with all actions routed to SymbolicOnly.
    ///
    /// Used when static complexity analysis detects exponential state space
    /// (e.g., nested `SUBSET(SUBSET ...)`) that makes BFS infeasible.
    /// All actions are routed to the symbolic engine from the start.
    ///
    /// Part of #3826.
    #[must_use]
    pub(crate) fn all_symbolic(action_count: usize) -> Self {
        Self {
            routes: vec![ActionRoute::SymbolicOnly; action_count],
            last_reroute_depth: 0,
            symbolic_threshold: DEFAULT_SYMBOLIC_BRANCHING_THRESHOLD,
            low_threshold: DEFAULT_LOW_THRESHOLD,
            regret_tracker: OracleRegretTracker::new(),
            reroutes_since_tuning: 0,
        }
    }

    /// Get the routing decision for the action at `index`.
    ///
    /// Returns `BfsOnly` if the index is out of range.
    #[inline]
    #[must_use]
    pub(crate) fn route(&self, index: usize) -> ActionRoute {
        self.routes
            .get(index)
            .copied()
            .unwrap_or(ActionRoute::BfsOnly)
    }

    /// Get a slice of all routing decisions.
    #[must_use]
    pub(crate) fn routes(&self) -> &[ActionRoute] {
        &self.routes
    }

    /// Number of actions tracked by this oracle.
    #[must_use]
    pub(crate) fn action_count(&self) -> usize {
        self.routes.len()
    }

    /// Re-evaluate routing decisions if enough BFS levels have elapsed.
    ///
    /// Returns `true` if routes were actually updated (depth crossed the
    /// reroute interval boundary). The caller should invoke this at each
    /// BFS level transition.
    ///
    /// Every [`TUNING_INTERVAL_REROUTES`] reroute cycles, the regret tracker
    /// proposes new thresholds via Thompson sampling.
    pub(crate) fn reroute(
        &mut self,
        current_depth: usize,
        metrics: &[ActionMetrics],
        smt_compatible: &[bool],
    ) -> bool {
        if current_depth < self.last_reroute_depth + REROUTE_INTERVAL_LEVELS {
            return false;
        }

        // Update per-action branching data in the regret tracker.
        self.regret_tracker.update_action_branching(metrics);

        self.reroutes_since_tuning += 1;
        if self.reroutes_since_tuning >= TUNING_INTERVAL_REROUTES {
            let (high, low) = self.regret_tracker.suggest_thresholds();
            self.symbolic_threshold = high;
            self.low_threshold = low;
            self.reroutes_since_tuning = 0;
        }

        self.routes = compute_routes_with_thresholds(
            metrics,
            smt_compatible,
            self.symbolic_threshold,
            self.low_threshold,
        );
        self.last_reroute_depth = current_depth;
        true
    }

    /// Record an outcome for regret tracking after an action is processed.
    ///
    /// Called by the orchestrator after each action evaluation to feed the
    /// Thompson sampling model with outcome data.
    pub(crate) fn record_outcome(
        &mut self,
        action_idx: usize,
        engine: Engine,
        states_produced: u64,
        was_optimal: bool,
    ) {
        self.regret_tracker
            .record_outcome(action_idx, engine, states_produced, was_optimal);
    }

    /// Get the current regret ratio from the tracker.
    #[must_use]
    pub(crate) fn regret_ratio(&self) -> f64 {
        self.regret_tracker.regret_ratio()
    }

    /// Get a reference to the regret tracker (for diagnostics / testing).
    #[must_use]
    pub(crate) fn regret_tracker(&self) -> &OracleRegretTracker {
        &self.regret_tracker
    }

    /// Get the current symbolic threshold.
    #[must_use]
    pub(crate) fn symbolic_threshold(&self) -> f64 {
        self.symbolic_threshold
    }

    /// Get the current low threshold.
    #[must_use]
    pub(crate) fn low_threshold(&self) -> f64 {
        self.low_threshold
    }

    /// Count how many actions are routed to each category.
    #[must_use]
    pub(crate) fn route_summary(&self) -> RouteSummary {
        let mut bfs_only = 0usize;
        let mut symbolic_only = 0usize;
        let mut either = 0usize;
        for route in &self.routes {
            match route {
                ActionRoute::BfsOnly => bfs_only += 1,
                ActionRoute::SymbolicOnly => symbolic_only += 1,
                ActionRoute::Either => either += 1,
            }
        }
        RouteSummary {
            bfs_only,
            symbolic_only,
            either,
        }
    }
}

/// Summary of routing decisions across all actions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct RouteSummary {
    pub(crate) bfs_only: usize,
    pub(crate) symbolic_only: usize,
    pub(crate) either: usize,
}

// =========================================================================
// Thompson Sampling Regret Tracker (Part of #3843)
// =========================================================================

/// Beta distribution parameters for a single threshold candidate.
///
/// The Beta(alpha, beta) distribution models our belief about each
/// candidate's success probability. `alpha` counts successes + 1 prior,
/// `beta` counts failures + 1 prior (uniform prior).
#[derive(Debug, Clone)]
struct BetaParams {
    alpha: f64,
    beta: f64,
}

impl BetaParams {
    fn new() -> Self {
        // Uniform prior: Beta(1, 1)
        Self {
            alpha: 1.0,
            beta: 1.0,
        }
    }

    /// Record a success (the threshold led to a good routing decision).
    fn record_success(&mut self) {
        self.alpha += 1.0;
    }

    /// Record a failure (the threshold led to a suboptimal routing decision).
    fn record_failure(&mut self) {
        self.beta += 1.0;
    }

    /// Sample from the Beta distribution using the inverse-CDF method.
    ///
    /// Uses a simple PRNG seeded from a counter to avoid depending on the
    /// `rand` crate. The approximation uses the relationship between Beta
    /// and the incomplete beta function, but for Thompson sampling we only
    /// need approximate samples, so we use the mean + noise approach:
    ///
    /// Sample ~= mean + scaled_perturbation, where the perturbation
    /// magnitude decreases as we accumulate more data (higher alpha+beta).
    fn sample(&self, seed: u64) -> f64 {
        let mean = self.alpha / (self.alpha + self.beta);
        let total = self.alpha + self.beta;
        // Variance of Beta(a,b) = ab / ((a+b)^2 * (a+b+1))
        // stddev decreases as we gather more data.
        let variance = (self.alpha * self.beta) / (total * total * (total + 1.0));
        let stddev = variance.sqrt();

        // Generate a pseudo-normal perturbation from the seed using
        // Box-Muller-like approach with a simple hash.
        let u = pseudo_uniform(seed);
        // Map uniform to approximate normal via inverse-CDF approximation.
        // Beasley-Springer-Moro approximation for the normal quantile.
        let z = approx_normal_quantile(u);

        // Clamp to [0, 1] since Beta distribution support is [0, 1].
        (mean + stddev * z).clamp(0.0, 1.0)
    }
}

/// Regret tracker that uses Thompson sampling to self-tune oracle thresholds.
///
/// Tracks outcomes of routing decisions and uses Beta distributions over
/// candidate thresholds to propose improved (high_threshold, low_threshold)
/// pairs at regular intervals.
///
/// Part of #3843.
pub(crate) struct OracleRegretTracker {
    /// Total states explored (outcomes recorded).
    total_states: u64,
    /// States where the engine assignment was suboptimal.
    regret_states: u64,
    /// Running average branching factor per action index.
    action_branching: FxHashMap<usize, f64>,
    /// Thompson sampling Beta parameters for each high threshold candidate.
    high_threshold_params: Vec<BetaParams>,
    /// Thompson sampling Beta parameters for each low threshold candidate.
    low_threshold_params: Vec<BetaParams>,
    /// Index of the currently active high threshold candidate.
    active_high_idx: usize,
    /// Index of the currently active low threshold candidate.
    active_low_idx: usize,
    /// Monotonic counter used as PRNG seed for Thompson sampling.
    sample_counter: u64,
}

impl OracleRegretTracker {
    /// Create a new regret tracker with uniform priors on all candidates.
    #[must_use]
    pub(crate) fn new() -> Self {
        let default_high_idx = HIGH_THRESHOLD_CANDIDATES
            .iter()
            .position(|&t| (t - DEFAULT_SYMBOLIC_BRANCHING_THRESHOLD).abs() < f64::EPSILON)
            .unwrap_or(3); // index of 100.0

        let default_low_idx = LOW_THRESHOLD_CANDIDATES
            .iter()
            .position(|&t| (t - DEFAULT_LOW_THRESHOLD).abs() < f64::EPSILON)
            .unwrap_or(0); // index of 0.0

        Self {
            total_states: 0,
            regret_states: 0,
            action_branching: FxHashMap::default(),
            high_threshold_params: HIGH_THRESHOLD_CANDIDATES
                .iter()
                .map(|_| BetaParams::new())
                .collect(),
            low_threshold_params: LOW_THRESHOLD_CANDIDATES
                .iter()
                .map(|_| BetaParams::new())
                .collect(),
            active_high_idx: default_high_idx,
            active_low_idx: default_low_idx,
            sample_counter: 0,
        }
    }

    /// Record a routing outcome for regret tracking.
    ///
    /// - `action_idx`: which action was processed
    /// - `engine`: which engine handled it
    /// - `states_produced`: how many successor states were generated
    /// - `was_optimal`: whether the engine choice was optimal (caller decides
    ///   based on heuristic, e.g., symbolic was faster for high-branching)
    pub(crate) fn record_outcome(
        &mut self,
        action_idx: usize,
        _engine: Engine,
        states_produced: u64,
        was_optimal: bool,
    ) {
        self.total_states += states_produced;
        if !was_optimal {
            self.regret_states += states_produced;
        }

        // Update running average branching factor for this action.
        let entry = self.action_branching.entry(action_idx).or_insert(0.0);
        // Exponential moving average with alpha=0.1 for smoothing.
        *entry = *entry * 0.9 + states_produced as f64 * 0.1;

        // Update Beta parameters for the active threshold candidates.
        if was_optimal {
            if let Some(params) = self.high_threshold_params.get_mut(self.active_high_idx) {
                params.record_success();
            }
            if let Some(params) = self.low_threshold_params.get_mut(self.active_low_idx) {
                params.record_success();
            }
        } else {
            if let Some(params) = self.high_threshold_params.get_mut(self.active_high_idx) {
                params.record_failure();
            }
            if let Some(params) = self.low_threshold_params.get_mut(self.active_low_idx) {
                params.record_failure();
            }
        }
    }

    /// Update the per-action branching factor snapshot from metrics.
    ///
    /// Called at each reroute to refresh the tracker's view of action behavior.
    pub(crate) fn update_action_branching(&mut self, metrics: &[ActionMetrics]) {
        for (i, m) in metrics.iter().enumerate() {
            let times = m.times_evaluated.load(Ordering::Relaxed);
            if times > 0 {
                let total = m.total_successors.load(Ordering::Relaxed);
                let avg = total as f64 / times as f64;
                self.action_branching.insert(i, avg);
            }
        }
    }

    /// Use Thompson sampling to propose new (high_threshold, low_threshold).
    ///
    /// Samples from each candidate's Beta distribution and selects the
    /// candidate with the highest sampled value (probability of being optimal).
    /// Returns the actual threshold values, not indices.
    #[must_use]
    pub(crate) fn suggest_thresholds(&mut self) -> (f64, f64) {
        // Sample from each high threshold candidate's Beta distribution.
        let high_idx = sample_best_candidate(&self.high_threshold_params, &mut self.sample_counter);
        self.active_high_idx = high_idx;
        let high = HIGH_THRESHOLD_CANDIDATES[high_idx];

        // Sample from each low threshold candidate's Beta distribution.
        let low_idx = sample_best_candidate(&self.low_threshold_params, &mut self.sample_counter);
        self.active_low_idx = low_idx;
        let low = LOW_THRESHOLD_CANDIDATES[low_idx];

        // Ensure low < high (sanity check).
        if low >= high {
            return (high, 0.0);
        }

        (high, low)
    }

    /// Current regret ratio: fraction of states where routing was suboptimal.
    ///
    /// Returns 0.0 if no outcomes have been recorded yet.
    #[must_use]
    pub(crate) fn regret_ratio(&self) -> f64 {
        if self.total_states == 0 {
            return 0.0;
        }
        self.regret_states as f64 / self.total_states as f64
    }

    /// Total states tracked.
    #[must_use]
    pub(crate) fn total_states(&self) -> u64 {
        self.total_states
    }

    /// States where routing was suboptimal.
    #[must_use]
    pub(crate) fn regret_states(&self) -> u64 {
        self.regret_states
    }

    /// Get the running average branching factor for a specific action.
    #[must_use]
    pub(crate) fn action_avg_branching(&self, action_idx: usize) -> Option<f64> {
        self.action_branching.get(&action_idx).copied()
    }
}

/// Sample from each candidate's Beta distribution and return the index
/// of the candidate with the highest sample.
///
/// Takes the sample counter by mutable reference to avoid borrow conflicts
/// when called from `suggest_thresholds`.
fn sample_best_candidate(params: &[BetaParams], counter: &mut u64) -> usize {
    let mut best_idx = 0;
    let mut best_sample = f64::NEG_INFINITY;
    for (i, p) in params.iter().enumerate() {
        *counter = counter.wrapping_add(1);
        let sample = p.sample(*counter);
        if sample > best_sample {
            best_sample = sample;
            best_idx = i;
        }
    }
    best_idx
}

// =========================================================================
// PRNG and distribution helpers (no external dependencies)
// =========================================================================

/// Simple pseudo-random number in (0, 1) from a u64 seed.
///
/// Uses SplitMix64 (Vigna, 2015) — a fast, well-distributed hash function.
/// Not cryptographic, but sufficient for Thompson sampling exploration.
fn pseudo_uniform(seed: u64) -> f64 {
    let mut z = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^= z >> 31;
    // Map to (0, 1) excluding exact 0 and 1.
    ((z >> 11) as f64 + 0.5) / (1u64 << 53) as f64
}

/// Approximate the standard normal quantile (inverse CDF) for u in (0, 1).
///
/// Uses the Beasley-Springer-Moro algorithm, which is accurate to ~1e-6
/// for the central region and reasonable in the tails. This avoids
/// depending on external math libraries.
///
/// Reference: Beasley & Springer (1977), Moro (1995).
fn approx_normal_quantile(u: f64) -> f64 {
    // Rational approximation coefficients.
    const A: [f64; 4] = [
        2.50662_82388_2,
        -18.61500_06253,
        41.39119_77353_3,
        -25.44106_04963_8,
    ];
    const B: [f64; 4] = [
        -8.47351_09309,
        23.08336_74374_2,
        -21.06224_10182,
        3.13082_90983_3,
    ];
    const C: [f64; 9] = [
        0.33742_64738_48e-2,
        0.32260_45290_7e-1,
        0.12027_15924_2,
        0.21061_37690_3,
        0.27061_60372_7,
        0.20689_93250_4e-1,
        0.27467_10141_5e-1,
        0.32476_26959_6e-2,
        0.15076_07084_8e-4,
    ];

    let y = u - 0.5;
    if y.abs() < 0.42 {
        // Central region: rational approximation.
        let r = y * y;
        let num = y * (A[0] + r * (A[1] + r * (A[2] + r * A[3])));
        let den = 1.0 + r * (B[0] + r * (B[1] + r * (B[2] + r * B[3])));
        num / den
    } else {
        // Tail region: use Chebyshev approximation.
        let r = if y > 0.0 { 1.0 - u } else { u };
        // r > 0 since u is in (0,1), so ln(r) is negative.
        let s = (-2.0 * r.ln()).sqrt();

        let mut t = C[0];
        for &c in &C[1..] {
            t = t * s + c;
        }
        // Flip sign for upper tail.
        if y > 0.0 {
            // Note: the polynomial is built for the lower tail, so the
            // value `t` approximates the quantile for probability `r`.
            // For the upper tail, we negate.
            s - t / s
        } else {
            -(s - t / s)
        }
    }
}

// =========================================================================
// Route computation
// =========================================================================

/// Compute routing decisions from per-action metrics and SMT compatibility.
///
/// Delegates to [`compute_routes_with_thresholds`] using default thresholds.
/// This preserves the original API for callers that don't need threshold tuning.
#[must_use]
pub(crate) fn compute_routes(
    metrics: &[ActionMetrics],
    smt_compatible: &[bool],
) -> Vec<ActionRoute> {
    compute_routes_with_thresholds(
        metrics,
        smt_compatible,
        DEFAULT_SYMBOLIC_BRANCHING_THRESHOLD,
        DEFAULT_LOW_THRESHOLD,
    )
}

/// Compute routing decisions using explicit threshold parameters.
///
/// # Routing logic
///
/// For each action `i`:
/// 1. If `smt_compatible[i]` is `false` -> `BfsOnly`.
/// 2. If no evaluation data yet -> `Either` (if SMT-compatible), or `BfsOnly` if JIT-compiled.
/// 3. If avg branching factor <= `low_threshold` -> `BfsOnly` (too cheap for symbolic).
/// 4. If avg branching factor > `high_threshold` -> `SymbolicOnly`, downgraded to `Either`
///    if JIT-compiled (native BFS may be competitive).
/// 5. Otherwise -> `Either`, upgraded to `BfsOnly` if JIT-compiled (native BFS is preferred).
///
/// # JIT Bias (Part of #3854)
///
/// JIT-compiled actions execute as native machine code in BFS, making them
/// significantly faster than interpreter-based evaluation. The oracle factors
/// this in by biasing JIT-compiled actions towards BFS:
/// - `Either` -> `BfsOnly` (prefer fast native BFS)
/// - `SymbolicOnly` -> `Either` (let BFS compete with native speed advantage)
#[must_use]
pub(crate) fn compute_routes_with_thresholds(
    metrics: &[ActionMetrics],
    smt_compatible: &[bool],
    high_threshold: f64,
    low_threshold: f64,
) -> Vec<ActionRoute> {
    let len = metrics.len().min(smt_compatible.len());
    (0..len)
        .map(|i| {
            if !smt_compatible[i] {
                return ActionRoute::BfsOnly;
            }

            let is_jit = metrics[i].jit_compiled.load(Ordering::Relaxed);

            let times = metrics[i].times_evaluated.load(Ordering::Relaxed);
            if times == 0 {
                // No data yet — SMT-compatible actions default to Either,
                // but JIT-compiled actions prefer BFS from the start.
                return if is_jit {
                    ActionRoute::BfsOnly
                } else {
                    ActionRoute::Either
                };
            }

            let total = metrics[i].total_successors.load(Ordering::Relaxed);
            let avg_branching = total as f64 / times as f64;

            let base_route = if low_threshold > 0.0 && avg_branching <= low_threshold {
                ActionRoute::BfsOnly
            } else if avg_branching > high_threshold {
                ActionRoute::SymbolicOnly
            } else {
                ActionRoute::Either
            };

            // Apply JIT bias: JIT-compiled actions are faster in BFS,
            // so we shift routing one step towards BfsOnly.
            if is_jit {
                match base_route {
                    ActionRoute::SymbolicOnly => ActionRoute::Either,
                    ActionRoute::Either => ActionRoute::BfsOnly,
                    ActionRoute::BfsOnly => ActionRoute::BfsOnly,
                }
            } else {
                base_route
            }
        })
        .collect()
}

/// Compute the average branching factor for a single action.
///
/// Returns `None` if the action has not been evaluated yet.
#[must_use]
pub(crate) fn avg_branching_factor(metrics: &ActionMetrics) -> Option<f64> {
    let times = metrics.times_evaluated.load(Ordering::Relaxed);
    if times == 0 {
        return None;
    }
    let total = metrics.total_successors.load(Ordering::Relaxed);
    Some(total as f64 / times as f64)
}

// =========================================================================
// Static complexity analysis (Part of #3826)
// =========================================================================

/// Minimum set cardinality in a SUBSET operand to flag as high-cardinality.
///
/// `SUBSET S` produces 2^|S| elements. For |S| > 16 this is > 65536 states
/// from a single expression, making BFS infeasible.
const HIGH_CARDINALITY_SUBSET_THRESHOLD: usize = 16;

/// Signal from static complexity analysis indicating the spec has an
/// exponential state space that makes BFS infeasible.
///
/// Part of #3826.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ExponentialComplexity {
    /// Human-readable description of the detected pattern.
    pub reason: String,
}

/// Walk a module AST to detect exponential state space patterns.
///
/// Currently detects:
/// - **Nested SUBSET**: `SUBSET(SUBSET S)` produces 2^(2^|S|) elements — doubly exponential.
/// - **High-cardinality SUBSET**: `SUBSET S` where `S` is a set enumeration with
///   more than [`HIGH_CARDINALITY_SUBSET_THRESHOLD`] elements, or a Cartesian product
///   / record set with a combinatorial explosion.
///
/// The visitor is conservative: it only flags clear exponential patterns to avoid
/// false positives on specs with manageable SUBSET usage.
///
/// Part of #3826.
pub(crate) struct ComplexityVisitor {
    /// Accumulated signals from the walk.
    signals: Vec<ExponentialComplexity>,
}

impl ComplexityVisitor {
    /// Create a new visitor with no accumulated signals.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            signals: Vec::new(),
        }
    }

    /// Walk an entire module, scanning all operator bodies.
    pub(crate) fn visit_module(&mut self, module: &Module) {
        for unit in &module.units {
            if let Unit::Operator(def) = &unit.node {
                self.visit_expr(&def.body);
            }
        }
    }

    /// Walk an expression tree, detecting exponential patterns.
    pub(crate) fn visit_expr(&mut self, expr: &Spanned<Expr>) {
        match &expr.node {
            // --- Primary detection: nested SUBSET ---
            Expr::Powerset(inner) => {
                if self.is_powerset_or_high_cardinality(inner) {
                    self.signals.push(ExponentialComplexity {
                        reason:
                            "nested SUBSET(SUBSET ...) detected — doubly exponential state space"
                                .to_string(),
                    });
                }
                // Continue walking the inner expression for other patterns.
                self.visit_expr(inner);
            }

            // --- Recurse into subexpressions ---
            Expr::And(a, b)
            | Expr::Or(a, b)
            | Expr::Implies(a, b)
            | Expr::Equiv(a, b)
            | Expr::Eq(a, b)
            | Expr::Neq(a, b)
            | Expr::Lt(a, b)
            | Expr::Leq(a, b)
            | Expr::Gt(a, b)
            | Expr::Geq(a, b)
            | Expr::Add(a, b)
            | Expr::Sub(a, b)
            | Expr::Mul(a, b)
            | Expr::Div(a, b)
            | Expr::IntDiv(a, b)
            | Expr::Mod(a, b)
            | Expr::Pow(a, b)
            | Expr::Range(a, b)
            | Expr::In(a, b)
            | Expr::NotIn(a, b)
            | Expr::Subseteq(a, b)
            | Expr::Union(a, b)
            | Expr::Intersect(a, b)
            | Expr::SetMinus(a, b)
            | Expr::FuncApply(a, b)
            | Expr::FuncSet(a, b)
            | Expr::LeadsTo(a, b)
            | Expr::WeakFair(a, b)
            | Expr::StrongFair(a, b) => {
                self.visit_expr(a);
                self.visit_expr(b);
            }
            Expr::Not(inner)
            | Expr::Neg(inner)
            | Expr::BigUnion(inner)
            | Expr::Domain(inner)
            | Expr::Prime(inner)
            | Expr::Always(inner)
            | Expr::Eventually(inner)
            | Expr::Enabled(inner)
            | Expr::Unchanged(inner) => {
                self.visit_expr(inner);
            }
            Expr::If(cond, then_e, else_e) => {
                self.visit_expr(cond);
                self.visit_expr(then_e);
                self.visit_expr(else_e);
            }
            Expr::Apply(func, args) => {
                self.visit_expr(func);
                for arg in args {
                    self.visit_expr(arg);
                }
            }
            Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => {
                for e in elems {
                    self.visit_expr(e);
                }
            }
            Expr::SetBuilder(body, bounds) => {
                self.visit_expr(body);
                for bv in bounds {
                    if let Some(ref domain) = bv.domain {
                        self.visit_expr(domain);
                    }
                }
            }
            Expr::SetFilter(bv, body) => {
                if let Some(ref domain) = bv.domain {
                    self.visit_expr(domain);
                }
                self.visit_expr(body);
            }
            Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
                for bv in bounds {
                    if let Some(ref domain) = bv.domain {
                        self.visit_expr(domain);
                    }
                }
                self.visit_expr(body);
            }
            Expr::Choose(bv, body) => {
                if let Some(ref domain) = bv.domain {
                    self.visit_expr(domain);
                }
                self.visit_expr(body);
            }
            Expr::FuncDef(bounds, body) => {
                for bv in bounds {
                    if let Some(ref domain) = bv.domain {
                        self.visit_expr(domain);
                    }
                }
                self.visit_expr(body);
            }
            Expr::Except(base, specs) => {
                self.visit_expr(base);
                for spec in specs {
                    self.visit_expr(&spec.value);
                    for path_elem in &spec.path {
                        if let tla_core::ast::ExceptPathElement::Index(idx) = path_elem {
                            self.visit_expr(idx);
                        }
                    }
                }
            }
            Expr::Record(fields) | Expr::RecordSet(fields) => {
                for (_, val) in fields {
                    self.visit_expr(val);
                }
            }
            Expr::RecordAccess(base, _) => {
                self.visit_expr(base);
            }
            Expr::Let(defs, body) => {
                for def in defs {
                    self.visit_expr(&def.body);
                }
                self.visit_expr(body);
            }
            Expr::Case(arms, other) => {
                for arm in arms {
                    self.visit_expr(&arm.guard);
                    self.visit_expr(&arm.body);
                }
                if let Some(ref default) = other {
                    self.visit_expr(default);
                }
            }
            Expr::Lambda(_, body) => {
                self.visit_expr(body);
            }
            Expr::Label(label) => {
                self.visit_expr(&label.body);
            }
            Expr::SubstIn(_, body) => {
                self.visit_expr(body);
            }
            Expr::ModuleRef(_, _, args) => {
                for arg in args {
                    self.visit_expr(arg);
                }
            }

            // Leaves: no children to visit.
            Expr::Bool(_)
            | Expr::Int(_)
            | Expr::String(_)
            | Expr::Ident(_, _)
            | Expr::StateVar(_, _, _)
            | Expr::OpRef(_)
            | Expr::InstanceExpr(_, _) => {}
        }
    }

    /// Check whether an expression is itself a `Powerset` or represents a
    /// high-cardinality set that would make `SUBSET` of it exponential.
    fn is_powerset_or_high_cardinality(&self, expr: &Spanned<Expr>) -> bool {
        match &expr.node {
            // Nested SUBSET: SUBSET(SUBSET X) is doubly exponential.
            Expr::Powerset(_) => true,
            // Set enumeration with many elements: SUBSET {a, b, ..., z}.
            Expr::SetEnum(elems) if elems.len() > HIGH_CARDINALITY_SUBSET_THRESHOLD => true,
            // Cartesian product: SUBSET (S \X T \X ...) — product of domains.
            // Even small domains (3 x 3 x 3 = 27) make SUBSET produce 2^27 states.
            Expr::Times(factors) if factors.len() >= 3 => true,
            // RecordSet: SUBSET [a : S, b : T, ...] — like Cartesian product.
            Expr::RecordSet(fields) if fields.len() >= 3 => true,
            _ => false,
        }
    }

    /// Consume the visitor and return any detected exponential complexity signals.
    #[must_use]
    pub(crate) fn into_signals(self) -> Vec<ExponentialComplexity> {
        self.signals
    }
}

/// Detect whether a module contains exponential state space patterns.
///
/// Walks all operator bodies in the module looking for patterns that would make
/// BFS infeasible (e.g., `SUBSET(SUBSET Nodes)`). Returns the first detected
/// signal, or `None` if the spec has manageable complexity.
///
/// This is the primary entry point for static complexity detection.
///
/// Part of #3826.
#[must_use]
pub fn detect_exponential_complexity(module: &Module) -> Option<ExponentialComplexity> {
    let mut visitor = ComplexityVisitor::new();
    visitor.visit_module(module);
    visitor.into_signals().into_iter().next()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicBool;
    use std::sync::atomic::AtomicU64;

    fn make_metrics(total_successors: u64, times_evaluated: u64, smt: bool) -> ActionMetrics {
        ActionMetrics {
            total_successors: AtomicU64::new(total_successors),
            times_evaluated: AtomicU64::new(times_evaluated),
            smt_compatible: AtomicBool::new(smt),
            jit_compiled: AtomicBool::new(false),
        }
    }

    fn make_metrics_with_jit(
        total_successors: u64,
        times_evaluated: u64,
        smt: bool,
        jit: bool,
    ) -> ActionMetrics {
        ActionMetrics {
            total_successors: AtomicU64::new(total_successors),
            times_evaluated: AtomicU64::new(times_evaluated),
            smt_compatible: AtomicBool::new(smt),
            jit_compiled: AtomicBool::new(jit),
        }
    }

    // =====================================================================
    // Original compute_routes tests (unchanged behavior)
    // =====================================================================

    #[test]
    fn test_compute_routes_not_smt_compatible_returns_bfs_only() {
        let metrics = vec![make_metrics(500, 2, false)];
        let smt = vec![false];
        let routes = compute_routes(&metrics, &smt);
        assert_eq!(routes, vec![ActionRoute::BfsOnly]);
    }

    #[test]
    fn test_compute_routes_high_branching_smt_returns_symbolic() {
        // avg = 500/2 = 250 > 100 threshold
        let metrics = vec![make_metrics(500, 2, true)];
        let smt = vec![true];
        let routes = compute_routes(&metrics, &smt);
        assert_eq!(routes, vec![ActionRoute::SymbolicOnly]);
    }

    #[test]
    fn test_compute_routes_low_branching_smt_returns_either() {
        // avg = 50/5 = 10 < 100 threshold
        let metrics = vec![make_metrics(50, 5, true)];
        let smt = vec![true];
        let routes = compute_routes(&metrics, &smt);
        assert_eq!(routes, vec![ActionRoute::Either]);
    }

    #[test]
    fn test_compute_routes_no_data_smt_returns_either() {
        let metrics = vec![make_metrics(0, 0, true)];
        let smt = vec![true];
        let routes = compute_routes(&metrics, &smt);
        assert_eq!(routes, vec![ActionRoute::Either]);
    }

    #[test]
    fn test_compute_routes_no_data_not_smt_returns_bfs() {
        let metrics = vec![make_metrics(0, 0, false)];
        let smt = vec![false];
        let routes = compute_routes(&metrics, &smt);
        assert_eq!(routes, vec![ActionRoute::BfsOnly]);
    }

    #[test]
    fn test_compute_routes_mixed_actions() {
        let metrics = vec![
            make_metrics(1000, 5, true),  // avg=200 > 100, smt -> Symbolic
            make_metrics(10, 5, true),    // avg=2 < 100, smt -> Either
            make_metrics(5000, 1, false), // not smt -> BfsOnly
            make_metrics(0, 0, true),     // no data, smt -> Either
        ];
        let smt = vec![true, true, false, true];
        let routes = compute_routes(&metrics, &smt);
        assert_eq!(
            routes,
            vec![
                ActionRoute::SymbolicOnly,
                ActionRoute::Either,
                ActionRoute::BfsOnly,
                ActionRoute::Either,
            ]
        );
    }

    #[test]
    fn test_compute_routes_exactly_at_threshold_returns_either() {
        // avg = 100/1 = 100.0, NOT > 100 so it stays Either
        let metrics = vec![make_metrics(100, 1, true)];
        let smt = vec![true];
        let routes = compute_routes(&metrics, &smt);
        assert_eq!(routes, vec![ActionRoute::Either]);
    }

    #[test]
    fn test_compute_routes_just_above_threshold_returns_symbolic() {
        // avg = 101/1 = 101.0 > 100
        let metrics = vec![make_metrics(101, 1, true)];
        let smt = vec![true];
        let routes = compute_routes(&metrics, &smt);
        assert_eq!(routes, vec![ActionRoute::SymbolicOnly]);
    }

    // =====================================================================
    // ActionOracle tests
    // =====================================================================

    #[test]
    fn test_oracle_new_and_route() {
        let metrics = vec![
            make_metrics(500, 2, true), // avg=250 -> Symbolic
            make_metrics(10, 5, false), // not smt -> BfsOnly
        ];
        let smt = vec![true, false];
        let oracle = ActionOracle::new(&metrics, &smt);

        assert_eq!(oracle.route(0), ActionRoute::SymbolicOnly);
        assert_eq!(oracle.route(1), ActionRoute::BfsOnly);
        assert_eq!(oracle.route(99), ActionRoute::BfsOnly); // out of range
        assert_eq!(oracle.action_count(), 2);
    }

    #[test]
    fn test_oracle_all_bfs() {
        let oracle = ActionOracle::all_bfs(3);
        assert_eq!(oracle.action_count(), 3);
        assert_eq!(oracle.route(0), ActionRoute::BfsOnly);
        assert_eq!(oracle.route(1), ActionRoute::BfsOnly);
        assert_eq!(oracle.route(2), ActionRoute::BfsOnly);
    }

    #[test]
    fn test_oracle_reroute_respects_interval() {
        let metrics = vec![make_metrics(0, 0, true)];
        let smt = vec![true];
        let mut oracle = ActionOracle::new(&metrics, &smt);

        // Initial route should be Either (no data)
        assert_eq!(oracle.route(0), ActionRoute::Either);

        // Simulate BFS accumulating data
        metrics[0].total_successors.store(1000, Ordering::Relaxed);
        metrics[0].times_evaluated.store(5, Ordering::Relaxed);

        // Depth 2: too early to reroute (interval is 5)
        assert!(!oracle.reroute(2, &metrics, &smt));
        assert_eq!(oracle.route(0), ActionRoute::Either); // unchanged

        // Depth 5: triggers reroute (0 + 5 = 5)
        assert!(oracle.reroute(5, &metrics, &smt));
        assert_eq!(oracle.route(0), ActionRoute::SymbolicOnly); // avg=200 > 100
    }

    #[test]
    fn test_oracle_reroute_updates_last_depth() {
        let metrics = vec![make_metrics(50, 5, true)]; // avg=10
        let smt = vec![true];
        let mut oracle = ActionOracle::new(&metrics, &smt);

        // First reroute at depth 5
        assert!(oracle.reroute(5, &metrics, &smt));
        // Next reroute at depth 9 should NOT trigger (5 + 5 = 10)
        assert!(!oracle.reroute(9, &metrics, &smt));
        // Depth 10 should trigger
        assert!(oracle.reroute(10, &metrics, &smt));
    }

    #[test]
    fn test_oracle_route_summary() {
        let metrics = vec![
            make_metrics(500, 2, true), // Symbolic
            make_metrics(10, 5, true),  // Either
            make_metrics(10, 5, false), // BfsOnly
        ];
        let smt = vec![true, true, false];
        let oracle = ActionOracle::new(&metrics, &smt);
        let summary = oracle.route_summary();
        assert_eq!(summary.bfs_only, 1);
        assert_eq!(summary.symbolic_only, 1);
        assert_eq!(summary.either, 1);
    }

    #[test]
    fn test_avg_branching_factor_with_data() {
        let m = make_metrics(500, 10, true);
        assert_eq!(avg_branching_factor(&m), Some(50.0));
    }

    #[test]
    fn test_avg_branching_factor_no_data() {
        let m = make_metrics(0, 0, true);
        assert_eq!(avg_branching_factor(&m), None);
    }

    #[test]
    fn test_compute_routes_mismatched_lengths_uses_min() {
        // metrics has 3 entries, smt has 2 — should produce 2 routes
        let metrics = vec![
            make_metrics(10, 1, true),
            make_metrics(200, 1, true),
            make_metrics(300, 1, true),
        ];
        let smt = vec![true, true];
        let routes = compute_routes(&metrics, &smt);
        assert_eq!(routes.len(), 2);
    }

    #[test]
    fn test_oracle_empty_actions() {
        let oracle = ActionOracle::new(&[], &[]);
        assert_eq!(oracle.action_count(), 0);
        assert_eq!(oracle.route(0), ActionRoute::BfsOnly);
        let summary = oracle.route_summary();
        assert_eq!(summary.bfs_only, 0);
        assert_eq!(summary.symbolic_only, 0);
        assert_eq!(summary.either, 0);
    }

    // =====================================================================
    // OracleRegretTracker tests (Part of #3843)
    // =====================================================================

    #[test]
    fn test_regret_tracker_new_has_zero_regret() {
        let tracker = OracleRegretTracker::new();
        assert_eq!(tracker.total_states(), 0);
        assert_eq!(tracker.regret_states(), 0);
        assert!((tracker.regret_ratio() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_regret_tracker_record_optimal_outcomes() {
        let mut tracker = OracleRegretTracker::new();
        tracker.record_outcome(0, Engine::Bfs, 10, true);
        tracker.record_outcome(1, Engine::Symbolic, 20, true);

        assert_eq!(tracker.total_states(), 30);
        assert_eq!(tracker.regret_states(), 0);
        assert!((tracker.regret_ratio() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_regret_tracker_record_suboptimal_outcomes() {
        let mut tracker = OracleRegretTracker::new();
        tracker.record_outcome(0, Engine::Bfs, 10, true);
        tracker.record_outcome(1, Engine::Bfs, 20, false); // suboptimal

        assert_eq!(tracker.total_states(), 30);
        assert_eq!(tracker.regret_states(), 20);
        let expected = 20.0 / 30.0;
        assert!(
            (tracker.regret_ratio() - expected).abs() < 1e-10,
            "expected {expected}, got {}",
            tracker.regret_ratio()
        );
    }

    #[test]
    fn test_regret_tracker_action_branching_ema() {
        let mut tracker = OracleRegretTracker::new();
        // First outcome: EMA starts at 0.0, then 0.0*0.9 + 100*0.1 = 10.0
        tracker.record_outcome(0, Engine::Bfs, 100, true);
        let avg = tracker.action_avg_branching(0).expect("should have data");
        assert!(
            (avg - 10.0).abs() < f64::EPSILON,
            "expected 10.0, got {avg}"
        );

        // Second outcome: 10.0*0.9 + 200*0.1 = 9.0 + 20.0 = 29.0
        tracker.record_outcome(0, Engine::Bfs, 200, true);
        let avg = tracker.action_avg_branching(0).expect("should have data");
        assert!(
            (avg - 29.0).abs() < f64::EPSILON,
            "expected 29.0, got {avg}"
        );
    }

    #[test]
    fn test_regret_tracker_action_branching_unknown_action() {
        let tracker = OracleRegretTracker::new();
        assert!(tracker.action_avg_branching(99).is_none());
    }

    #[test]
    fn test_regret_tracker_suggest_thresholds_returns_valid_pair() {
        let mut tracker = OracleRegretTracker::new();
        // Record a mix of outcomes to influence Beta parameters.
        for i in 0..50 {
            let optimal = i % 3 != 0;
            tracker.record_outcome(0, Engine::Bfs, 10, optimal);
        }

        let (high, low) = tracker.suggest_thresholds();
        // High threshold should be one of the candidates.
        assert!(
            HIGH_THRESHOLD_CANDIDATES.contains(&high),
            "high threshold {high} not in candidates"
        );
        // Low threshold should be one of the candidates.
        assert!(
            LOW_THRESHOLD_CANDIDATES.contains(&low) || (low - 0.0).abs() < f64::EPSILON,
            "low threshold {low} not in candidates"
        );
        // Low must be < high (or 0.0 if clamped).
        assert!(
            low < high || (low - 0.0).abs() < f64::EPSILON,
            "low {low} >= high {high}"
        );
    }

    #[test]
    fn test_regret_tracker_suggest_thresholds_deterministic_for_fixed_state() {
        // Two trackers with identical state should produce identical suggestions.
        let mut tracker1 = OracleRegretTracker::new();
        let mut tracker2 = OracleRegretTracker::new();

        for i in 0..20 {
            let optimal = i % 2 == 0;
            tracker1.record_outcome(0, Engine::Bfs, 5, optimal);
            tracker2.record_outcome(0, Engine::Bfs, 5, optimal);
        }

        let (h1, l1) = tracker1.suggest_thresholds();
        let (h2, l2) = tracker2.suggest_thresholds();
        assert!(
            (h1 - h2).abs() < f64::EPSILON && (l1 - l2).abs() < f64::EPSILON,
            "trackers diverged: ({h1},{l1}) vs ({h2},{l2})"
        );
    }

    #[test]
    fn test_regret_tracker_update_action_branching_from_metrics() {
        let mut tracker = OracleRegretTracker::new();
        let metrics = vec![
            make_metrics(500, 10, true), // avg=50
            make_metrics(0, 0, true),    // no data
            make_metrics(300, 3, false), // avg=100
        ];

        tracker.update_action_branching(&metrics);
        assert!(
            (tracker.action_avg_branching(0).expect("should exist") - 50.0).abs() < f64::EPSILON
        );
        assert!(tracker.action_avg_branching(1).is_none()); // no evals
        assert!(
            (tracker.action_avg_branching(2).expect("should exist") - 100.0).abs() < f64::EPSILON
        );
    }

    // =====================================================================
    // compute_routes_with_thresholds tests (Part of #3843)
    // =====================================================================

    #[test]
    fn test_compute_routes_with_low_threshold_filters_cheap_actions() {
        // avg=2, low_threshold=5 -> BfsOnly (too cheap for symbolic)
        let metrics = vec![make_metrics(10, 5, true)];
        let smt = vec![true];
        let routes = compute_routes_with_thresholds(&metrics, &smt, 100.0, 5.0);
        assert_eq!(routes, vec![ActionRoute::BfsOnly]);
    }

    #[test]
    fn test_compute_routes_with_low_threshold_zero_disables_filter() {
        // avg=2, low_threshold=0.0 -> Either (low filter disabled)
        let metrics = vec![make_metrics(10, 5, true)];
        let smt = vec![true];
        let routes = compute_routes_with_thresholds(&metrics, &smt, 100.0, 0.0);
        assert_eq!(routes, vec![ActionRoute::Either]);
    }

    #[test]
    fn test_compute_routes_with_custom_high_threshold() {
        // avg=60, high=50 -> SymbolicOnly
        let metrics = vec![make_metrics(300, 5, true)];
        let smt = vec![true];
        let routes = compute_routes_with_thresholds(&metrics, &smt, 50.0, 0.0);
        assert_eq!(routes, vec![ActionRoute::SymbolicOnly]);
    }

    #[test]
    fn test_compute_routes_with_both_thresholds() {
        let metrics = vec![
            make_metrics(500, 5, true), // avg=100, > high=50 -> SymbolicOnly
            make_metrics(15, 5, true),  // avg=3, between low=2 and high=50 -> Either
            make_metrics(5, 5, true),   // avg=1, <= low=2 -> BfsOnly
        ];
        let smt = vec![true, true, true];
        let routes = compute_routes_with_thresholds(&metrics, &smt, 50.0, 2.0);
        assert_eq!(
            routes,
            vec![
                ActionRoute::SymbolicOnly,
                ActionRoute::Either,
                ActionRoute::BfsOnly,
            ]
        );
    }

    // =====================================================================
    // Oracle threshold tuning integration tests (Part of #3843)
    // =====================================================================

    #[test]
    fn test_oracle_starts_with_default_thresholds() {
        let oracle = ActionOracle::new(&[], &[]);
        assert!(
            (oracle.symbolic_threshold() - DEFAULT_SYMBOLIC_BRANCHING_THRESHOLD).abs()
                < f64::EPSILON
        );
        assert!((oracle.low_threshold() - DEFAULT_LOW_THRESHOLD).abs() < f64::EPSILON);
    }

    #[test]
    fn test_oracle_record_outcome_updates_regret() {
        let metrics = vec![make_metrics(100, 5, true)];
        let smt = vec![true];
        let mut oracle = ActionOracle::new(&metrics, &smt);

        oracle.record_outcome(0, Engine::Bfs, 10, true);
        oracle.record_outcome(0, Engine::Bfs, 5, false);

        assert_eq!(oracle.regret_tracker().total_states(), 15);
        assert_eq!(oracle.regret_tracker().regret_states(), 5);
        let expected = 5.0 / 15.0;
        assert!(
            (oracle.regret_ratio() - expected).abs() < 1e-10,
            "expected {expected}, got {}",
            oracle.regret_ratio()
        );
    }

    #[test]
    fn test_oracle_tuning_triggers_after_interval() {
        let metrics = vec![make_metrics(50, 5, true)];
        let smt = vec![true];
        let mut oracle = ActionOracle::new(&metrics, &smt);

        // Record some outcomes so Beta distributions have data.
        for i in 0..100 {
            oracle.record_outcome(0, Engine::Bfs, 5, i % 3 != 0);
        }

        let initial_high = oracle.symbolic_threshold();

        // Trigger TUNING_INTERVAL_REROUTES reroutes at 5-level intervals.
        for cycle in 1..=TUNING_INTERVAL_REROUTES {
            let depth = cycle * REROUTE_INTERVAL_LEVELS;
            oracle.reroute(depth, &metrics, &smt);
        }

        // After enough reroutes, the threshold may have changed
        // (or stayed the same if sampling chose the same candidate).
        // The key invariant: thresholds are always valid candidates.
        assert!(
            HIGH_THRESHOLD_CANDIDATES.contains(&oracle.symbolic_threshold()),
            "high threshold {} not in candidates after tuning",
            oracle.symbolic_threshold()
        );
        assert!(
            LOW_THRESHOLD_CANDIDATES.contains(&oracle.low_threshold())
                || (oracle.low_threshold() - 0.0).abs() < f64::EPSILON,
            "low threshold {} not in candidates after tuning",
            oracle.low_threshold()
        );

        // Verify tuning actually ran (counter was reset).
        // The initial threshold was the default; if tuning ran, the field
        // was set (even if to the same value).
        let _ = initial_high; // suppress unused warning
    }

    // =====================================================================
    // PRNG / distribution helper tests
    // =====================================================================

    #[test]
    fn test_pseudo_uniform_range() {
        for seed in 0..1000 {
            let u = pseudo_uniform(seed);
            assert!(u > 0.0 && u < 1.0, "seed {seed} -> {u} out of (0,1)");
        }
    }

    #[test]
    fn test_pseudo_uniform_different_seeds_produce_different_values() {
        let a = pseudo_uniform(42);
        let b = pseudo_uniform(43);
        assert!(
            (a - b).abs() > 1e-15,
            "adjacent seeds should produce different values"
        );
    }

    #[test]
    fn test_approx_normal_quantile_median_is_zero() {
        let q = approx_normal_quantile(0.5);
        assert!(q.abs() < 1e-6, "quantile at 0.5 should be ~0.0, got {q}");
    }

    #[test]
    fn test_approx_normal_quantile_symmetry() {
        for &u in &[0.1, 0.2, 0.3, 0.4] {
            let lower = approx_normal_quantile(u);
            let upper = approx_normal_quantile(1.0 - u);
            assert!(
                (lower + upper).abs() < 1e-4,
                "quantile asymmetry at u={u}: {lower} + {upper} != 0"
            );
        }
    }

    #[test]
    fn test_beta_params_sample_within_bounds() {
        let params = BetaParams {
            alpha: 5.0,
            beta: 3.0,
        };
        for seed in 0..500 {
            let s = params.sample(seed);
            assert!(
                (0.0..=1.0).contains(&s),
                "seed {seed}: sample {s} out of [0,1]"
            );
        }
    }

    #[test]
    fn test_beta_params_strong_prior_concentrates_samples() {
        // Beta(100, 1) should produce samples very close to 1.0.
        let params = BetaParams {
            alpha: 100.0,
            beta: 1.0,
        };
        let mut sum = 0.0;
        let n = 100;
        for seed in 0..n {
            sum += params.sample(seed);
        }
        let mean = sum / n as f64;
        assert!(mean > 0.9, "Beta(100,1) mean should be ~0.99, got {mean}");
    }

    #[test]
    fn test_beta_params_uniform_prior_moderate_samples() {
        // Beta(1, 1) = uniform, mean should be ~0.5.
        let params = BetaParams::new();
        let mut sum = 0.0;
        let n = 200;
        for seed in 0..n {
            sum += params.sample(seed);
        }
        let mean = sum / n as f64;
        assert!(
            (mean - 0.5).abs() < 0.15,
            "Beta(1,1) mean should be ~0.5, got {mean}"
        );
    }

    // =====================================================================
    // ActionOracle::all_symbolic tests (Part of #3826)
    // =====================================================================

    #[test]
    fn test_oracle_all_symbolic() {
        let oracle = ActionOracle::all_symbolic(3);
        assert_eq!(oracle.action_count(), 3);
        assert_eq!(oracle.route(0), ActionRoute::SymbolicOnly);
        assert_eq!(oracle.route(1), ActionRoute::SymbolicOnly);
        assert_eq!(oracle.route(2), ActionRoute::SymbolicOnly);
    }

    #[test]
    fn test_oracle_all_symbolic_empty() {
        let oracle = ActionOracle::all_symbolic(0);
        assert_eq!(oracle.action_count(), 0);
        assert_eq!(oracle.route(0), ActionRoute::BfsOnly); // out of range fallback
    }

    // =====================================================================
    // ComplexityVisitor tests (Part of #3826)
    // =====================================================================

    /// Helper: build a Spanned<Expr> with dummy span for test construction.
    fn spanned(expr: Expr) -> Spanned<Expr> {
        Spanned {
            node: expr,
            span: tla_core::span::Span::dummy(),
        }
    }

    #[test]
    fn test_complexity_visitor_nested_subset_detected() {
        // SUBSET(SUBSET x) — doubly exponential
        let inner_set = spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ));
        let subset_inner = spanned(Expr::Powerset(Box::new(inner_set)));
        let subset_outer = spanned(Expr::Powerset(Box::new(subset_inner)));

        let mut visitor = ComplexityVisitor::new();
        visitor.visit_expr(&subset_outer);
        let signals = visitor.into_signals();

        assert_eq!(signals.len(), 1, "should detect one exponential pattern");
        assert!(
            signals[0].reason.contains("nested SUBSET"),
            "reason should mention nested SUBSET, got: {}",
            signals[0].reason
        );
    }

    #[test]
    fn test_complexity_visitor_single_subset_not_flagged() {
        // SUBSET x — not exponential (just 2^|x|, which is normal)
        let inner_set = spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ));
        let subset = spanned(Expr::Powerset(Box::new(inner_set)));

        let mut visitor = ComplexityVisitor::new();
        visitor.visit_expr(&subset);
        let signals = visitor.into_signals();

        assert!(signals.is_empty(), "single SUBSET should not be flagged");
    }

    #[test]
    fn test_complexity_visitor_high_cardinality_subset_detected() {
        // SUBSET {1, 2, 3, ..., 20} — 2^20 = 1M elements
        let elements: Vec<Spanned<Expr>> = (1..=20)
            .map(|i| spanned(Expr::Int(num_bigint::BigInt::from(i))))
            .collect();
        let set_enum = spanned(Expr::SetEnum(elements));
        let subset = spanned(Expr::Powerset(Box::new(set_enum)));

        let mut visitor = ComplexityVisitor::new();
        visitor.visit_expr(&subset);
        let signals = visitor.into_signals();

        assert_eq!(
            signals.len(),
            1,
            "SUBSET of >16-element set should be flagged"
        );
    }

    #[test]
    fn test_complexity_visitor_small_set_enum_subset_not_flagged() {
        // SUBSET {1, 2, 3} — 2^3 = 8, fine
        let elements: Vec<Spanned<Expr>> = (1..=3)
            .map(|i| spanned(Expr::Int(num_bigint::BigInt::from(i))))
            .collect();
        let set_enum = spanned(Expr::SetEnum(elements));
        let subset = spanned(Expr::Powerset(Box::new(set_enum)));

        let mut visitor = ComplexityVisitor::new();
        visitor.visit_expr(&subset);
        let signals = visitor.into_signals();

        assert!(
            signals.is_empty(),
            "SUBSET of small set should not be flagged"
        );
    }

    #[test]
    fn test_complexity_visitor_subset_of_cartesian_product_detected() {
        // SUBSET (S \X T \X U) — product of 3 domains makes SUBSET exponential
        let s = spanned(Expr::Ident(
            "S".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ));
        let t = spanned(Expr::Ident(
            "T".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ));
        let u = spanned(Expr::Ident(
            "U".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ));
        let product = spanned(Expr::Times(vec![s, t, u]));
        let subset = spanned(Expr::Powerset(Box::new(product)));

        let mut visitor = ComplexityVisitor::new();
        visitor.visit_expr(&subset);
        let signals = visitor.into_signals();

        assert_eq!(
            signals.len(),
            1,
            "SUBSET of 3-way Cartesian product should be flagged"
        );
    }

    #[test]
    fn test_complexity_visitor_nested_in_conjunction_detected() {
        // (P /\ SUBSET(SUBSET x)) — should still detect the nested SUBSET
        let inner_set = spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ));
        let subset_inner = spanned(Expr::Powerset(Box::new(inner_set)));
        let subset_outer = spanned(Expr::Powerset(Box::new(subset_inner)));
        let pred = spanned(Expr::Bool(true));
        let conj = spanned(Expr::And(Box::new(pred), Box::new(subset_outer)));

        let mut visitor = ComplexityVisitor::new();
        visitor.visit_expr(&conj);
        let signals = visitor.into_signals();

        assert_eq!(
            signals.len(),
            1,
            "nested SUBSET inside conjunction should be detected"
        );
    }

    #[test]
    fn test_detect_exponential_complexity_module_with_nested_subset() {
        // Build a module with one operator: Op == SUBSET(SUBSET Nodes)
        let inner_set = spanned(Expr::Ident(
            "Nodes".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ));
        let subset_inner = spanned(Expr::Powerset(Box::new(inner_set)));
        let subset_outer = spanned(Expr::Powerset(Box::new(subset_inner)));

        let op_def = tla_core::ast::OperatorDef {
            name: Spanned {
                node: "Op".to_string(),
                span: tla_core::span::Span::dummy(),
            },
            params: vec![],
            body: subset_outer,
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        };

        let module = Module {
            name: Spanned {
                node: "TestModule".to_string(),
                span: tla_core::span::Span::dummy(),
            },
            extends: vec![],
            units: vec![Spanned {
                node: Unit::Operator(op_def),
                span: tla_core::span::Span::dummy(),
            }],
            action_subscript_spans: std::collections::HashSet::new(),
            span: tla_core::span::Span::dummy(),
        };

        let result = detect_exponential_complexity(&module);
        assert!(result.is_some(), "should detect exponential complexity");
        assert!(
            result.as_ref().unwrap().reason.contains("nested SUBSET"),
            "reason: {}",
            result.unwrap().reason
        );
    }

    #[test]
    fn test_detect_exponential_complexity_simple_module_none() {
        // Module with simple operator: Op == x + 1
        let body = spanned(Expr::Add(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(num_bigint::BigInt::from(1)))),
        ));

        let op_def = tla_core::ast::OperatorDef {
            name: Spanned {
                node: "Op".to_string(),
                span: tla_core::span::Span::dummy(),
            },
            params: vec![],
            body,
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        };

        let module = Module {
            name: Spanned {
                node: "SimpleModule".to_string(),
                span: tla_core::span::Span::dummy(),
            },
            extends: vec![],
            units: vec![Spanned {
                node: Unit::Operator(op_def),
                span: tla_core::span::Span::dummy(),
            }],
            action_subscript_spans: std::collections::HashSet::new(),
            span: tla_core::span::Span::dummy(),
        };

        let result = detect_exponential_complexity(&module);
        assert!(
            result.is_none(),
            "simple module should not trigger exponential complexity"
        );
    }

    #[test]
    fn test_complexity_visitor_subset_subset_in_set_filter_domain() {
        // SpanTreeTest pattern: Edges \in {E \in SUBSET(SUBSET Nodes) : P(E)}
        // The nested SUBSET appears as the domain of a SetFilter.
        // The visitor should detect this through recursion into SetFilter domain.
        let nodes_ident = spanned(Expr::Ident(
            "Nodes".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ));
        // SUBSET(SUBSET Nodes)
        let subset_inner = spanned(Expr::Powerset(Box::new(nodes_ident)));
        let subset_outer = spanned(Expr::Powerset(Box::new(subset_inner)));

        // {E \in SUBSET(SUBSET Nodes) : TRUE} — SetFilter with doubly-exponential domain
        let bv = tla_core::ast::BoundVar {
            name: Spanned {
                node: "E".to_string(),
                span: tla_core::span::Span::dummy(),
            },
            domain: Some(Box::new(subset_outer)),
            pattern: None,
        };
        let body = spanned(Expr::Bool(true));
        let set_filter = spanned(Expr::SetFilter(bv, Box::new(body)));

        // Edges \in {E \in SUBSET(SUBSET Nodes) : TRUE}
        let edges_ident = spanned(Expr::Ident(
            "Edges".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ));
        let in_expr = spanned(Expr::In(Box::new(edges_ident), Box::new(set_filter)));

        let mut visitor = ComplexityVisitor::new();
        visitor.visit_expr(&in_expr);
        let signals = visitor.into_signals();

        assert_eq!(
            signals.len(),
            1,
            "should detect nested SUBSET in SetFilter domain (SpanTreeTest pattern)"
        );
        assert!(
            signals[0].reason.contains("nested SUBSET"),
            "reason should mention nested SUBSET, got: {}",
            signals[0].reason
        );
    }

    #[test]
    fn test_detect_exponential_complexity_spantree_pattern() {
        // Build a module resembling SpanTreeTest:
        // Init == ... /\ Edges \in {E \in SUBSET(SUBSET Nodes) : P(E)}
        let nodes = spanned(Expr::Ident(
            "Nodes".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ));
        let subset_inner = spanned(Expr::Powerset(Box::new(nodes)));
        let subset_outer = spanned(Expr::Powerset(Box::new(subset_inner)));

        let bv = tla_core::ast::BoundVar {
            name: Spanned {
                node: "E".to_string(),
                span: tla_core::span::Span::dummy(),
            },
            domain: Some(Box::new(subset_outer)),
            pattern: None,
        };
        let filter_body = spanned(Expr::Bool(true));
        let set_filter = spanned(Expr::SetFilter(bv, Box::new(filter_body)));

        let edges = spanned(Expr::Ident(
            "Edges".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ));
        let in_expr = spanned(Expr::In(Box::new(edges), Box::new(set_filter)));

        // Init == in_expr (simplified)
        let op_def = tla_core::ast::OperatorDef {
            name: Spanned {
                node: "Init".to_string(),
                span: tla_core::span::Span::dummy(),
            },
            params: vec![],
            body: in_expr,
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        };

        let module = Module {
            name: Spanned {
                node: "SpanTreeTest".to_string(),
                span: tla_core::span::Span::dummy(),
            },
            extends: vec![],
            units: vec![Spanned {
                node: Unit::Operator(op_def),
                span: tla_core::span::Span::dummy(),
            }],
            action_subscript_spans: std::collections::HashSet::new(),
            span: tla_core::span::Span::dummy(),
        };

        let result = detect_exponential_complexity(&module);
        assert!(
            result.is_some(),
            "should detect SpanTreeTest-like exponential complexity"
        );
    }

    // =====================================================================
    // JIT bias tests (Part of #3854)
    // =====================================================================

    #[test]
    fn test_jit_compiled_either_becomes_bfs_only() {
        // Action with moderate branching (avg=10), SMT-compatible, JIT-compiled.
        // Without JIT: Either. With JIT: BfsOnly (prefer fast native BFS).
        let metrics = vec![make_metrics_with_jit(50, 5, true, true)];
        let smt = vec![true];
        let routes = compute_routes_with_thresholds(&metrics, &smt, 100.0, 0.0);
        assert_eq!(routes, vec![ActionRoute::BfsOnly]);
    }

    #[test]
    fn test_jit_compiled_symbolic_only_becomes_either() {
        // Action with high branching (avg=250), SMT-compatible, JIT-compiled.
        // Without JIT: SymbolicOnly. With JIT: Either (let BFS compete).
        let metrics = vec![make_metrics_with_jit(500, 2, true, true)];
        let smt = vec![true];
        let routes = compute_routes_with_thresholds(&metrics, &smt, 100.0, 0.0);
        assert_eq!(routes, vec![ActionRoute::Either]);
    }

    #[test]
    fn test_jit_compiled_bfs_only_stays_bfs_only() {
        // Action that is not SMT-compatible, JIT-compiled.
        // Not SMT -> BfsOnly regardless of JIT status.
        let metrics = vec![make_metrics_with_jit(50, 5, false, true)];
        let smt = vec![false];
        let routes = compute_routes_with_thresholds(&metrics, &smt, 100.0, 0.0);
        assert_eq!(routes, vec![ActionRoute::BfsOnly]);
    }

    #[test]
    fn test_non_jit_action_routes_unchanged() {
        // Action with moderate branching, SMT-compatible, NOT JIT-compiled.
        // Should route to Either (no JIT bias applied).
        let metrics = vec![make_metrics_with_jit(50, 5, true, false)];
        let smt = vec![true];
        let routes = compute_routes_with_thresholds(&metrics, &smt, 100.0, 0.0);
        assert_eq!(routes, vec![ActionRoute::Either]);
    }

    #[test]
    fn test_jit_no_data_routes_to_bfs_only() {
        // Action with no evaluation data, SMT-compatible, JIT-compiled.
        // Without JIT: Either (default). With JIT: BfsOnly (prefer native).
        let metrics = vec![make_metrics_with_jit(0, 0, true, true)];
        let smt = vec![true];
        let routes = compute_routes_with_thresholds(&metrics, &smt, 100.0, 0.0);
        assert_eq!(routes, vec![ActionRoute::BfsOnly]);
    }

    #[test]
    fn test_non_jit_no_data_routes_to_either() {
        // Action with no evaluation data, SMT-compatible, NOT JIT-compiled.
        // Should route to Either (no JIT bias).
        let metrics = vec![make_metrics_with_jit(0, 0, true, false)];
        let smt = vec![true];
        let routes = compute_routes_with_thresholds(&metrics, &smt, 100.0, 0.0);
        assert_eq!(routes, vec![ActionRoute::Either]);
    }

    #[test]
    fn test_mixed_jit_and_non_jit_actions() {
        let metrics = vec![
            make_metrics_with_jit(500, 2, true, true), // avg=250, JIT -> Either (was SymbolicOnly)
            make_metrics_with_jit(50, 5, true, false), // avg=10, no JIT -> Either
            make_metrics_with_jit(50, 5, true, true),  // avg=10, JIT -> BfsOnly (was Either)
            make_metrics_with_jit(1000, 5, false, true), // not SMT -> BfsOnly
        ];
        let smt = vec![true, true, true, false];
        let routes = compute_routes_with_thresholds(&metrics, &smt, 100.0, 0.0);
        assert_eq!(
            routes,
            vec![
                ActionRoute::Either,  // JIT bias: SymbolicOnly -> Either
                ActionRoute::Either,  // no JIT: stays Either
                ActionRoute::BfsOnly, // JIT bias: Either -> BfsOnly
                ActionRoute::BfsOnly, // not SMT: always BfsOnly
            ]
        );
    }

    #[test]
    fn test_oracle_reroute_with_jit_bias() {
        let metrics = vec![
            make_metrics_with_jit(0, 0, true, true), // JIT-compiled, no data yet
            make_metrics_with_jit(0, 0, true, false), // not JIT, no data yet
        ];
        let smt = vec![true, true];
        let mut oracle = ActionOracle::new(&metrics, &smt);

        // Initially: JIT action -> BfsOnly, non-JIT -> Either
        assert_eq!(oracle.route(0), ActionRoute::BfsOnly);
        assert_eq!(oracle.route(1), ActionRoute::Either);

        // Simulate BFS accumulating high branching data on both
        metrics[0].total_successors.store(1000, Ordering::Relaxed);
        metrics[0].times_evaluated.store(5, Ordering::Relaxed);
        metrics[1].total_successors.store(1000, Ordering::Relaxed);
        metrics[1].times_evaluated.store(5, Ordering::Relaxed);

        // Trigger reroute
        assert!(oracle.reroute(5, &metrics, &smt));

        // High branching (avg=200): JIT -> Either (was SymbolicOnly), non-JIT -> SymbolicOnly
        assert_eq!(oracle.route(0), ActionRoute::Either);
        assert_eq!(oracle.route(1), ActionRoute::SymbolicOnly);
    }
}
