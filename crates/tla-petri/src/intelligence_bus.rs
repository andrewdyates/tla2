// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Intelligence bus for cross-technique cooperation in Petri net model checking.
//!
//! The intelligence bus is a thread-safe shared state that enables different
//! verification techniques (BFS, LP, PDR/IC3, BMC, k-induction) to share
//! discoveries in real time:
//!
//! - **BFS → IC3**: frontier fingerprints seed IC3 initial states
//! - **IC3/LP → BFS**: proved invariants prune the BFS search space
//! - **LP → all**: place bounds tighten analyses across all techniques
//! - **Any → all**: counterexamples and verdicts short-circuit everything
//!
//! # Thread safety
//!
//! All operations use lock-free or fine-grained locking:
//! - `DashSet` for frontier fingerprints (lock-free concurrent insert/contains)
//! - `RwLock` for invariants and bounds (many readers, rare writers)
//! - `Mutex` for counterexample traces (rare writes, no hot path)
//! - `AtomicBool` + `Mutex<Option<Verdict>>` for verdict (write-once)
//!
//! The bus is designed for the pipeline's sequential phases but is safe for
//! concurrent access if techniques are run in parallel threads.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

use dashmap::DashSet;
use parking_lot::{Mutex, RwLock};

use crate::output::Verdict;
use crate::petri_net::PlaceIdx;

// ---------------------------------------------------------------------------
// LinearConstraint — proved linear invariant over place markings
// ---------------------------------------------------------------------------

/// Comparison operator for linear constraints.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Comparison {
    /// sum(coefficients[i] * marking[place_i]) <= rhs
    Leq,
    /// sum(coefficients[i] * marking[place_i]) >= rhs
    Geq,
    /// sum(coefficients[i] * marking[place_i]) == rhs
    Eq,
}

/// A linear constraint over place markings.
///
/// Represents: `sum(coeff_i * tokens(place_i))  <op>  rhs`
///
/// These are published by IC3 (frame lemmas) and LP (P-invariants, bounds).
/// BFS uses them to prune unreachable successor markings.
#[derive(Debug, Clone)]
pub(crate) struct LinearConstraint {
    /// Place-coefficient pairs. Only non-zero coefficients are stored.
    pub coefficients: Vec<(PlaceIdx, i64)>,
    /// Comparison operator.
    pub comparison: Comparison,
    /// Right-hand side constant.
    pub rhs: i64,
}

impl LinearConstraint {
    /// Evaluate this constraint against a concrete marking.
    ///
    /// Returns `true` if the marking satisfies the constraint.
    #[must_use]
    pub fn evaluate(&self, marking: &[u64]) -> bool {
        let lhs: i64 = self
            .coefficients
            .iter()
            .map(|(place, coeff)| coeff * marking[place.0 as usize] as i64)
            .sum();
        match self.comparison {
            Comparison::Leq => lhs <= self.rhs,
            Comparison::Geq => lhs >= self.rhs,
            Comparison::Eq => lhs == self.rhs,
        }
    }
}

// ---------------------------------------------------------------------------
// Trace — counterexample trace (sequence of transition firings)
// ---------------------------------------------------------------------------

/// A counterexample trace: a sequence of markings leading to a property violation.
#[derive(Debug, Clone)]
pub(crate) struct Trace {
    /// Sequence of markings (each is a vector of token counts per place).
    pub markings: Vec<Vec<u64>>,
}

// ---------------------------------------------------------------------------
// IntelligenceBus
// ---------------------------------------------------------------------------

/// Thread-safe shared state for cross-technique cooperation.
///
/// Created once per examination run and shared (via `Arc`) among all
/// verification technique threads/phases.
pub(crate) struct IntelligenceBus {
    /// Fingerprints of states discovered by BFS.
    ///
    /// BFS publishes frontier fingerprints here; IC3 can use them to seed
    /// its initial frame or check reachability of candidate states.
    reachable_states: DashSet<u64>,

    /// Proved linear invariants over place markings.
    ///
    /// Published by IC3 (frame lemmas) and LP (P-invariants).
    /// BFS checks `check_pruned()` to skip successors that violate
    /// any proved invariant.
    invariants: RwLock<Vec<LinearConstraint>>,

    /// LP-proven upper bounds on individual place token counts.
    ///
    /// Published by LP at startup. Used by all techniques to tighten
    /// search spaces.
    bounds: RwLock<HashMap<PlaceIdx, u64>>,

    /// Counterexample traces found by any technique.
    counterexamples: Mutex<Vec<Trace>>,

    /// First definitive verdict. Write-once: the first technique to
    /// publish a verdict wins.
    verdict_set: AtomicBool,
    verdict: Mutex<Option<Verdict>>,

    /// Statistics counters for observability.
    stats: BusStats,
}

/// Counters for intelligence bus activity.
struct BusStats {
    frontier_publishes: AtomicU64,
    invariant_publishes: AtomicU64,
    pruned_checks: AtomicU64,
    pruned_hits: AtomicU64,
}

impl IntelligenceBus {
    /// Create a new, empty intelligence bus.
    #[must_use]
    pub fn new() -> Self {
        Self {
            reachable_states: DashSet::new(),
            invariants: RwLock::new(Vec::new()),
            bounds: RwLock::new(HashMap::new()),
            counterexamples: Mutex::new(Vec::new()),
            verdict_set: AtomicBool::new(false),
            verdict: Mutex::new(None),
            stats: BusStats {
                frontier_publishes: AtomicU64::new(0),
                invariant_publishes: AtomicU64::new(0),
                pruned_checks: AtomicU64::new(0),
                pruned_hits: AtomicU64::new(0),
            },
        }
    }

    // -- Frontier (BFS → IC3) ------------------------------------------------

    /// Publish BFS frontier state fingerprints.
    ///
    /// Called by BFS after expanding a batch of states. IC3 can query
    /// these to seed its initial frame or check if a candidate state
    /// has been concretely reached.
    pub fn publish_frontier(&self, states: &[u64]) {
        for &fp in states {
            self.reachable_states.insert(fp);
        }
        self.stats
            .frontier_publishes
            .fetch_add(states.len() as u64, Ordering::Relaxed);
    }

    /// Check if a state fingerprint was seen by BFS.
    #[must_use]
    pub fn is_reachable(&self, fingerprint: u64) -> bool {
        self.reachable_states.contains(&fingerprint)
    }

    /// Number of unique reachable state fingerprints published.
    #[must_use]
    pub fn reachable_count(&self) -> usize {
        self.reachable_states.len()
    }

    // -- Invariants (IC3/LP → BFS) -------------------------------------------

    /// Publish a proved linear invariant.
    ///
    /// Called by IC3 when a frame lemma is proved, or by LP when a
    /// P-invariant or structural bound is established.
    pub fn publish_invariant(&self, constraint: LinearConstraint) {
        self.invariants.write().push(constraint);
        self.stats
            .invariant_publishes
            .fetch_add(1, Ordering::Relaxed);
    }

    /// Publish multiple proved invariants at once.
    pub fn publish_invariants(&self, constraints: Vec<LinearConstraint>) {
        let count = constraints.len() as u64;
        self.invariants.write().extend(constraints);
        self.stats
            .invariant_publishes
            .fetch_add(count, Ordering::Relaxed);
    }

    /// Check if a marking violates any proved invariant.
    ///
    /// Returns `true` if the marking should be pruned (violates at least
    /// one invariant). Called by BFS before adding a successor to the
    /// frontier.
    ///
    /// This is on the BFS hot path. The read lock allows concurrent
    /// checking from multiple BFS threads without blocking.
    #[must_use]
    pub fn check_pruned(&self, marking: &[u64]) -> bool {
        self.stats.pruned_checks.fetch_add(1, Ordering::Relaxed);
        let invariants = self.invariants.read();
        for constraint in invariants.iter() {
            if !constraint.evaluate(marking) {
                self.stats.pruned_hits.fetch_add(1, Ordering::Relaxed);
                return true;
            }
        }
        false
    }

    /// Number of proved invariants currently on the bus.
    #[must_use]
    pub fn invariant_count(&self) -> usize {
        self.invariants.read().len()
    }

    // -- Bounds (LP → all) ---------------------------------------------------

    /// Publish LP-proven place bounds.
    ///
    /// Merges with existing bounds, keeping the tighter (lower) bound
    /// for each place.
    pub fn publish_bounds(&self, new_bounds: HashMap<PlaceIdx, u64>) {
        let mut bounds = self.bounds.write();
        for (place, bound) in new_bounds {
            bounds
                .entry(place)
                .and_modify(|existing| *existing = (*existing).min(bound))
                .or_insert(bound);
        }
    }

    /// Get the current known bounds for all places.
    #[must_use]
    pub fn get_bounds(&self) -> HashMap<PlaceIdx, u64> {
        self.bounds.read().clone()
    }

    /// Get the bound for a specific place, if known.
    #[must_use]
    pub fn get_place_bound(&self, place: PlaceIdx) -> Option<u64> {
        self.bounds.read().get(&place).copied()
    }

    // -- Counterexamples (any → all) -----------------------------------------

    /// Publish a counterexample trace.
    ///
    /// Any technique that finds a concrete property violation publishes
    /// the trace here. Also sets the verdict to `False` if no verdict
    /// has been published yet.
    pub fn publish_counterexample(&self, trace: Trace) {
        self.counterexamples.lock().push(trace);
        // A counterexample means the property is violated.
        self.try_publish_verdict(Verdict::False);
    }

    /// Get all published counterexample traces.
    #[must_use]
    pub fn get_counterexamples(&self) -> Vec<Trace> {
        self.counterexamples.lock().clone()
    }

    // -- Verdict (any → abort all) -------------------------------------------

    /// Try to publish a definitive verdict.
    ///
    /// Returns `true` if this was the first verdict published.
    /// Subsequent calls are no-ops (first writer wins).
    pub fn try_publish_verdict(&self, v: Verdict) -> bool {
        // Fast path: already set.
        if self.verdict_set.load(Ordering::Acquire) {
            return false;
        }
        // Slow path: acquire the lock and set if still unset.
        let mut verdict = self.verdict.lock();
        if verdict.is_some() {
            return false;
        }
        *verdict = Some(v);
        self.verdict_set.store(true, Ordering::Release);
        true
    }

    /// Poll for a definitive verdict.
    ///
    /// Returns `Some(verdict)` if any technique has published a final answer.
    /// This is a cheap atomic check on the fast path.
    #[must_use]
    pub fn poll_verdict(&self) -> Option<Verdict> {
        if self.verdict_set.load(Ordering::Acquire) {
            *self.verdict.lock()
        } else {
            None
        }
    }

    /// Check if a verdict has been published (fast atomic check).
    #[must_use]
    pub fn has_verdict(&self) -> bool {
        self.verdict_set.load(Ordering::Acquire)
    }

    // -- Statistics -----------------------------------------------------------

    /// Log a summary of bus activity to stderr.
    pub fn log_summary(&self) {
        let frontier = self.stats.frontier_publishes.load(Ordering::Relaxed);
        let invariants = self.stats.invariant_publishes.load(Ordering::Relaxed);
        let checks = self.stats.pruned_checks.load(Ordering::Relaxed);
        let hits = self.stats.pruned_hits.load(Ordering::Relaxed);
        let bounds_count = self.bounds.read().len();

        if frontier > 0 || invariants > 0 || checks > 0 {
            eprintln!(
                "IntelligenceBus: {} frontier states, {} invariants, {} bounds, \
                 {}/{} pruning checks hit",
                frontier, invariants, bounds_count, hits, checks,
            );
        }
    }
}

// ---------------------------------------------------------------------------
// LP → IntelligenceBus bridge
// ---------------------------------------------------------------------------

/// Seed the intelligence bus with LP-derived place bounds.
///
/// For each place in the net, computes the LP upper bound and publishes
/// it to the bus. Also converts P-invariants into `LinearConstraint`s.
pub(crate) fn seed_from_lp(bus: &IntelligenceBus, net: &crate::petri_net::PetriNet) {
    use crate::lp_state_equation::lp_upper_bound;

    // Publish per-place LP upper bounds.
    let mut bounds = HashMap::new();
    for p in 0..net.num_places() {
        if let Some(bound) = lp_upper_bound(net, &[PlaceIdx(p as u32)]) {
            bounds.insert(PlaceIdx(p as u32), bound);
        }
    }
    if !bounds.is_empty() {
        let count = bounds.len();
        bus.publish_bounds(bounds.clone());

        // Convert bounds to invariants for pruning:
        // tokens(place_i) <= bound_i
        let invariants: Vec<LinearConstraint> = bounds
            .into_iter()
            .map(|(place, bound)| LinearConstraint {
                coefficients: vec![(place, 1)],
                comparison: Comparison::Leq,
                rhs: bound as i64,
            })
            .collect();
        bus.publish_invariants(invariants);

        eprintln!("IntelligenceBus: LP seeded {count} place bounds");
    }

    // Convert P-invariants to linear equality constraints.
    let p_invariants = crate::invariant::compute_p_invariants(net);
    if !p_invariants.is_empty() {
        let constraints: Vec<LinearConstraint> = p_invariants
            .iter()
            .map(|inv| {
                let coefficients: Vec<(PlaceIdx, i64)> = inv
                    .weights
                    .iter()
                    .enumerate()
                    .filter(|(_, &w)| w > 0)
                    .map(|(p, &w)| (PlaceIdx(p as u32), w as i64))
                    .collect();
                LinearConstraint {
                    coefficients,
                    comparison: Comparison::Eq,
                    rhs: inv.token_count as i64,
                }
            })
            .collect();
        let count = constraints.len();
        bus.publish_invariants(constraints);
        eprintln!("IntelligenceBus: published {count} P-invariant constraints");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};

    fn place(id: &str) -> PlaceInfo {
        PlaceInfo {
            id: id.to_string(),
            name: None,
        }
    }

    fn arc(place: u32, weight: u64) -> Arc {
        Arc {
            place: PlaceIdx(place),
            weight,
        }
    }

    fn trans(id: &str, inputs: Vec<Arc>, outputs: Vec<Arc>) -> TransitionInfo {
        TransitionInfo {
            id: id.to_string(),
            name: None,
            inputs,
            outputs,
        }
    }

    fn conserving_net() -> PetriNet {
        PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
            initial_marking: vec![3, 0],
        }
    }

    #[test]
    fn test_linear_constraint_leq_satisfied() {
        let constraint = LinearConstraint {
            coefficients: vec![(PlaceIdx(0), 1)],
            comparison: Comparison::Leq,
            rhs: 5,
        };
        assert!(constraint.evaluate(&[3, 0]));
        assert!(constraint.evaluate(&[5, 0]));
        assert!(!constraint.evaluate(&[6, 0]));
    }

    #[test]
    fn test_linear_constraint_geq_satisfied() {
        let constraint = LinearConstraint {
            coefficients: vec![(PlaceIdx(1), 1)],
            comparison: Comparison::Geq,
            rhs: 2,
        };
        assert!(!constraint.evaluate(&[0, 1]));
        assert!(constraint.evaluate(&[0, 2]));
        assert!(constraint.evaluate(&[0, 3]));
    }

    #[test]
    fn test_linear_constraint_eq_satisfied() {
        // P-invariant: p0 + p1 = 3
        let constraint = LinearConstraint {
            coefficients: vec![(PlaceIdx(0), 1), (PlaceIdx(1), 1)],
            comparison: Comparison::Eq,
            rhs: 3,
        };
        assert!(constraint.evaluate(&[3, 0]));
        assert!(constraint.evaluate(&[2, 1]));
        assert!(constraint.evaluate(&[0, 3]));
        assert!(!constraint.evaluate(&[2, 2]));
    }

    #[test]
    fn test_bus_verdict_first_writer_wins() {
        let bus = IntelligenceBus::new();
        assert!(bus.poll_verdict().is_none());

        assert!(bus.try_publish_verdict(Verdict::True));
        assert_eq!(bus.poll_verdict(), Some(Verdict::True));

        // Second write is a no-op.
        assert!(!bus.try_publish_verdict(Verdict::False));
        assert_eq!(bus.poll_verdict(), Some(Verdict::True));
    }

    #[test]
    fn test_bus_frontier_publish_and_query() {
        let bus = IntelligenceBus::new();
        assert_eq!(bus.reachable_count(), 0);
        assert!(!bus.is_reachable(42));

        bus.publish_frontier(&[42, 43, 44]);
        assert_eq!(bus.reachable_count(), 3);
        assert!(bus.is_reachable(42));
        assert!(bus.is_reachable(44));
        assert!(!bus.is_reachable(99));
    }

    #[test]
    fn test_bus_invariant_pruning() {
        let bus = IntelligenceBus::new();

        // P-invariant: p0 + p1 = 3
        bus.publish_invariant(LinearConstraint {
            coefficients: vec![(PlaceIdx(0), 1), (PlaceIdx(1), 1)],
            comparison: Comparison::Eq,
            rhs: 3,
        });

        // Valid markings pass.
        assert!(!bus.check_pruned(&[3, 0]));
        assert!(!bus.check_pruned(&[1, 2]));

        // Invalid marking is pruned.
        assert!(bus.check_pruned(&[2, 2]));
    }

    #[test]
    fn test_bus_bounds_tighten() {
        let bus = IntelligenceBus::new();

        let mut bounds1 = HashMap::new();
        bounds1.insert(PlaceIdx(0), 10);
        bounds1.insert(PlaceIdx(1), 5);
        bus.publish_bounds(bounds1);

        assert_eq!(bus.get_place_bound(PlaceIdx(0)), Some(10));
        assert_eq!(bus.get_place_bound(PlaceIdx(1)), Some(5));

        // Tighter bound for p0, looser for p1 (should keep 5).
        let mut bounds2 = HashMap::new();
        bounds2.insert(PlaceIdx(0), 7);
        bounds2.insert(PlaceIdx(1), 8);
        bus.publish_bounds(bounds2);

        assert_eq!(bus.get_place_bound(PlaceIdx(0)), Some(7));
        assert_eq!(bus.get_place_bound(PlaceIdx(1)), Some(5));
    }

    #[test]
    fn test_bus_counterexample_sets_verdict() {
        let bus = IntelligenceBus::new();

        bus.publish_counterexample(Trace {
            markings: vec![vec![3, 0], vec![2, 1]],
        });

        assert_eq!(bus.poll_verdict(), Some(Verdict::False));
        assert_eq!(bus.get_counterexamples().len(), 1);
    }

    #[test]
    fn test_bus_has_verdict_fast_check() {
        let bus = IntelligenceBus::new();
        assert!(!bus.has_verdict());

        bus.try_publish_verdict(Verdict::True);
        assert!(bus.has_verdict());
    }

    #[test]
    fn test_seed_from_lp_conserving_net() {
        let net = conserving_net();
        let bus = IntelligenceBus::new();

        seed_from_lp(&bus, &net);

        // Conserving net: p0 + p1 = 3, so both places bounded by 3.
        assert_eq!(bus.get_place_bound(PlaceIdx(0)), Some(3));
        assert_eq!(bus.get_place_bound(PlaceIdx(1)), Some(3));

        // Should have at least LP bounds + P-invariant constraints.
        assert!(bus.invariant_count() >= 2);

        // P-invariant should prune markings that violate conservation.
        assert!(bus.check_pruned(&[4, 0])); // sum = 4 > 3
        assert!(!bus.check_pruned(&[2, 1])); // sum = 3, ok
    }

    #[test]
    fn test_bus_empty_has_no_effect() {
        let bus = IntelligenceBus::new();

        // Empty bus should not prune anything.
        assert!(!bus.check_pruned(&[100, 200, 300]));
        assert!(bus.poll_verdict().is_none());
        assert!(!bus.has_verdict());
        assert_eq!(bus.reachable_count(), 0);
        assert!(bus.get_bounds().is_empty());
        assert_eq!(bus.invariant_count(), 0);
    }

    #[test]
    fn test_linear_constraint_weighted_sum() {
        // 2*p0 + 3*p1 <= 10
        let constraint = LinearConstraint {
            coefficients: vec![(PlaceIdx(0), 2), (PlaceIdx(1), 3)],
            comparison: Comparison::Leq,
            rhs: 10,
        };
        assert!(constraint.evaluate(&[2, 2])); // 4 + 6 = 10
        assert!(!constraint.evaluate(&[3, 2])); // 6 + 6 = 12
        assert!(constraint.evaluate(&[1, 1])); // 2 + 3 = 5
    }
}
