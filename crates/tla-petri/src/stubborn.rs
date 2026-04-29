// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Stubborn set partial-order reduction for Petri net BFS exploration.
//!
//! Implements Valmari (1990) / Schmidt (2000) stubborn sets to reduce
//! the explored state space while preserving safety and deadlock properties.
//! At each BFS state, only a subset of enabled transitions (the "stubborn set")
//! is fired, skipping interleavings of independent transitions.
//!
//! Reference: Schmidt, K. (2000). "Stubborn Sets for Standard Properties."
//! ICATPN 2000, LNCS 1825.

use crate::petri_net::{PetriNet, TransitionIdx};

/// Pre-computed transition dependency information for stubborn set computation.
///
/// Built once from the net structure before BFS begins. Construction is
/// O(|T| × max_arcs + |P|) — negligible vs the BFS itself.
pub(crate) struct DependencyGraph {
    /// For each transition t, transitions that can newly enable t by
    /// adding tokens to one of t's input places.
    #[cfg_attr(not(test), allow(dead_code))]
    can_enable: Vec<Vec<TransitionIdx>>,
    /// For each transition t, transitions that share an input or output
    /// place with t (firing one may change whether the other is enabled
    /// or alter the result of firing it).
    interferes_with: Vec<Vec<TransitionIdx>>,
    /// For each place p, transitions that produce tokens into p
    /// (have p as an output arc).
    producers: Vec<Vec<TransitionIdx>>,
    /// For each place p, transitions that consume tokens from p
    /// (have p as an input arc).
    #[cfg_attr(not(test), allow(dead_code))]
    consumers: Vec<Vec<TransitionIdx>>,
}

/// Partial-order reduction strategy controlling which transitions to explore.
#[derive(Debug, Clone)]
pub(crate) enum PorStrategy {
    /// No reduction — explore all enabled transitions (current behavior).
    None,
    /// Deadlock-preserving stubborn sets (D1+D2).
    /// Safe for: ReachabilityDeadlock.
    DeadlockPreserving,
    /// Safety-preserving stubborn sets (D1+D2+visibility).
    /// Safe for: all safety properties (OneSafe, StableMarking,
    /// UpperBounds, Reachability*).
    /// `visible` lists transitions that can affect the property being checked.
    #[cfg_attr(not(test), allow(dead_code))]
    SafetyPreserving { visible: Vec<TransitionIdx> },
}

/// Aggregated partial-order reduction statistics across explored states.
#[derive(Debug, Clone, Default)]
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) struct PorStats {
    pub(crate) states_with_reduction: u64,
    pub(crate) states_without_reduction: u64,
    pub(crate) transitions_pruned: u64,
    pub(crate) transitions_total: u64,
}

impl PorStats {
    /// Fraction of enabled transitions pruned by POR across all tracked states.
    #[must_use]
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn reduction_ratio(&self) -> f64 {
        if self.transitions_total == 0 {
            return 0.0;
        }

        self.transitions_pruned as f64 / self.transitions_total as f64
    }
}

/// Convenience wrapper for tracked stubborn-set computation.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) struct PorStatsCollector<'a> {
    dep: &'a DependencyGraph,
    stats: PorStats,
}

impl<'a> PorStatsCollector<'a> {
    #[must_use]
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn new(dep: &'a DependencyGraph) -> Self {
        Self {
            dep,
            stats: PorStats::default(),
        }
    }

    #[must_use]
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn dependency_graph(&self) -> &DependencyGraph {
        self.dep
    }

    #[must_use]
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn stats(&self) -> &PorStats {
        &self.stats
    }

    #[must_use]
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn into_stats(self) -> PorStats {
        self.stats
    }

    #[cfg_attr(not(test), allow(dead_code))]
    fn record(&mut self, enabled_total: usize, stubborn: Option<&[TransitionIdx]>) {
        self.stats.transitions_total += enabled_total as u64;
        match stubborn {
            Some(transitions) => {
                self.stats.states_with_reduction += 1;
                self.stats.transitions_pruned += (enabled_total - transitions.len()) as u64;
            }
            None => {
                self.stats.states_without_reduction += 1;
            }
        }
    }
}

impl DependencyGraph {
    /// Build the dependency graph from a Petri net's structure.
    ///
    /// One pass over all arcs: O(sum of arc counts across all transitions).
    pub(crate) fn build(net: &PetriNet) -> Self {
        let num_transitions = net.num_transitions();
        let num_places = net.num_places();

        // Step 1: build per-place producer/consumer lists.
        let mut producers: Vec<Vec<TransitionIdx>> = vec![Vec::new(); num_places];
        let mut consumers: Vec<Vec<TransitionIdx>> = vec![Vec::new(); num_places];

        for (tidx, t) in net.transitions.iter().enumerate() {
            let ti = TransitionIdx(tidx as u32);
            for arc in &t.outputs {
                producers[arc.place.0 as usize].push(ti);
            }
            for arc in &t.inputs {
                consumers[arc.place.0 as usize].push(ti);
            }
        }

        // Step 2: build can_enable[t] = union of producers[p] for all input places p of t.
        let mut can_enable: Vec<Vec<TransitionIdx>> = Vec::with_capacity(num_transitions);
        for t in &net.transitions {
            let mut enablers = Vec::new();
            for arc in &t.inputs {
                for &prod in &producers[arc.place.0 as usize] {
                    enablers.push(prod);
                }
            }
            enablers.sort_unstable_by_key(|t| t.0);
            enablers.dedup();
            can_enable.push(enablers);
        }

        // Step 3: build interferes_with[t] = transitions sharing any input or output
        // place with t (excluding t itself).
        let mut interferes_with: Vec<Vec<TransitionIdx>> = Vec::with_capacity(num_transitions);
        for (tidx, t) in net.transitions.iter().enumerate() {
            let ti = TransitionIdx(tidx as u32);
            let mut neighbors = Vec::new();
            // Transitions consuming from the same input places (compete for tokens).
            for arc in &t.inputs {
                for &con in &consumers[arc.place.0 as usize] {
                    if con != ti {
                        neighbors.push(con);
                    }
                }
                // Transitions producing to our input places can change our enabledness.
                for &prod in &producers[arc.place.0 as usize] {
                    if prod != ti {
                        neighbors.push(prod);
                    }
                }
            }
            // Transitions consuming from our output places (we produce, they consume
            // from the same place — firing order matters).
            for arc in &t.outputs {
                for &con in &consumers[arc.place.0 as usize] {
                    if con != ti {
                        neighbors.push(con);
                    }
                }
                // Transitions producing to the same output place — commutative for
                // token counts, but included for completeness (Schmidt 2000 includes
                // all transitions on shared places in the interference set).
                for &prod in &producers[arc.place.0 as usize] {
                    if prod != ti {
                        neighbors.push(prod);
                    }
                }
            }
            neighbors.sort_unstable_by_key(|t| t.0);
            neighbors.dedup();
            interferes_with.push(neighbors);
        }

        Self {
            can_enable,
            interferes_with,
            producers,
            consumers,
        }
    }

    /// Number of transitions in the dependency graph.
    #[cfg(test)]
    fn num_transitions(&self) -> usize {
        self.can_enable.len()
    }

    /// Producers for a given place.
    #[cfg(test)]
    fn place_producers(&self, p: usize) -> &[TransitionIdx] {
        &self.producers[p]
    }

    /// Consumers for a given place.
    #[cfg(test)]
    fn place_consumers(&self, p: usize) -> &[TransitionIdx] {
        &self.consumers[p]
    }
}

/// Compute the stubborn set for a given marking under the specified strategy.
///
/// Returns the subset of transition indices to fire at this state.
/// When the computed stubborn set equals the full enabled set (no reduction),
/// returns `None` to signal the caller should fire all enabled transitions.
///
/// For `PorStrategy::None`, always returns `None`.
pub(crate) fn compute_stubborn_set(
    net: &PetriNet,
    marking: &[u64],
    dep: &DependencyGraph,
    strategy: &PorStrategy,
) -> Option<Vec<TransitionIdx>> {
    match strategy {
        PorStrategy::None => None,
        PorStrategy::DeadlockPreserving => compute_deadlock_preserving(net, marking, dep),
        PorStrategy::SafetyPreserving { visible } => {
            compute_safety_preserving(net, marking, dep, visible)
        }
    }
}

/// Compute a stubborn set and update aggregate POR statistics.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn compute_stubborn_set_tracked(
    net: &PetriNet,
    marking: &[u64],
    collector: &mut PorStatsCollector<'_>,
    strategy: &PorStrategy,
) -> Option<Vec<TransitionIdx>> {
    let enabled_total = count_enabled_transitions(net, marking);
    let stubborn = compute_stubborn_set(net, marking, collector.dependency_graph(), strategy);
    collector.record(enabled_total, stubborn.as_deref());
    stubborn
}

#[cfg_attr(not(test), allow(dead_code))]
fn count_enabled_transitions(net: &PetriNet, marking: &[u64]) -> usize {
    let mut enabled = 0usize;
    for tidx in 0..net.num_transitions() {
        if net.is_enabled(marking, TransitionIdx(tidx as u32)) {
            enabled += 1;
        }
    }
    enabled
}

/// Deadlock-preserving stubborn set (D1+D2).
///
/// Algorithm (Schmidt 2000):
/// 1. Find all enabled transitions E(s).
/// 2. If |E(s)| ≤ 1, no reduction possible.
/// 3. Pick seed t₀ ∈ E(s) with fewest dependencies (heuristic).
/// 4. Close T_s under D2: for enabled t, add interferes_with[t];
///    for disabled t, find key place p and add producers[p].
/// 5. Return T_s ∩ E(s).
fn compute_deadlock_preserving(
    net: &PetriNet,
    marking: &[u64],
    dep: &DependencyGraph,
) -> Option<Vec<TransitionIdx>> {
    let num_transitions = net.num_transitions();

    // Find all enabled transitions.
    let mut enabled = Vec::new();
    for tidx in 0..num_transitions {
        let ti = TransitionIdx(tidx as u32);
        if net.is_enabled(marking, ti) {
            enabled.push(ti);
        }
    }

    // Deadlock state or single enabled transition: no reduction possible.
    if enabled.len() <= 1 {
        return None;
    }

    // Pick seed: enabled transition with smallest interference set (heuristic).
    let seed = *enabled
        .iter()
        .min_by_key(|t| dep.interferes_with[t.0 as usize].len())
        .expect("enabled is non-empty");

    // Closure: BFS over dependency graph.
    let mut in_stubborn = vec![false; num_transitions];
    let mut worklist = Vec::new();

    in_stubborn[seed.0 as usize] = true;
    worklist.push(seed);

    while let Some(t) = worklist.pop() {
        if net.is_enabled(marking, t) {
            // D2 for enabled transitions: add all interfering transitions.
            for &neighbor in &dep.interferes_with[t.0 as usize] {
                if !in_stubborn[neighbor.0 as usize] {
                    in_stubborn[neighbor.0 as usize] = true;
                    worklist.push(neighbor);
                }
            }
        } else {
            // D2 for disabled transitions: find key place (insufficiently marked
            // input), add all producers of that key place.
            // Heuristic: pick the key place with fewest producers.
            let trans_info = &net.transitions[t.0 as usize];
            let key_place = trans_info
                .inputs
                .iter()
                .filter(|arc| marking[arc.place.0 as usize] < arc.weight)
                .min_by_key(|arc| dep.producers[arc.place.0 as usize].len());

            if let Some(arc) = key_place {
                for &prod in &dep.producers[arc.place.0 as usize] {
                    if !in_stubborn[prod.0 as usize] {
                        in_stubborn[prod.0 as usize] = true;
                        worklist.push(prod);
                    }
                }
            }
        }
    }

    // Intersect stubborn set with enabled set.
    let result: Vec<TransitionIdx> = enabled
        .iter()
        .copied()
        .filter(|t| in_stubborn[t.0 as usize])
        .collect();

    // If no reduction achieved, signal caller to use the normal path.
    if result.len() >= enabled.len() {
        return None;
    }

    // D1 guarantee: at least one enabled transition is in the stubborn set
    // (the seed is enabled and in the set).
    debug_assert!(!result.is_empty());

    Some(result)
}

/// Safety-preserving stubborn set (D1+D2+visibility).
///
/// Same as deadlock-preserving, but additionally ensures that if any
/// visible transition is in the stubborn set, ALL visible transitions
/// are included. This prevents the reduced state space from hiding
/// a state where the safety property is violated.
fn compute_safety_preserving(
    net: &PetriNet,
    marking: &[u64],
    dep: &DependencyGraph,
    visible: &[TransitionIdx],
) -> Option<Vec<TransitionIdx>> {
    let num_transitions = net.num_transitions();

    // If all transitions are visible, POR gives no benefit.
    if visible.len() >= num_transitions {
        return None;
    }

    // Build visibility lookup.
    let mut is_visible = vec![false; num_transitions];
    for &v in visible {
        is_visible[v.0 as usize] = true;
    }

    // Find all enabled transitions.
    let mut enabled = Vec::new();
    for tidx in 0..num_transitions {
        let ti = TransitionIdx(tidx as u32);
        if net.is_enabled(marking, ti) {
            enabled.push(ti);
        }
    }

    if enabled.len() <= 1 {
        return None;
    }

    // Pick seed: if any visible transition is enabled, start from a visible
    // transition so safety-relevant work cannot be starved by independent
    // invisible transitions. Otherwise pick the enabled transition with the
    // smallest interference set.
    let seed = enabled
        .iter()
        .copied()
        .filter(|t| is_visible[t.0 as usize])
        .min_by_key(|t| dep.interferes_with[t.0 as usize].len())
        .or_else(|| {
            enabled
                .iter()
                .copied()
                .min_by_key(|t| dep.interferes_with[t.0 as usize].len())
        })
        .expect("enabled is non-empty");

    // Closure: same D2 as deadlock-preserving.
    let mut in_stubborn = vec![false; num_transitions];
    let mut worklist = Vec::new();

    in_stubborn[seed.0 as usize] = true;
    worklist.push(seed);

    // Track whether we've already expanded all visible transitions.
    let mut visible_expanded = false;

    while let Some(t) = worklist.pop() {
        // Visibility condition: if any visible transition enters the stubborn set,
        // include ALL visible transitions.
        if !visible_expanded && is_visible[t.0 as usize] {
            visible_expanded = true;
            for &v in visible {
                if !in_stubborn[v.0 as usize] {
                    in_stubborn[v.0 as usize] = true;
                    worklist.push(v);
                }
            }
        }

        if net.is_enabled(marking, t) {
            for &neighbor in &dep.interferes_with[t.0 as usize] {
                if !in_stubborn[neighbor.0 as usize] {
                    in_stubborn[neighbor.0 as usize] = true;
                    worklist.push(neighbor);
                }
            }
        } else {
            let trans_info = &net.transitions[t.0 as usize];
            let key_place = trans_info
                .inputs
                .iter()
                .filter(|arc| marking[arc.place.0 as usize] < arc.weight)
                .min_by_key(|arc| dep.producers[arc.place.0 as usize].len());

            if let Some(arc) = key_place {
                for &prod in &dep.producers[arc.place.0 as usize] {
                    if !in_stubborn[prod.0 as usize] {
                        in_stubborn[prod.0 as usize] = true;
                        worklist.push(prod);
                    }
                }
            }
        }
    }

    let result: Vec<TransitionIdx> = enabled
        .iter()
        .copied()
        .filter(|t| in_stubborn[t.0 as usize])
        .collect();

    if result.len() >= enabled.len() {
        return None;
    }

    debug_assert!(!result.is_empty());
    Some(result)
}

#[cfg(test)]
#[path = "stubborn_tests.rs"]
mod stubborn_tests;
