// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Petri net component decomposition via hypergraph min-cut partitioning.
//!
//! For loosely-coupled Petri nets, verifying each component independently
//! (then composing results via assume-guarantee) is exponentially faster
//! than checking the flat net. This module implements:
//!
//! 1. **Hypergraph construction** — places are vertices, transitions are
//!    hyperedges connecting all pre/post places, weighted by arc weight sum.
//! 2. **Balanced min-cut partitioning** — BFS-seeded growth splitting places
//!    into two groups, recursive until components are small enough or the
//!    normalized cut cost exceeds threshold THETA.
//! 3. **Per-component technique routing** — routes each component to AIGER
//!    (bounded, few latches), CHC/PDR (unbounded), or BFS (small state space).
//!
//! # References
//!
//! Christensen & Petrucci (2000) "Modular Analysis of Petri Nets"
//! Wimmel & Wolf (2012) "Applying CEGAR to the Petri Net State Equation"

use std::collections::VecDeque;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::invariant::structural_place_bounds;
use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};

/// Normalized cut threshold. If the interface cost ratio exceeds this,
/// the partition is too tightly coupled to decompose.
const THETA: f64 = 0.3;

/// A connected component of a decomposed Petri net.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Component {
    /// Places belonging to this component.
    pub(crate) places: Vec<PlaceIdx>,
    /// Transitions whose pre/post places are all within this component
    /// (or on the interface).
    pub(crate) transitions: Vec<TransitionIdx>,
    /// Places shared with other components (the interface).
    pub(crate) interface_places: Vec<PlaceIdx>,
}

/// Recommended verification technique for a component.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RecommendedTechnique {
    /// All places bounded and total latches <= 500: encode as AIGER circuit.
    Aiger,
    /// Some places unbounded: use CHC/PDR symbolic approach.
    ChcPdr,
    /// Small estimated state space (< 1M states): explicit BFS.
    Bfs,
}

/// A hyperedge in the place-connectivity hypergraph.
/// Each transition induces one hyperedge over all its pre/post places.
#[derive(Debug)]
struct Hyperedge {
    /// All places connected by this transition (union of input and output places).
    places: Vec<u32>,
    /// Weight = sum of all arc weights on this transition.
    weight: u64,
}

/// Build the hypergraph representation of the Petri net.
///
/// Each transition becomes a hyperedge connecting all its input and output
/// places. The edge weight is the sum of all arc weights (heavier coupling
/// = higher cost to cut).
fn build_hypergraph(net: &PetriNet) -> Vec<Hyperedge> {
    net.transitions
        .iter()
        .map(|t| {
            let mut place_set = FxHashSet::default();
            for arc in &t.inputs {
                place_set.insert(arc.place.0);
            }
            for arc in &t.outputs {
                place_set.insert(arc.place.0);
            }
            let weight: u64 = t.inputs.iter().map(|a| a.weight).sum::<u64>()
                + t.outputs.iter().map(|a| a.weight).sum::<u64>();
            Hyperedge {
                places: place_set.into_iter().collect(),
                weight,
            }
        })
        .collect()
}

/// Build adjacency list: for each place, which other places share a transition?
/// Returns (neighbor place index, edge weight) pairs.
fn build_adjacency(net: &PetriNet) -> Vec<Vec<(u32, u64)>> {
    let np = net.num_places();
    let mut adj: Vec<Vec<(u32, u64)>> = vec![Vec::new(); np];
    let hyperedges = build_hypergraph(net);

    for edge in &hyperedges {
        for &p1 in &edge.places {
            for &p2 in &edge.places {
                if p1 != p2 {
                    adj[p1 as usize].push((p2, edge.weight));
                }
            }
        }
    }

    // Deduplicate and merge weights for same neighbor pairs
    for neighbors in &mut adj {
        neighbors.sort_by_key(|&(p, _)| p);
        let mut merged: Vec<(u32, u64)> = Vec::new();
        for &(p, w) in neighbors.iter() {
            if let Some(last) = merged.last_mut() {
                if last.0 == p {
                    last.1 += w;
                    continue;
                }
            }
            merged.push((p, w));
        }
        *neighbors = merged;
    }

    adj
}

/// BFS-seeded balanced partition: grow from a seed place, assigning
/// visited places to partition A until half the places are assigned,
/// then the rest go to partition B.
///
/// Returns a boolean vector: `true` = partition A, `false` = partition B.
fn bfs_partition(adj: &[Vec<(u32, u64)>], seed: u32, active_places: &[u32]) -> Vec<bool> {
    let np = adj.len();
    let mut partition = vec![false; np];

    // Build set of active places for quick lookup
    let active_set: FxHashSet<u32> = active_places.iter().copied().collect();
    let half = active_places.len() / 2;

    let mut visited = FxHashSet::default();
    let mut queue = VecDeque::new();
    queue.push_back(seed);
    visited.insert(seed);

    let mut count = 0;
    while let Some(p) = queue.pop_front() {
        if count >= half {
            break;
        }
        if active_set.contains(&p) {
            partition[p as usize] = true;
            count += 1;
        }

        // Sort neighbors by weight (prefer cutting lighter edges)
        let mut neighbors: Vec<(u32, u64)> = adj[p as usize]
            .iter()
            .filter(|(n, _)| active_set.contains(n) && !visited.contains(n))
            .copied()
            .collect();
        neighbors.sort_by_key(|&(_, w)| w);

        for (n, _) in neighbors {
            if !visited.contains(&n) {
                visited.insert(n);
                queue.push_back(n);
            }
        }
    }

    partition
}

/// Find the best seed for partitioning: the place with the fewest
/// connections (peripheral node), which tends to produce more balanced cuts.
fn find_seed(adj: &[Vec<(u32, u64)>], active_places: &[u32]) -> u32 {
    let active_set: FxHashSet<u32> = active_places.iter().copied().collect();
    *active_places
        .iter()
        .min_by_key(|&&p| {
            adj[p as usize]
                .iter()
                .filter(|(n, _)| active_set.contains(n))
                .count()
        })
        .expect("invariant: active_places is non-empty")
}

/// Recursively partition places via balanced min-cut.
///
/// Stops recursion when:
/// - Component has fewer than `min_component_size` places
/// - Normalized cut exceeds THETA (too tightly coupled)
fn recursive_partition(
    adj: &[Vec<(u32, u64)>],
    hyperedges: &[Hyperedge],
    active_places: &[u32],
    min_component_size: usize,
) -> Vec<Vec<u32>> {
    if active_places.len() <= min_component_size {
        return vec![active_places.to_vec()];
    }

    let seed = find_seed(adj, active_places);
    let partition = bfs_partition(adj, seed, active_places);

    // Compute normalized cut: cut_weight / total_weight_of_active_edges
    let active_set: FxHashSet<u32> = active_places.iter().copied().collect();
    let active_hyperedges: Vec<&Hyperedge> = hyperedges
        .iter()
        .filter(|e| e.places.iter().any(|p| active_set.contains(p)))
        .collect();

    let total_w: u64 = active_hyperedges.iter().map(|e| e.weight).sum();
    let cut_w: u64 = active_hyperedges
        .iter()
        .filter(|e| {
            if e.places.len() < 2 {
                return false;
            }
            let active_in_e: Vec<u32> =
                e.places.iter().copied().filter(|p| active_set.contains(p)).collect();
            if active_in_e.len() < 2 {
                return false;
            }
            let first_side = partition[active_in_e[0] as usize];
            active_in_e.iter().any(|&p| partition[p as usize] != first_side)
        })
        .map(|e| e.weight)
        .sum();

    let normalized_cut = if total_w > 0 {
        cut_w as f64 / total_w as f64
    } else {
        0.0
    };

    // Don't split if the cut is too expensive (tightly coupled)
    if normalized_cut > THETA {
        return vec![active_places.to_vec()];
    }

    let part_a: Vec<u32> = active_places
        .iter()
        .copied()
        .filter(|&p| partition[p as usize])
        .collect();
    let part_b: Vec<u32> = active_places
        .iter()
        .copied()
        .filter(|&p| !partition[p as usize])
        .collect();

    // If partitioning produced a trivially imbalanced split, stop
    if part_a.is_empty() || part_b.is_empty() {
        return vec![active_places.to_vec()];
    }

    let mut result = Vec::new();
    result.extend(recursive_partition(adj, hyperedges, &part_a, min_component_size));
    result.extend(recursive_partition(adj, hyperedges, &part_b, min_component_size));
    result
}

/// Assign transitions to components based on which component contains
/// the majority of their connected places.
fn assign_transitions(
    net: &PetriNet,
    components: &[Vec<u32>],
) -> Vec<Vec<TransitionIdx>> {
    // Build place -> component index map
    let mut place_to_comp: FxHashMap<u32, usize> = FxHashMap::default();
    for (comp_idx, places) in components.iter().enumerate() {
        for &p in places {
            place_to_comp.insert(p, comp_idx);
        }
    }

    let mut trans_assignments: Vec<Vec<TransitionIdx>> = vec![Vec::new(); components.len()];

    for (t_idx, transition) in net.transitions.iter().enumerate() {
        // Count how many places of this transition belong to each component
        let mut comp_counts: FxHashMap<usize, usize> = FxHashMap::default();
        for arc in transition.inputs.iter().chain(transition.outputs.iter()) {
            if let Some(&comp) = place_to_comp.get(&arc.place.0) {
                *comp_counts.entry(comp).or_insert(0) += 1;
            }
        }

        // Assign to the component with the most connected places
        if let Some((&best_comp, _)) = comp_counts.iter().max_by_key(|(_, &count)| count) {
            trans_assignments[best_comp].push(TransitionIdx(t_idx as u32));
        }
    }

    trans_assignments
}

/// Identify interface places: places that appear in transitions assigned
/// to a different component than the one the place belongs to.
fn find_interface_places(
    net: &PetriNet,
    component_places: &[u32],
    component_transitions: &[TransitionIdx],
    place_to_comp: &FxHashMap<u32, usize>,
    comp_idx: usize,
) -> Vec<PlaceIdx> {
    let comp_place_set: FxHashSet<u32> = component_places.iter().copied().collect();
    let mut interface = FxHashSet::default();

    // Places in this component that are touched by transitions in other components
    for (t_idx, transition) in net.transitions.iter().enumerate() {
        let t_id = TransitionIdx(t_idx as u32);
        let is_local = component_transitions.contains(&t_id);
        if is_local {
            // Check if this local transition touches places outside this component
            for arc in transition.inputs.iter().chain(transition.outputs.iter()) {
                if !comp_place_set.contains(&arc.place.0) {
                    // The external place is an interface place of its own component
                    // but we also mark our places that connect to external transitions
                }
            }
        } else {
            // External transition touching our places
            for arc in transition.inputs.iter().chain(transition.outputs.iter()) {
                if comp_place_set.contains(&arc.place.0) {
                    interface.insert(arc.place.0);
                }
            }
        }
    }

    // Also: places in this component that belong to hyperedges spanning
    // multiple components
    for transition in &net.transitions {
        let mut comps_in_transition = FxHashSet::default();
        for arc in transition.inputs.iter().chain(transition.outputs.iter()) {
            if let Some(&c) = place_to_comp.get(&arc.place.0) {
                comps_in_transition.insert(c);
            }
        }
        if comps_in_transition.len() > 1 && comps_in_transition.contains(&comp_idx) {
            for arc in transition.inputs.iter().chain(transition.outputs.iter()) {
                if comp_place_set.contains(&arc.place.0) {
                    interface.insert(arc.place.0);
                }
            }
        }
    }

    let mut result: Vec<PlaceIdx> = interface.into_iter().map(PlaceIdx).collect();
    result.sort_by_key(|p| p.0);
    result
}

/// Decompose a Petri net into loosely-coupled components.
///
/// Uses hypergraph min-cut partitioning to split the net's places into
/// groups with minimal inter-group coupling. Each component contains its
/// local transitions and identifies interface places shared with other
/// components.
///
/// Returns a single component containing the entire net if:
/// - The net has fewer than `2 * min_component_size` places
/// - The normalized cut cost exceeds THETA for every attempted split
///
/// # Arguments
///
/// * `net` - The Petri net to decompose
/// * `min_component_size` - Minimum places per component (don't split smaller)
#[must_use]
pub(crate) fn decompose(net: &PetriNet, min_component_size: usize) -> Vec<Component> {
    let np = net.num_places();

    // Trivially small nets: don't decompose
    if np < 2 * min_component_size || np < 4 {
        let all_places: Vec<PlaceIdx> = (0..np as u32).map(PlaceIdx).collect();
        let all_transitions: Vec<TransitionIdx> =
            (0..net.num_transitions() as u32).map(TransitionIdx).collect();
        return vec![Component {
            places: all_places,
            transitions: all_transitions,
            interface_places: Vec::new(),
        }];
    }

    let adj = build_adjacency(net);
    let hyperedges = build_hypergraph(net);
    let all_places: Vec<u32> = (0..np as u32).collect();

    let partitions = recursive_partition(&adj, &hyperedges, &all_places, min_component_size);

    // If we got only one partition, return the whole net as one component
    if partitions.len() <= 1 {
        let all_places: Vec<PlaceIdx> = (0..np as u32).map(PlaceIdx).collect();
        let all_transitions: Vec<TransitionIdx> =
            (0..net.num_transitions() as u32).map(TransitionIdx).collect();
        return vec![Component {
            places: all_places,
            transitions: all_transitions,
            interface_places: Vec::new(),
        }];
    }

    let trans_assignments = assign_transitions(net, &partitions);

    // Build place -> component map
    let mut place_to_comp: FxHashMap<u32, usize> = FxHashMap::default();
    for (comp_idx, places) in partitions.iter().enumerate() {
        for &p in places {
            place_to_comp.insert(p, comp_idx);
        }
    }

    partitions
        .iter()
        .enumerate()
        .map(|(comp_idx, places)| {
            let interface = find_interface_places(
                net,
                places,
                &trans_assignments[comp_idx],
                &place_to_comp,
                comp_idx,
            );
            Component {
                places: {
                    let mut ps: Vec<PlaceIdx> = places.iter().map(|&p| PlaceIdx(p)).collect();
                    ps.sort_by_key(|p| p.0);
                    ps
                },
                transitions: {
                    let mut ts = trans_assignments[comp_idx].clone();
                    ts.sort_by_key(|t| t.0);
                    ts
                },
                interface_places: interface,
            }
        })
        .collect()
}

/// Estimate the state space size for a component based on place bounds.
///
/// For each place with a known bound B, the number of possible values is
/// B+1 (0 through B). The estimated state space is the product of all
/// such values. Returns `None` if any place is unbounded.
fn estimate_state_space(bounds: &[Option<u64>], places: &[PlaceIdx]) -> Option<u64> {
    let mut product: u64 = 1;
    for p in places {
        let bound = bounds[p.0 as usize]?;
        // Saturating multiply to avoid overflow on huge state spaces
        product = product.saturating_mul(bound + 1);
        if product > u64::MAX / 2 {
            return Some(u64::MAX); // overflow sentinel
        }
    }
    Some(product)
}

/// Route each component to the recommended verification technique.
///
/// Routing rules:
/// 1. All places bounded and total latches <= 500 -> AIGER
/// 2. Some places unbounded -> CHC/PDR
/// 3. Small state space (estimated < 1M states) -> BFS
///
/// The AIGER threshold of 500 latches matches `encode_aiger::MAX_TOTAL_LATCHES`.
#[must_use]
pub(crate) fn route_techniques(
    net: &PetriNet,
    components: &[Component],
) -> Vec<(Component, RecommendedTechnique)> {
    let bounds = structural_place_bounds(net);

    components
        .iter()
        .map(|comp| {
            let technique = route_single_component(&bounds, comp);
            (comp.clone(), technique)
        })
        .collect()
}

/// Route a single component to a verification technique.
fn route_single_component(
    bounds: &[Option<u64>],
    comp: &Component,
) -> RecommendedTechnique {
    // Check if all places are bounded
    let all_bounded = comp
        .places
        .iter()
        .all(|p| bounds[p.0 as usize].is_some());

    if !all_bounded {
        return RecommendedTechnique::ChcPdr;
    }

    // Estimate state space for BFS check
    if let Some(estimated_states) = estimate_state_space(bounds, &comp.places) {
        if estimated_states < 1_000_000 {
            return RecommendedTechnique::Bfs;
        }
    }

    // Check total latch count for AIGER
    let total_latches: u32 = comp
        .places
        .iter()
        .filter_map(|p| {
            bounds[p.0 as usize].map(|b| {
                // ceil(log2(b+1)) bits needed to encode values 0..=b
                if b == 0 {
                    1 // at least 1 latch even for constant-0 place
                } else {
                    (u64::BITS - b.leading_zeros()) as u32
                }
            })
        })
        .sum();

    if total_latches <= 500 {
        RecommendedTechnique::Aiger
    } else {
        // Bounded but too many latches for AIGER — fall back to CHC/PDR
        RecommendedTechnique::ChcPdr
    }
}

#[cfg(test)]
#[path = "decomposition_tests.rs"]
mod tests;
