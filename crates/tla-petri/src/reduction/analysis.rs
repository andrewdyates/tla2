// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};

use super::model::ReductionReport;

// Re-export from sibling modules so external callers don't need to know the split.
pub(super) use super::analysis_agglomeration::{build_place_connectivity, find_agglomerations};
pub(crate) use super::analysis_invariant::{
    find_never_disabling_arcs, find_non_decreasing_places, find_parallel_places,
    find_token_eliminated_places,
};
pub(super) use super::analysis_transitions::{
    find_dominated_transitions, find_duplicate_transitions, find_self_loop_arcs,
    find_self_loop_transitions,
};

/// Analyze a Petri net and report which structures can be reduced.
///
/// Uses iterative fixpoint analysis for dead transitions: removing a dead
/// transition can make other transitions dead (by removing the only producer
/// for their input places). Places that become isolated after dead transition
/// removal are also detected and reported.
#[must_use]
pub(crate) fn analyze(net: &PetriNet) -> ReductionReport {
    let constant = find_constant_places(net);
    let dead = find_dead_transitions(net);
    let duplicate_transitions = find_duplicate_transitions(net, &dead);
    let self_loop_transitions = find_self_loop_transitions(net, &dead);
    let non_decreasing_places = find_non_decreasing_places(net, &dead, &[], &[]);
    let parallel_places = find_parallel_places(net, &dead, &[]);
    let mut isolated = find_isolated_places(net);

    // Places that become isolated after dead transition removal.
    let cascade_isolated = find_cascade_isolated_places(net, &dead);
    isolated.extend(cascade_isolated);

    // Agglomeration detection (connectivity + candidates + conflict resolution).
    let (pre_agg, post_agg) = find_agglomerations(net, &dead);

    let dominated = find_dominated_transitions(net, &dead);

    ReductionReport {
        constant_places: constant,
        source_places: Vec::new(),
        dead_transitions: dead,
        isolated_places: isolated,
        pre_agglomerations: pre_agg,
        post_agglomerations: post_agg,
        duplicate_transitions,
        self_loop_transitions,
        dominated_transitions: dominated,
        self_loop_arcs: Vec::new(),
        never_disabling_arcs: Vec::new(),
        token_eliminated_places: Vec::new(),
        redundant_places: Vec::new(),
        parallel_places,
        non_decreasing_places,
    }
}

/// Find producer-only places that are safe to elide because no live transition
/// ever consumes from them and they are not query-protected.
pub(crate) fn find_source_places(
    net: &PetriNet,
    dead_transitions: &[TransitionIdx],
    protected_places: &[bool],
) -> Vec<PlaceIdx> {
    let connectivity = build_place_connectivity(net, dead_transitions);
    let mut source_places = Vec::new();

    for place_idx in 0..net.num_places() {
        if protected_places.get(place_idx).copied().unwrap_or(false) {
            continue;
        }
        if !connectivity.consumers[place_idx].is_empty() {
            continue;
        }
        if connectivity.producers[place_idx].is_empty() {
            continue;
        }
        source_places.push(PlaceIdx(place_idx as u32));
    }

    source_places
}

/// A place is constant if every transition has zero net effect on it.
///
/// For each transition, we compute `sum(output_arcs_to_p) - sum(input_arcs_from_p)`.
/// If this delta is zero for ALL transitions, the place's token count can never change.
fn find_constant_places(net: &PetriNet) -> Vec<PlaceIdx> {
    let num_places = net.num_places();
    // Track whether each place has ever been affected with a nonzero delta.
    let mut is_constant = vec![true; num_places];
    // Also track whether the place is connected to any transition at all.
    let mut is_connected = vec![false; num_places];
    // Reusable delta buffer — avoids O(P) allocation per transition.
    let mut delta = vec![0i64; num_places];
    // Track which places were touched so we can reset only those entries.
    let mut touched = Vec::with_capacity(16);

    for t in &net.transitions {
        touched.clear();
        for arc in &t.inputs {
            let p = arc.place.0 as usize;
            delta[p] -= arc.weight as i64;
            is_connected[p] = true;
            touched.push(p);
        }
        for arc in &t.outputs {
            let p = arc.place.0 as usize;
            delta[p] += arc.weight as i64;
            is_connected[p] = true;
            touched.push(p);
        }
        for &p in &touched {
            if delta[p] != 0 {
                is_constant[p] = false;
            }
            delta[p] = 0;
        }
    }

    // Only report connected constant places. Isolated places are reported separately.
    is_constant
        .iter()
        .zip(is_connected.iter())
        .enumerate()
        .filter(|(_, (&c, &conn))| c && conn)
        .map(|(i, _)| PlaceIdx(i as u32))
        .collect()
}

/// Find all dead transitions via iterative fixpoint analysis.
///
/// A transition is dead if it can never fire from any reachable marking.
/// This uses cascading analysis: when a dead transition is removed, its
/// output places lose a producer. If a place then has no remaining producer
/// and insufficient initial marking, transitions consuming from it also
/// become dead. The analysis iterates until no new dead transitions are found.
///
/// Example cascade: `p0(0) → t0 → p1(0) → t1 → p2`. If p0 has no producer
/// and initial marking 0, t0 is dead. Removing t0 means p1 has no producer,
/// so t1 is also dead. Single-pass analysis would only catch t0.
fn find_dead_transitions(net: &PetriNet) -> Vec<TransitionIdx> {
    let num_places = net.num_places();
    let num_transitions = net.num_transitions();
    let mut is_dead = vec![false; num_transitions];

    loop {
        // Recompute producer status ignoring dead transitions.
        let mut has_producer = vec![false; num_places];
        for (tidx, t) in net.transitions.iter().enumerate() {
            if is_dead[tidx] {
                continue;
            }
            for arc in &t.outputs {
                has_producer[arc.place.0 as usize] = true;
            }
        }

        // Find newly dead transitions.
        let mut changed = false;
        for (tidx, t) in net.transitions.iter().enumerate() {
            if is_dead[tidx] {
                continue;
            }
            let dead = t.inputs.iter().any(|arc| {
                let p = arc.place.0 as usize;
                !has_producer[p] && net.initial_marking[p] < arc.weight
            });
            if dead {
                is_dead[tidx] = true;
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }

    is_dead
        .iter()
        .enumerate()
        .filter(|(_, &d)| d)
        .map(|(i, _)| TransitionIdx(i as u32))
        .collect()
}

/// Places with no incoming or outgoing arcs. These contribute nothing to
/// the reachable state space (their token count is always the initial value).
fn find_isolated_places(net: &PetriNet) -> Vec<PlaceIdx> {
    find_isolated_places_ignoring(net, &[])
}

/// Places with no arcs to any alive transition.
///
/// A place is "cascade-isolated" if all transitions it connects to are dead.
/// Unlike structurally isolated places (zero arcs), these places HAVE arcs
/// but only to dead transitions. Their token count is invariant because no
/// alive transition can consume from or produce into them.
fn find_cascade_isolated_places(
    net: &PetriNet,
    dead_transitions: &[TransitionIdx],
) -> Vec<PlaceIdx> {
    if dead_transitions.is_empty() {
        return Vec::new();
    }

    // Only return places that were NOT already structurally isolated
    // (those are reported separately to avoid double-counting).
    let structurally_isolated = find_isolated_places(net);
    find_isolated_places_ignoring(net, dead_transitions)
        .into_iter()
        .filter(|p| !structurally_isolated.contains(p))
        .collect()
}

/// Places with no arcs to any alive (non-ignored) transition.
fn find_isolated_places_ignoring(
    net: &PetriNet,
    ignored_transitions: &[TransitionIdx],
) -> Vec<PlaceIdx> {
    let num_places = net.num_places();
    let num_transitions = net.num_transitions();

    let mut is_ignored = vec![false; num_transitions];
    for &TransitionIdx(t) in ignored_transitions {
        is_ignored[t as usize] = true;
    }

    let mut connected = vec![false; num_places];
    for (tidx, t) in net.transitions.iter().enumerate() {
        if is_ignored[tidx] {
            continue;
        }
        for arc in &t.inputs {
            connected[arc.place.0 as usize] = true;
        }
        for arc in &t.outputs {
            connected[arc.place.0 as usize] = true;
        }
    }

    connected
        .iter()
        .enumerate()
        .filter(|(_, &c)| !c)
        .map(|(i, _)| PlaceIdx(i as u32))
        .collect()
}
