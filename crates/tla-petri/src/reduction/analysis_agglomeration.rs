// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::petri_net::{PetriNet, TransitionIdx};

use super::model::{PostAgglomeration, PreAgglomeration};

/// Per-place connectivity: which transitions produce into / consume from each place.
pub(super) struct PlaceConnectivity {
    /// For each place: transitions that produce tokens into it (place's pre-set).
    pub(super) producers: Vec<Vec<(TransitionIdx, u64)>>,
    /// For each place: transitions that consume tokens from it (place's post-set).
    pub(super) consumers: Vec<Vec<(TransitionIdx, u64)>>,
}

/// Build per-place connectivity, ignoring dead transitions.
pub(super) fn build_place_connectivity(
    net: &PetriNet,
    dead_transitions: &[TransitionIdx],
) -> PlaceConnectivity {
    let num_places = net.num_places();
    let num_transitions = net.num_transitions();

    let mut is_dead = vec![false; num_transitions];
    for &TransitionIdx(t) in dead_transitions {
        is_dead[t as usize] = true;
    }

    let mut producers = vec![Vec::new(); num_places];
    let mut consumers = vec![Vec::new(); num_places];

    for (tidx, t) in net.transitions.iter().enumerate() {
        if is_dead[tidx] {
            continue;
        }
        let t_idx = TransitionIdx(tidx as u32);
        for arc in &t.outputs {
            producers[arc.place.0 as usize].push((t_idx, arc.weight));
        }
        for arc in &t.inputs {
            consumers[arc.place.0 as usize].push((t_idx, arc.weight));
        }
    }

    PlaceConnectivity {
        producers,
        consumers,
    }
}

/// Find all agglomeration candidates and resolve conflicts.
///
/// Wraps the 3-step sequence: build connectivity, find pre/post candidates,
/// then resolve conflicts (pre-agglomerations get priority).
pub(super) fn find_agglomerations(
    net: &PetriNet,
    dead_transitions: &[TransitionIdx],
) -> (Vec<PreAgglomeration>, Vec<PostAgglomeration>) {
    let connectivity = build_place_connectivity(net, dead_transitions);
    let pre_candidates = find_pre_agglomerations(net, dead_transitions, &connectivity);
    let post_candidates = find_post_agglomerations(net, dead_transitions, &connectivity);
    resolve_agglomeration_conflicts(pre_candidates, post_candidates)
}

/// Find pre-agglomeration candidates (Berthelot 1987).
///
/// A transition `t` is pre-agglomeratable when:
/// 1. `t` has exactly one output place `p` with arc weight 1
/// 2. `p` has exactly one producer (which is `t`)
/// 3. `p` has zero initial tokens
/// 4. Every consumer of `p` reads exactly one token
/// 5. `t` is not in its own successor set (no self-loop through `p`)
/// 6. Source inputs ∩ successor outputs = ∅ (Berthelot condition 6:
///    prevents creating false self-loops when merged)
fn find_pre_agglomerations(
    net: &PetriNet,
    dead_transitions: &[TransitionIdx],
    conn: &PlaceConnectivity,
) -> Vec<PreAgglomeration> {
    use std::collections::HashSet;

    let num_transitions = net.num_transitions();
    let mut is_dead = vec![false; num_transitions];
    for &TransitionIdx(t) in dead_transitions {
        is_dead[t as usize] = true;
    }

    let mut results = Vec::new();

    for (tidx, t) in net.transitions.iter().enumerate() {
        if is_dead[tidx] {
            continue;
        }
        // Condition 1: exactly one output place, weight 1.
        if t.outputs.len() != 1 || t.outputs[0].weight != 1 {
            continue;
        }
        let p = t.outputs[0].place;
        let p_idx = p.0 as usize;

        // Condition 2: p has exactly one producer.
        if conn.producers[p_idx].len() != 1 {
            continue;
        }

        // Condition 3: zero initial tokens.
        if net.initial_marking[p_idx] != 0 {
            continue;
        }

        // Condition 4: every consumer reads exactly 1 token.
        if conn.consumers[p_idx].iter().any(|&(_, w)| w != 1) {
            continue;
        }

        let successors: Vec<TransitionIdx> = conn.consumers[p_idx]
            .iter()
            .map(|&(t_idx, _)| t_idx)
            .collect();

        if successors.is_empty() {
            continue;
        }

        // Condition 5: no self-loop through p.
        let t_idx = TransitionIdx(tidx as u32);
        if successors.contains(&t_idx) {
            continue;
        }

        // Condition 6 (Berthelot): source inputs must not overlap with
        // any successor's outputs. Prevents creating self-loops that
        // hide intermediate markings (e.g., mutex cycle).
        let source_inputs: HashSet<u32> = t.inputs.iter().map(|a| a.place.0).collect();
        let overlap = successors.iter().any(|&TransitionIdx(si)| {
            let succ = &net.transitions[si as usize];
            succ.outputs
                .iter()
                .any(|a| source_inputs.contains(&a.place.0))
        });
        if overlap {
            continue;
        }

        results.push(PreAgglomeration {
            transition: t_idx,
            place: p,
            successors,
        });
    }

    results
}

/// Find post-agglomeration candidates (dual of pre-agglomeration).
///
/// A transition `t` is post-agglomeratable when:
/// 1. `t` has exactly one input place `p` with arc weight 1
/// 2. `p` has exactly one consumer (which is `t`)
/// 3. `p` has zero initial tokens
/// 4. Every producer of `p` produces exactly one token
/// 5. `t` is not in its own predecessor set (no self-loop through `p`)
/// 6. Sink outputs ∩ predecessor inputs = ∅ (dual of Berthelot condition 6)
fn find_post_agglomerations(
    net: &PetriNet,
    dead_transitions: &[TransitionIdx],
    conn: &PlaceConnectivity,
) -> Vec<PostAgglomeration> {
    use std::collections::HashSet;

    let num_transitions = net.num_transitions();
    let mut is_dead = vec![false; num_transitions];
    for &TransitionIdx(t) in dead_transitions {
        is_dead[t as usize] = true;
    }

    let mut results = Vec::new();

    for (tidx, t) in net.transitions.iter().enumerate() {
        if is_dead[tidx] {
            continue;
        }
        // Condition 1: exactly one input place, weight 1.
        if t.inputs.len() != 1 || t.inputs[0].weight != 1 {
            continue;
        }
        let p = t.inputs[0].place;
        let p_idx = p.0 as usize;

        // Condition 2: p has exactly one consumer.
        if conn.consumers[p_idx].len() != 1 {
            continue;
        }

        // Condition 3: zero initial tokens.
        if net.initial_marking[p_idx] != 0 {
            continue;
        }

        // Condition 4: every producer produces exactly 1 token.
        if conn.producers[p_idx].iter().any(|&(_, w)| w != 1) {
            continue;
        }

        let predecessors: Vec<TransitionIdx> = conn.producers[p_idx]
            .iter()
            .map(|&(t_idx, _)| t_idx)
            .collect();

        if predecessors.is_empty() {
            continue;
        }

        // Condition 5: no self-loop through p.
        let t_idx = TransitionIdx(tidx as u32);
        if predecessors.contains(&t_idx) {
            continue;
        }

        // Condition 6 (Berthelot dual): sink outputs must not overlap
        // with any predecessor's inputs. Prevents false self-loops.
        let sink_outputs: HashSet<u32> = t.outputs.iter().map(|a| a.place.0).collect();
        let overlap = predecessors.iter().any(|&TransitionIdx(pi)| {
            let pred = &net.transitions[pi as usize];
            pred.inputs
                .iter()
                .any(|a| sink_outputs.contains(&a.place.0))
        });
        if overlap {
            continue;
        }

        results.push(PostAgglomeration {
            transition: t_idx,
            place: p,
            predecessors,
        });
    }

    results
}

/// Resolve conflicts between agglomeration candidates.
///
/// A transition cannot be both removed (as source/sink) and modified
/// (as successor/predecessor) in the same pass. A place can only appear
/// in one agglomeration. Pre-agglomerations get priority.
fn resolve_agglomeration_conflicts(
    pre: Vec<PreAgglomeration>,
    post: Vec<PostAgglomeration>,
) -> (Vec<PreAgglomeration>, Vec<PostAgglomeration>) {
    use std::collections::HashSet;

    let mut used_places: HashSet<u32> = HashSet::new();
    let mut removed_transitions: HashSet<u32> = HashSet::new();
    // Transitions that receive extra arcs from agglomeration and must NOT
    // be removed by a subsequent agglomeration in the same pass. Without
    // this guard, chained pre-agglomerations (e.g., r0→r1→r2→r3) lose
    // intermediate arcs: the successor of the first agglomeration becomes
    // the source of the second, so its extra inputs are never applied.
    let mut receiving_transitions: HashSet<u32> = HashSet::new();

    let mut selected_pre = Vec::new();
    for agg in pre {
        if used_places.contains(&agg.place.0) {
            continue;
        }
        if removed_transitions.contains(&agg.transition.0) {
            continue;
        }
        // Source must not be a receiving transition from a prior agglomeration.
        if receiving_transitions.contains(&agg.transition.0) {
            continue;
        }
        if agg
            .successors
            .iter()
            .any(|s| removed_transitions.contains(&s.0))
        {
            continue;
        }

        used_places.insert(agg.place.0);
        removed_transitions.insert(agg.transition.0);
        for s in &agg.successors {
            receiving_transitions.insert(s.0);
        }
        selected_pre.push(agg);
    }

    let mut selected_post = Vec::new();
    for agg in post {
        if used_places.contains(&agg.place.0) {
            continue;
        }
        if removed_transitions.contains(&agg.transition.0) {
            continue;
        }
        // Sink must not be a receiving transition from a prior agglomeration.
        if receiving_transitions.contains(&agg.transition.0) {
            continue;
        }
        if agg
            .predecessors
            .iter()
            .any(|p| removed_transitions.contains(&p.0))
        {
            continue;
        }

        used_places.insert(agg.place.0);
        removed_transitions.insert(agg.transition.0);
        for p in &agg.predecessors {
            receiving_transitions.insert(p.0);
        }
        selected_post.push(agg);
    }

    (selected_pre, selected_post)
}
