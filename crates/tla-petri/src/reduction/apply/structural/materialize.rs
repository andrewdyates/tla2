// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::{BTreeMap, BTreeSet};

use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionIdx, TransitionInfo};

use super::super::super::ReducedNet;
use super::planning::StructuralPlan;

/// Remap arcs through `place_map`, combining weights for duplicate places.
///
/// Arcs to removed places (where `place_map` is `None`) are dropped.
/// When multiple arcs reference the same surviving place, their weights
/// are summed. This handles the merge step of agglomeration correctly.
fn remap_and_combine_arcs(arcs: &[Arc], place_map: &[Option<PlaceIdx>]) -> Vec<Arc> {
    let mut combined: BTreeMap<u32, u64> = BTreeMap::new();
    for arc in arcs {
        if let Some(new_p) = place_map[arc.place.0 as usize] {
            *combined.entry(new_p.0).or_default() += arc.weight;
        }
    }
    combined
        .into_iter()
        .map(|(p, w)| Arc {
            place: PlaceIdx(p),
            weight: w,
        })
        .collect()
}

/// Subtract `weight_to_strip` from arcs on `place`, preserving any unmatched
/// residual weight on the same place.
fn strip_arc_weight(arcs: &mut Vec<Arc>, place: PlaceIdx, mut weight_to_strip: u64) {
    if weight_to_strip == 0 {
        return;
    }

    for arc in arcs.iter_mut().filter(|arc| arc.place == place) {
        if weight_to_strip == 0 {
            break;
        }
        let stripped = arc.weight.min(weight_to_strip);
        arc.weight -= stripped;
        weight_to_strip -= stripped;
    }

    arcs.retain(|arc| arc.weight > 0);
    debug_assert_eq!(
        weight_to_strip, 0,
        "Rule K strip weight must be fully accounted for by original transition arcs"
    );
}

/// Turn a [`StructuralPlan`] into a [`ReducedNet`] by building place/transition
/// mappings, splicing agglomeration arcs, and stripping self-loop weights.
pub(super) fn build_reduced_net(net: &PetriNet, plan: StructuralPlan) -> ReducedNet {
    let StructuralPlan {
        report,
        place_removed,
        place_agglomerated,
        redundant_set,
        reconstructions,
    } = plan;

    let num_places = net.num_places();
    let num_transitions = net.num_transitions();

    // Build place mappings.
    let mut place_map: Vec<Option<PlaceIdx>> = vec![None; num_places];
    let mut place_unmap: Vec<PlaceIdx> = Vec::new();
    let mut new_pidx = 0u32;
    for (orig, &removed) in place_removed.iter().enumerate() {
        if !removed {
            place_map[orig] = Some(PlaceIdx(new_pidx));
            place_unmap.push(PlaceIdx(orig as u32));
            new_pidx += 1;
        }
    }
    for merge in &report.parallel_places {
        if let Some(canonical) = place_map[merge.canonical.0 as usize] {
            place_map[merge.duplicate.0 as usize] = Some(canonical);
        }
    }

    // Build set of transitions to remove.
    let mut trans_removed = vec![false; num_transitions];
    for &TransitionIdx(t) in &report.dead_transitions {
        trans_removed[t as usize] = true;
    }
    for agg in &report.pre_agglomerations {
        trans_removed[agg.transition.0 as usize] = true;
    }
    for agg in &report.post_agglomerations {
        trans_removed[agg.transition.0 as usize] = true;
    }
    for class in &report.duplicate_transitions {
        for duplicate in &class.duplicates {
            trans_removed[duplicate.0 as usize] = true;
        }
    }
    for &TransitionIdx(t) in &report.self_loop_transitions {
        trans_removed[t as usize] = true;
    }
    for &TransitionIdx(t) in &report.dominated_transitions {
        trans_removed[t as usize] = true;
    }
    // Transitions blocked by a constant/isolated place with insufficient tokens.
    for (tidx, t) in net.transitions.iter().enumerate() {
        if trans_removed[tidx] {
            continue;
        }
        let blocked_by_constant = t.inputs.iter().any(|arc| {
            let p = arc.place.0 as usize;
            place_removed[p]
                && !place_agglomerated[p]
                && !redundant_set[p]
                && net.initial_marking[p] < arc.weight
        });
        if blocked_by_constant {
            trans_removed[tidx] = true;
        }
    }

    // Build extra arcs from agglomerations.
    let mut extra_inputs: Vec<Vec<Arc>> = vec![Vec::new(); num_transitions];
    let mut extra_outputs: Vec<Vec<Arc>> = vec![Vec::new(); num_transitions];

    for agg in &report.pre_agglomerations {
        let source = &net.transitions[agg.transition.0 as usize];
        for &succ in &agg.successors {
            extra_inputs[succ.0 as usize].extend(source.inputs.iter().cloned());
        }
    }
    for agg in &report.post_agglomerations {
        let sink = &net.transitions[agg.transition.0 as usize];
        for &pred in &agg.predecessors {
            extra_outputs[pred.0 as usize].extend(sink.outputs.iter().cloned());
        }
    }

    // Build transition mappings.
    let mut transition_map: Vec<Option<TransitionIdx>> = vec![None; num_transitions];
    let mut transition_unmap: Vec<TransitionIdx> = Vec::new();
    let mut new_tidx = 0u32;
    for (orig, &removed) in trans_removed.iter().enumerate() {
        if !removed {
            transition_map[orig] = Some(TransitionIdx(new_tidx));
            transition_unmap.push(TransitionIdx(orig as u32));
            new_tidx += 1;
        }
    }
    for class in &report.duplicate_transitions {
        let Some(canonical) = transition_map[class.canonical.0 as usize] else {
            continue;
        };
        for duplicate in &class.duplicates {
            transition_map[duplicate.0 as usize] = Some(canonical);
        }
    }

    // Build reduced net.
    let new_places: Vec<PlaceInfo> = place_unmap
        .iter()
        .map(|&PlaceIdx(orig)| net.places[orig as usize].clone())
        .collect();

    let new_initial: Vec<u64> = place_unmap
        .iter()
        .map(|&PlaceIdx(orig)| net.initial_marking[orig as usize])
        .collect();

    // Build exact self-loop strip weights from the original transition arcs (Rule K).
    let mut self_loop_strip_weights: BTreeMap<(u32, u32), u64> = BTreeMap::new();
    for self_loop_arc in &report.self_loop_arcs {
        *self_loop_strip_weights
            .entry((self_loop_arc.transition.0, self_loop_arc.place.0))
            .or_default() += self_loop_arc.weight;
    }
    let self_loop_places: BTreeSet<(u32, u32)> = report
        .self_loop_arcs
        .iter()
        .map(|self_loop_arc| (self_loop_arc.transition.0, self_loop_arc.place.0))
        .collect();
    let new_transitions: Vec<TransitionInfo> = transition_unmap
        .iter()
        .map(|&TransitionIdx(orig)| {
            let t = &net.transitions[orig as usize];
            let orig_idx = orig as usize;

            let mut all_inputs: Vec<Arc> = t.inputs.clone();
            if !self_loop_places.is_empty() {
                for &(transition, place) in self_loop_places
                    .iter()
                    .filter(|(transition, _)| *transition == orig)
                {
                    let weight = self_loop_strip_weights[&(transition, place)];
                    strip_arc_weight(&mut all_inputs, PlaceIdx(place), weight);
                }
            }
            all_inputs.extend_from_slice(&extra_inputs[orig_idx]);
            let new_inputs = remap_and_combine_arcs(&all_inputs, &place_map);

            let mut all_outputs: Vec<Arc> = t.outputs.clone();
            if !self_loop_places.is_empty() {
                for &(transition, place) in self_loop_places
                    .iter()
                    .filter(|(transition, _)| *transition == orig)
                {
                    let weight = self_loop_strip_weights[&(transition, place)];
                    strip_arc_weight(&mut all_outputs, PlaceIdx(place), weight);
                }
            }
            all_outputs.extend_from_slice(&extra_outputs[orig_idx]);
            let new_outputs = remap_and_combine_arcs(&all_outputs, &place_map);

            TransitionInfo {
                id: t.id.clone(),
                name: t.name.clone(),
                inputs: new_inputs,
                outputs: new_outputs,
            }
        })
        .collect();

    // Record expansion values for non-redundant removed places.
    let constant_values: Vec<(PlaceIdx, u64)> = place_removed
        .iter()
        .enumerate()
        .filter(|(p, &removed)| removed && place_map[*p].is_none() && !redundant_set[*p])
        .map(|(p, _)| (PlaceIdx(p as u32), net.initial_marking[p]))
        .collect();

    let reduced_net = PetriNet {
        name: net.name.clone(),
        places: new_places,
        transitions: new_transitions,
        initial_marking: new_initial,
    };

    ReducedNet {
        net: reduced_net,
        place_map,
        place_unmap,
        place_scales: vec![1; num_places],
        transition_map,
        transition_unmap,
        constant_values,
        reconstructions,
        report,
    }
}
