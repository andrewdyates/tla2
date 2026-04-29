// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::petri_net::{Arc, PetriNet, PlaceIdx, TransitionIdx, TransitionInfo};
use crate::query_slice::QuerySlice;

/// A single contraction step in circulation loop reduction.
///
/// The connecting transition is removed, and `drop_place` is merged into
/// `keep_place` by redirecting all arcs and combining initial markings.
#[derive(Debug, Clone)]
struct CirculationLoopMerge {
    remove_transition: usize,
    keep_place: usize,
    drop_place: usize,
}

/// Reduce query-local circulation loops to fixpoint.
///
/// Repeatedly finds and contracts one circulation loop merge per pass until
/// no more contractions are possible. Returns `None` if no contraction was
/// performed on the first pass.
///
/// `protected_places` is indexed by the **reduced-net** place indices (the
/// coordinate system of `slice.place_unmap` origins). A local place `p` in
/// the slice is protected if `protected_places[slice.place_unmap[p].0]` is true.
pub(crate) fn reduce_query_local_circulation_loops_fixpoint(
    mut slice: QuerySlice,
    protected_places: &[bool],
) -> Option<QuerySlice> {
    let mut any_changed = false;
    while let Some(contracted) = reduce_query_local_circulation_loops_once(&slice, protected_places)
    {
        slice = contracted;
        any_changed = true;
    }
    if any_changed {
        Some(slice)
    } else {
        None
    }
}

/// Attempt one circulation loop contraction on the slice's local net.
fn reduce_query_local_circulation_loops_once(
    slice: &QuerySlice,
    protected_places: &[bool],
) -> Option<QuerySlice> {
    let net = &slice.net;
    let np = net.num_places();
    let nt = net.num_transitions();

    let local_protected: Vec<bool> = (0..np)
        .map(|local_p| {
            let orig_p = slice.place_unmap[local_p].0 as usize;
            orig_p < protected_places.len() && protected_places[orig_p]
        })
        .collect();

    let candidates: Vec<(usize, usize, usize)> = (0..nt)
        .filter_map(|t| {
            let trans = &net.transitions[t];
            if trans.inputs.len() != 1 || trans.outputs.len() != 1 {
                return None;
            }
            if trans.inputs[0].weight != 1 || trans.outputs[0].weight != 1 {
                return None;
            }
            let in_p = trans.inputs[0].place.0 as usize;
            let out_p = trans.outputs[0].place.0 as usize;
            if in_p == out_p {
                return None;
            }
            Some((t, in_p, out_p))
        })
        .collect();

    if candidates.is_empty() {
        return None;
    }

    let mut place_to_consumer_candidates: Vec<Vec<usize>> = vec![vec![]; np];
    for (i, &(_, in_p, _)) in candidates.iter().enumerate() {
        place_to_consumer_candidates[in_p].push(i);
    }

    let merge = find_circulation_loop_merge(
        &candidates,
        &place_to_consumer_candidates,
        &local_protected,
        net,
    )?;
    apply_circulation_merge(slice, &merge)
}

fn find_circulation_loop_merge(
    candidates: &[(usize, usize, usize)],
    place_to_consumer_candidates: &[Vec<usize>],
    local_protected: &[bool],
    net: &PetriNet,
) -> Option<CirculationLoopMerge> {
    let nc = candidates.len();
    let mut visited = vec![false; nc];
    let mut on_stack = vec![false; nc];
    let mut stack_path: Vec<usize> = Vec::new();

    for start in 0..nc {
        if visited[start] {
            continue;
        }
        if let Some(merge) = dfs_find_loop(
            start,
            candidates,
            place_to_consumer_candidates,
            local_protected,
            net,
            &mut visited,
            &mut on_stack,
            &mut stack_path,
        ) {
            return Some(merge);
        }
    }
    None
}

fn dfs_find_loop(
    node: usize,
    candidates: &[(usize, usize, usize)],
    place_to_consumer_candidates: &[Vec<usize>],
    local_protected: &[bool],
    net: &PetriNet,
    visited: &mut [bool],
    on_stack: &mut [bool],
    stack_path: &mut Vec<usize>,
) -> Option<CirculationLoopMerge> {
    visited[node] = true;
    on_stack[node] = true;
    stack_path.push(node);

    let (_, _, out_p) = candidates[node];
    for &next in &place_to_consumer_candidates[out_p] {
        if !visited[next] {
            if let Some(merge) = dfs_find_loop(
                next,
                candidates,
                place_to_consumer_candidates,
                local_protected,
                net,
                visited,
                on_stack,
                stack_path,
            ) {
                stack_path.pop();
                on_stack[node] = false;
                return Some(merge);
            }
        } else if on_stack[next] {
            let cycle_start = stack_path.iter().position(|&n| n == next).unwrap();
            let cycle = &stack_path[cycle_start..];

            if let Some(merge) = find_merge_in_cycle(cycle, candidates, local_protected, net) {
                stack_path.pop();
                on_stack[node] = false;
                return Some(merge);
            }
        }
    }

    stack_path.pop();
    on_stack[node] = false;
    None
}

fn find_merge_in_cycle(
    cycle: &[usize],
    candidates: &[(usize, usize, usize)],
    local_protected: &[bool],
    net: &PetriNet,
) -> Option<CirculationLoopMerge> {
    for &cand_idx in cycle {
        let (trans_idx, keep_p, drop_p) = candidates[cand_idx];

        if local_protected[keep_p] || local_protected[drop_p] {
            continue;
        }

        if !neighborhood_all_unprotected(net, keep_p, local_protected)
            || !neighborhood_all_unprotected(net, drop_p, local_protected)
        {
            continue;
        }

        return Some(CirculationLoopMerge {
            remove_transition: trans_idx,
            keep_place: keep_p,
            drop_place: drop_p,
        });
    }
    None
}

fn neighborhood_all_unprotected(net: &PetriNet, place: usize, local_protected: &[bool]) -> bool {
    let place_idx = PlaceIdx(place as u32);
    for trans in &net.transitions {
        let touches = trans
            .inputs
            .iter()
            .chain(trans.outputs.iter())
            .any(|arc| arc.place == place_idx);
        if !touches {
            continue;
        }
        for arc in trans.inputs.iter().chain(trans.outputs.iter()) {
            let p = arc.place.0 as usize;
            if local_protected[p] {
                return false;
            }
        }
    }
    true
}

fn apply_circulation_merge(slice: &QuerySlice, merge: &CirculationLoopMerge) -> Option<QuerySlice> {
    let old_net = &slice.net;
    let np = old_net.num_places();
    let nt = old_net.num_transitions();

    let mut new_place_map: Vec<Option<usize>> = vec![None; np];
    let mut new_idx = 0usize;
    for p in 0..np {
        if p == merge.drop_place {
            continue;
        }
        new_place_map[p] = Some(new_idx);
        new_idx += 1;
    }
    let new_np = new_idx;
    new_place_map[merge.drop_place] = new_place_map[merge.keep_place];

    let mut new_places = Vec::with_capacity(new_np);
    let mut new_initial_marking = Vec::with_capacity(new_np);
    for p in 0..np {
        if p == merge.drop_place {
            continue;
        }
        new_places.push(old_net.places[p].clone());
        let mut tokens = old_net.initial_marking[p];
        if p == merge.keep_place {
            tokens += old_net.initial_marking[merge.drop_place];
        }
        new_initial_marking.push(tokens);
    }

    let mut new_transition_map: Vec<Option<usize>> = vec![None; nt];
    let mut new_transitions = Vec::new();
    let mut new_tidx = 0usize;
    for t in 0..nt {
        if t == merge.remove_transition {
            continue;
        }
        let old_trans = &old_net.transitions[t];
        let inputs = remap_and_combine_arcs(&old_trans.inputs, &new_place_map);
        let outputs = remap_and_combine_arcs(&old_trans.outputs, &new_place_map);

        new_transitions.push(TransitionInfo {
            id: old_trans.id.clone(),
            name: old_trans.name.clone(),
            inputs,
            outputs,
        });
        new_transition_map[t] = Some(new_tidx);
        new_tidx += 1;
    }

    let new_reduced_place_map: Vec<Option<PlaceIdx>> = slice
        .reduced_place_map
        .iter()
        .map(|mapped| {
            mapped.and_then(|local| new_place_map[local.0 as usize].map(|new| PlaceIdx(new as u32)))
        })
        .collect();

    let new_place_unmap: Vec<PlaceIdx> = (0..np)
        .filter(|&p| p != merge.drop_place)
        .map(|p| slice.place_unmap[p])
        .collect();

    let new_reduced_transition_map: Vec<Option<TransitionIdx>> = slice
        .reduced_transition_map
        .iter()
        .map(|mapped| {
            mapped.and_then(|local| {
                new_transition_map[local.0 as usize].map(|new| TransitionIdx(new as u32))
            })
        })
        .collect();

    let new_transition_unmap: Vec<TransitionIdx> = (0..nt)
        .filter(|&t| t != merge.remove_transition)
        .map(|t| slice.transition_unmap[t])
        .collect();

    Some(QuerySlice {
        net: PetriNet {
            name: old_net.name.clone(),
            places: new_places,
            transitions: new_transitions,
            initial_marking: new_initial_marking,
        },
        reduced_place_map: new_reduced_place_map,
        place_unmap: new_place_unmap,
        reduced_transition_map: new_reduced_transition_map,
        transition_unmap: new_transition_unmap,
    })
}

fn remap_and_combine_arcs(arcs: &[Arc], place_map: &[Option<usize>]) -> Vec<Arc> {
    let mut combined: std::collections::BTreeMap<u32, u64> = std::collections::BTreeMap::new();
    for arc in arcs {
        if let Some(new_p) = place_map[arc.place.0 as usize] {
            *combined.entry(new_p as u32).or_insert(0) += arc.weight;
        }
    }
    combined
        .into_iter()
        .map(|(place, weight)| Arc {
            place: PlaceIdx(place),
            weight,
        })
        .collect()
}

#[cfg(test)]
#[path = "circulation_loop_tests.rs"]
mod tests;
