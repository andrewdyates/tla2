// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Query-relevant irrelevance pruning (Tapaal Rule I).
//!
//! Removes places and transitions that are provably irrelevant to the
//! query being checked. Given a [`QuerySupport`] closure (the set of
//! places and transitions that can affect the query result), this
//! module builds a [`ReducedNet`] step that retains only the relevant
//! structure. The step composes with prior reductions via
//! [`ReducedNet::compose`].

use crate::petri_net::QuerySupport;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, TransitionIdx};

use super::model::ReductionReport;
use super::ReducedNet;

/// Build a reduction step that removes places and transitions outside
/// the given support set.
///
/// `keep` must already be a closed support set (e.g. the output of
/// [`closure_on_reduced_net`](crate::examinations::query_support::closure_on_reduced_net)
/// or
/// [`relevance_cone_on_reduced_net`](crate::examinations::query_support::relevance_cone_on_reduced_net)).
/// The function does NOT compute the closure itself — the caller
/// chooses which closure strategy is appropriate.
///
/// Returns `None` if the support already covers the entire net (no
/// pruning possible).
#[must_use]
pub(crate) fn reduce_irrelevant(net: &PetriNet, keep: &QuerySupport) -> Option<ReducedNet> {
    debug_assert_eq!(keep.places.len(), net.num_places());
    debug_assert_eq!(keep.transitions.len(), net.num_transitions());

    let kept_places: Vec<usize> = keep
        .places
        .iter()
        .enumerate()
        .filter_map(|(idx, &k): (usize, &bool)| k.then_some(idx))
        .collect();
    let kept_transitions: Vec<usize> = keep
        .transitions
        .iter()
        .enumerate()
        .filter_map(|(idx, &k): (usize, &bool)| k.then_some(idx))
        .collect();

    // No pruning if everything is kept.
    if kept_places.len() == net.num_places() && kept_transitions.len() == net.num_transitions() {
        return None;
    }

    // Build forward index maps (old → new).
    let mut place_map: Vec<Option<PlaceIdx>> = vec![None; net.num_places()];
    let mut place_unmap: Vec<PlaceIdx> = Vec::with_capacity(kept_places.len());
    for (new_idx, &old_idx) in kept_places.iter().enumerate() {
        place_map[old_idx] = Some(PlaceIdx(new_idx as u32));
        place_unmap.push(PlaceIdx(old_idx as u32));
    }

    let mut transition_map: Vec<Option<TransitionIdx>> = vec![None; net.num_transitions()];
    let mut transition_unmap: Vec<TransitionIdx> = Vec::with_capacity(kept_transitions.len());
    for (new_idx, &old_idx) in kept_transitions.iter().enumerate() {
        transition_map[old_idx] = Some(TransitionIdx(new_idx as u32));
        transition_unmap.push(TransitionIdx(old_idx as u32));
    }

    // Build pruned net.
    let places: Vec<_> = kept_places.iter().map(|&i| net.places[i].clone()).collect();
    let initial_marking: Vec<u64> = kept_places
        .iter()
        .map(|&i| net.initial_marking[i])
        .collect();
    let transitions: Vec<_> = kept_transitions
        .iter()
        .map(|&i| {
            let orig = &net.transitions[i];
            crate::petri_net::TransitionInfo {
                id: orig.id.clone(),
                name: orig.name.clone(),
                inputs: remap_arcs(&orig.inputs, &place_map),
                outputs: remap_arcs(&orig.outputs, &place_map),
            }
        })
        .collect();

    let pruned = PetriNet {
        name: net.name.clone(),
        places,
        transitions,
        initial_marking,
    };

    // Record constant values for removed places (their initial marking
    // in the input net). These are query-irrelevant, but compose()
    // accumulates them for marking expansion completeness.
    let constant_values: Vec<(PlaceIdx, u64)> = (0..net.num_places())
        .filter(|&i| place_map[i].is_none())
        .map(|i| (PlaceIdx(i as u32), net.initial_marking[i]))
        .collect();

    Some(ReducedNet {
        net: pruned,
        place_map,
        place_unmap,
        place_scales: vec![1; net.num_places()],
        transition_map,
        transition_unmap,
        constant_values,
        reconstructions: Vec::new(),
        report: ReductionReport::default(),
    })
}

/// Remap arcs through the place map, dropping arcs to removed places.
fn remap_arcs(arcs: &[Arc], place_map: &[Option<PlaceIdx>]) -> Vec<Arc> {
    arcs.iter()
        .filter_map(|arc| {
            place_map[arc.place.0 as usize].map(|new_place| Arc {
                place: new_place,
                weight: arc.weight,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::examinations::query_support::closure_on_reduced_net;
    use crate::petri_net::{PlaceInfo, TransitionInfo};

    /// Two disconnected components: {p0, p1, t0} and {q0, q1, t1}.
    /// Querying p0 should prune the entire q-component.
    fn disconnected_net() -> PetriNet {
        PetriNet {
            name: Some(String::from("disconnected")),
            places: vec![
                PlaceInfo {
                    id: String::from("p0"),
                    name: None,
                },
                PlaceInfo {
                    id: String::from("p1"),
                    name: None,
                },
                PlaceInfo {
                    id: String::from("q0"),
                    name: None,
                },
                PlaceInfo {
                    id: String::from("q1"),
                    name: None,
                },
            ],
            transitions: vec![
                TransitionInfo {
                    id: String::from("tp"),
                    name: None,
                    inputs: vec![Arc {
                        place: PlaceIdx(0),
                        weight: 1,
                    }],
                    outputs: vec![Arc {
                        place: PlaceIdx(1),
                        weight: 1,
                    }],
                },
                TransitionInfo {
                    id: String::from("tq"),
                    name: None,
                    inputs: vec![Arc {
                        place: PlaceIdx(2),
                        weight: 1,
                    }],
                    outputs: vec![Arc {
                        place: PlaceIdx(3),
                        weight: 1,
                    }],
                },
            ],
            initial_marking: vec![1, 0, 2, 0],
        }
    }

    #[test]
    fn test_reduce_irrelevant_prunes_disconnected_component() {
        let net = disconnected_net();
        let seeds = QuerySupport {
            places: vec![true, false, false, false],
            transitions: vec![false, false],
        };
        let closure = closure_on_reduced_net(&net, seeds);

        let step = reduce_irrelevant(&net, &closure).expect("should prune q-component");
        assert_eq!(step.net.num_places(), 2, "only p0 and p1 should remain");
        assert_eq!(step.net.num_transitions(), 1, "only tp should remain");
        assert_eq!(step.net.initial_marking, vec![1, 0]);

        // Verify maps.
        assert_eq!(step.place_map[0], Some(PlaceIdx(0))); // p0 → 0
        assert_eq!(step.place_map[1], Some(PlaceIdx(1))); // p1 → 1
        assert_eq!(step.place_map[2], None); // q0 removed
        assert_eq!(step.place_map[3], None); // q1 removed
        assert_eq!(step.transition_map[0], Some(TransitionIdx(0)));
        assert_eq!(step.transition_map[1], None); // tq removed

        // Constant values for removed places.
        assert!(step.constant_values.contains(&(PlaceIdx(2), 2)));
        assert!(step.constant_values.contains(&(PlaceIdx(3), 0)));
    }

    #[test]
    fn test_reduce_irrelevant_returns_none_when_full_support() {
        let net = disconnected_net();
        let full = QuerySupport {
            places: vec![true, true, true, true],
            transitions: vec![true, true],
        };
        assert!(reduce_irrelevant(&net, &full).is_none());
    }

    #[test]
    fn test_reduce_irrelevant_preserves_arcs_within_kept_component() {
        let net = disconnected_net();
        let seeds = QuerySupport {
            places: vec![true, false, false, false],
            transitions: vec![false, false],
        };
        let closure = closure_on_reduced_net(&net, seeds);
        let step = reduce_irrelevant(&net, &closure).expect("should prune");

        // The surviving transition tp should have input p0→0 and output p1→1.
        let t = &step.net.transitions[0];
        assert_eq!(t.inputs.len(), 1);
        assert_eq!(t.inputs[0].place, PlaceIdx(0));
        assert_eq!(t.outputs.len(), 1);
        assert_eq!(t.outputs[0].place, PlaceIdx(1));
    }

    #[test]
    fn test_reduce_irrelevant_composes_with_identity() {
        let net = disconnected_net();
        let identity = ReducedNet::identity(&net);
        let seeds = QuerySupport {
            places: vec![true, false, false, false],
            transitions: vec![false, false],
        };
        let closure = closure_on_reduced_net(&net, seeds);
        let step = reduce_irrelevant(&net, &closure).expect("should prune");

        let composed = identity.compose(&step).expect("compose should succeed");
        assert_eq!(composed.net.num_places(), 2);
        assert_eq!(composed.net.num_transitions(), 1);
        assert_eq!(composed.place_map[0], Some(PlaceIdx(0)));
        assert_eq!(composed.place_map[2], None);
    }
}
