// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::petri_net::QuerySupport;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, TransitionIdx, TransitionInfo};

#[derive(Debug, Clone)]
pub(crate) struct QuerySlice {
    pub(crate) net: PetriNet,
    pub(crate) reduced_place_map: Vec<Option<PlaceIdx>>,
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) place_unmap: Vec<PlaceIdx>,
    pub(crate) reduced_transition_map: Vec<Option<TransitionIdx>>,
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) transition_unmap: Vec<TransitionIdx>,
}

impl QuerySlice {
    #[must_use]
    pub(crate) fn compose_place_map(&self, upstream: &[Option<PlaceIdx>]) -> Vec<Option<PlaceIdx>> {
        upstream
            .iter()
            .map(|mapped| mapped.and_then(|place| self.reduced_place_map[place.0 as usize]))
            .collect()
    }

    #[must_use]
    pub(crate) fn compose_transition_map(
        &self,
        upstream: &[Option<TransitionIdx>],
    ) -> Vec<Option<TransitionIdx>> {
        upstream
            .iter()
            .map(|mapped| {
                mapped.and_then(|transition| self.reduced_transition_map[transition.0 as usize])
            })
            .collect()
    }
}

pub(crate) fn build_query_slice(net: &PetriNet, support: &QuerySupport) -> Option<QuerySlice> {
    if support.is_empty() {
        return None;
    }
    if support.places.len() != net.num_places()
        || support.transitions.len() != net.num_transitions()
    {
        return None;
    }

    let kept_places: Vec<usize> = support
        .places
        .iter()
        .enumerate()
        .filter_map(|(idx, keep)| keep.then_some(idx))
        .collect();
    let kept_transitions: Vec<usize> = support
        .transitions
        .iter()
        .enumerate()
        .filter_map(|(idx, keep)| keep.then_some(idx))
        .collect();

    if kept_places.len() == net.num_places() && kept_transitions.len() == net.num_transitions() {
        return None;
    }

    let mut reduced_place_map = vec![None; net.num_places()];
    let mut place_unmap = Vec::with_capacity(kept_places.len());
    let places = kept_places
        .iter()
        .enumerate()
        .map(|(new_idx, &old_idx)| {
            reduced_place_map[old_idx] = Some(PlaceIdx(new_idx as u32));
            place_unmap.push(PlaceIdx(old_idx as u32));
            net.places[old_idx].clone()
        })
        .collect();

    let mut reduced_transition_map = vec![None; net.num_transitions()];
    let mut transition_unmap = Vec::with_capacity(kept_transitions.len());
    let transitions = kept_transitions
        .iter()
        .enumerate()
        .map(|(new_idx, &old_idx)| {
            reduced_transition_map[old_idx] = Some(TransitionIdx(new_idx as u32));
            transition_unmap.push(TransitionIdx(old_idx as u32));
            remap_transition(&net.transitions[old_idx], &reduced_place_map)
        })
        .collect::<Option<Vec<TransitionInfo>>>()?;

    let initial_marking = kept_places
        .iter()
        .map(|&place_idx| net.initial_marking[place_idx])
        .collect();

    Some(QuerySlice {
        net: PetriNet {
            name: net.name.clone(),
            places,
            transitions,
            initial_marking,
        },
        reduced_place_map,
        place_unmap,
        reduced_transition_map,
        transition_unmap,
    })
}

fn remap_transition(
    transition: &TransitionInfo,
    place_map: &[Option<PlaceIdx>],
) -> Option<TransitionInfo> {
    Some(TransitionInfo {
        id: transition.id.clone(),
        name: transition.name.clone(),
        inputs: remap_arcs(&transition.inputs, place_map)?,
        outputs: remap_arcs(&transition.outputs, place_map)?,
    })
}

fn remap_arcs(arcs: &[Arc], place_map: &[Option<PlaceIdx>]) -> Option<Vec<Arc>> {
    arcs.iter()
        .map(|arc| {
            Some(Arc {
                place: place_map[arc.place.0 as usize]?,
                weight: arc.weight,
            })
        })
        .collect()
}

/// Filter arcs to only those whose places survive in the kept set.
///
/// Unlike [`remap_arcs`] which fails when any arc's place is missing,
/// this keeps only the arcs whose places are present.
fn filter_arcs(arcs: &[Arc], place_map: &[Option<PlaceIdx>]) -> Vec<Arc> {
    arcs.iter()
        .filter_map(|arc| {
            Some(Arc {
                place: place_map[arc.place.0 as usize]?,
                weight: arc.weight,
            })
        })
        .collect()
}

/// Build a query-local slice that can trim irrelevant output arcs.
///
/// Unlike [`build_query_slice`] which requires every kept transition's input
/// AND output places to be in the kept set, this builder:
///
/// 1. Remaps transition **inputs** fail-closed (every input place must be kept)
/// 2. Remaps transition **outputs** by filtering to kept places only
///
/// This allows keeping a transition while dropping its irrelevant output
/// places — the key capability needed for directional relevance cones.
///
/// Returns `None` when the local net removes zero places and zero transitions,
/// or when a kept transition has an input place that isn't kept.
pub(crate) fn build_query_local_slice(
    net: &PetriNet,
    support: &QuerySupport,
) -> Option<QuerySlice> {
    if support.is_empty() {
        return None;
    }
    if support.places.len() != net.num_places()
        || support.transitions.len() != net.num_transitions()
    {
        return None;
    }

    let kept_places: Vec<usize> = support
        .places
        .iter()
        .enumerate()
        .filter_map(|(idx, keep)| keep.then_some(idx))
        .collect();
    let kept_transitions: Vec<usize> = support
        .transitions
        .iter()
        .enumerate()
        .filter_map(|(idx, keep)| keep.then_some(idx))
        .collect();

    if kept_places.len() == net.num_places() && kept_transitions.len() == net.num_transitions() {
        return None;
    }

    let mut reduced_place_map = vec![None; net.num_places()];
    let mut place_unmap = Vec::with_capacity(kept_places.len());
    let places = kept_places
        .iter()
        .enumerate()
        .map(|(new_idx, &old_idx)| {
            reduced_place_map[old_idx] = Some(PlaceIdx(new_idx as u32));
            place_unmap.push(PlaceIdx(old_idx as u32));
            net.places[old_idx].clone()
        })
        .collect();

    let mut reduced_transition_map = vec![None; net.num_transitions()];
    let mut transition_unmap = Vec::with_capacity(kept_transitions.len());
    let transitions = kept_transitions
        .iter()
        .enumerate()
        .map(|(new_idx, &old_idx)| {
            let t = &net.transitions[old_idx];
            // Inputs must all be kept (fail-closed).
            let inputs = remap_arcs(&t.inputs, &reduced_place_map)?;
            // Outputs: filter to kept places only.
            let outputs = filter_arcs(&t.outputs, &reduced_place_map);
            reduced_transition_map[old_idx] = Some(TransitionIdx(new_idx as u32));
            transition_unmap.push(TransitionIdx(old_idx as u32));
            Some(TransitionInfo {
                id: t.id.clone(),
                name: t.name.clone(),
                inputs,
                outputs,
            })
        })
        .collect::<Option<Vec<TransitionInfo>>>()?;

    let initial_marking = kept_places
        .iter()
        .map(|&place_idx| net.initial_marking[place_idx])
        .collect();

    Some(QuerySlice {
        net: PetriNet {
            name: net.name.clone(),
            places,
            transitions,
            initial_marking,
        },
        reduced_place_map,
        place_unmap,
        reduced_transition_map,
        transition_unmap,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::petri_net::{PlaceInfo, TransitionInfo};

    fn two_component_net() -> PetriNet {
        PetriNet {
            name: Some(String::from("two-components")),
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
            initial_marking: vec![1, 0, 1, 0],
        }
    }

    #[test]
    fn test_build_query_slice_keeps_only_requested_component() {
        let net = two_component_net();
        let support = QuerySupport {
            places: vec![true, true, false, false],
            transitions: vec![true, false],
        };

        let slice =
            build_query_slice(&net, &support).expect("component slice should shrink the net");
        assert_eq!(slice.net.num_places(), 2);
        assert_eq!(slice.net.num_transitions(), 1);
        assert_eq!(slice.place_unmap, vec![PlaceIdx(0), PlaceIdx(1)]);
        assert_eq!(slice.transition_unmap, vec![TransitionIdx(0)]);
    }

    #[test]
    fn test_build_query_slice_returns_none_for_full_support() {
        let net = two_component_net();
        let support = QuerySupport {
            places: vec![true; 4],
            transitions: vec![true; 2],
        };

        assert!(build_query_slice(&net, &support).is_none());
    }

    /// Net where t0 has an output place (sink) NOT in the kept set.
    /// build_query_slice would fail (requires all outputs kept).
    /// build_query_local_slice keeps t0 but filters out the sink output.
    fn sink_output_net() -> PetriNet {
        PetriNet {
            name: Some(String::from("sink-output")),
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
                    id: String::from("sink"),
                    name: None,
                },
            ],
            transitions: vec![
                // t0: p0 -> p1, sink
                TransitionInfo {
                    id: String::from("t0"),
                    name: None,
                    inputs: vec![Arc {
                        place: PlaceIdx(0),
                        weight: 1,
                    }],
                    outputs: vec![
                        Arc {
                            place: PlaceIdx(1),
                            weight: 1,
                        },
                        Arc {
                            place: PlaceIdx(2),
                            weight: 1,
                        },
                    ],
                },
            ],
            initial_marking: vec![1, 0, 0],
        }
    }

    #[test]
    fn test_build_query_local_slice_trims_output_arcs() {
        let net = sink_output_net();
        // Keep p0, p1, t0 — but NOT sink.
        let support = QuerySupport {
            places: vec![true, true, false],
            transitions: vec![true],
        };

        // The induced-subnet builder fails because t0's output to sink is unmapped.
        assert!(build_query_slice(&net, &support).is_none());

        // The query-local builder keeps t0 with only p1 in its outputs.
        let slice = build_query_local_slice(&net, &support)
            .expect("query-local slice should handle trimmed outputs");
        assert_eq!(slice.net.num_places(), 2);
        assert_eq!(slice.net.num_transitions(), 1);
        assert_eq!(slice.net.transitions[0].inputs.len(), 1);
        assert_eq!(slice.net.transitions[0].outputs.len(), 1);
        assert_eq!(slice.net.transitions[0].outputs[0].place, PlaceIdx(1));
    }

    #[test]
    fn test_build_query_local_slice_fails_on_missing_input() {
        let net = sink_output_net();
        // Keep p1, sink, t0 — but NOT p0 (t0's input).
        let support = QuerySupport {
            places: vec![false, true, true],
            transitions: vec![true],
        };

        // Fail-closed: t0's input p0 is not in the kept set.
        assert!(build_query_local_slice(&net, &support).is_none());
    }
}
