// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;

use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};

use super::analysis_agglomeration::build_place_connectivity;
use super::model::SimpleChainPlace;

fn dead_transition_mask(net: &PetriNet, dead_transitions: &[TransitionIdx]) -> Vec<bool> {
    let mut is_dead = vec![false; net.num_transitions()];
    for &TransitionIdx(t) in dead_transitions {
        is_dead[t as usize] = true;
    }
    is_dead
}

/// Find pure consumer transitions that can only discard tokens from
/// unprotected places.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn find_sink_transitions(
    net: &PetriNet,
    dead_transitions: &[TransitionIdx],
    protected_places: &[bool],
) -> Vec<TransitionIdx> {
    let is_dead = dead_transition_mask(net, dead_transitions);
    let mut sink_transitions = Vec::new();

    for (tidx, transition) in net.transitions.iter().enumerate() {
        if is_dead[tidx] {
            continue;
        }
        if transition.inputs.is_empty() {
            continue;
        }
        if !transition.outputs.is_empty() {
            continue;
        }
        if transition.inputs.iter().any(|arc| {
            protected_places
                .get(arc.place.0 as usize)
                .copied()
                .unwrap_or(false)
        }) {
            continue;
        }

        sink_transitions.push(TransitionIdx(tidx as u32));
    }

    sink_transitions
}

/// Find weight-preserving 1-producer/1-consumer chains whose intermediate
/// place can be eliminated by merging the endpoint transitions.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn find_simple_chain_places(
    net: &PetriNet,
    dead_transitions: &[TransitionIdx],
    protected_places: &[bool],
) -> Vec<SimpleChainPlace> {
    let connectivity = build_place_connectivity(net, dead_transitions);
    let mut chain_places = Vec::new();

    for place_idx in 0..net.num_places() {
        if protected_places.get(place_idx).copied().unwrap_or(false) {
            continue;
        }
        if net.initial_marking[place_idx] != 0 {
            continue;
        }
        if connectivity.producers[place_idx].len() != 1
            || connectivity.consumers[place_idx].len() != 1
        {
            continue;
        }

        let (producer, produced_weight) = connectivity.producers[place_idx][0];
        let (consumer, consumed_weight) = connectivity.consumers[place_idx][0];
        if producer == consumer || produced_weight != consumed_weight {
            continue;
        }

        let place = PlaceIdx(place_idx as u32);
        let producer_transition = &net.transitions[producer.0 as usize];
        if producer_transition.outputs.len() != 1 || producer_transition.outputs[0].place != place {
            continue;
        }

        let consumer_transition = &net.transitions[consumer.0 as usize];
        if consumer_transition.inputs.len() != 1 || consumer_transition.inputs[0].place != place {
            continue;
        }

        let producer_inputs: HashSet<u32> = producer_transition
            .inputs
            .iter()
            .map(|arc| arc.place.0)
            .collect();
        let has_false_self_loop = consumer_transition
            .outputs
            .iter()
            .any(|arc| producer_inputs.contains(&arc.place.0));
        if has_false_self_loop {
            continue;
        }

        chain_places.push(SimpleChainPlace {
            place,
            producer,
            consumer,
            weight: produced_weight,
        });
    }

    chain_places
}

/// Find additional dead transitions by detecting zero-marked place sets that
/// are closed under token production from live transitions.
///
/// Starting from all zero-marked places, iteratively drop any place that can
/// receive a token from a live transition whose inputs are entirely outside
/// the current set. The remaining places stay empty forever, so any live
/// transition that consumes from them is dead.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn find_trap_dead_transitions(
    net: &PetriNet,
    dead_transitions: &[TransitionIdx],
) -> Vec<TransitionIdx> {
    let connectivity = build_place_connectivity(net, dead_transitions);
    let is_dead = dead_transition_mask(net, dead_transitions);
    let mut in_zero_trap = net
        .initial_marking
        .iter()
        .map(|&tokens| tokens == 0)
        .collect::<Vec<_>>();

    loop {
        let mut to_remove = Vec::new();

        for place_idx in 0..net.num_places() {
            if !in_zero_trap[place_idx] {
                continue;
            }

            let can_receive_from_outside =
                connectivity.producers[place_idx].iter().any(|&(t, _)| {
                    let transition = &net.transitions[t.0 as usize];
                    !transition
                        .inputs
                        .iter()
                        .any(|arc| in_zero_trap[arc.place.0 as usize])
                });
            if can_receive_from_outside {
                to_remove.push(place_idx);
            }
        }

        if to_remove.is_empty() {
            break;
        }

        for place_idx in to_remove {
            in_zero_trap[place_idx] = false;
        }
    }

    let mut trap_dead_transitions = Vec::new();
    for (tidx, transition) in net.transitions.iter().enumerate() {
        if is_dead[tidx] {
            continue;
        }
        if transition
            .inputs
            .iter()
            .any(|arc| in_zero_trap[arc.place.0 as usize])
        {
            trap_dead_transitions.push(TransitionIdx(tidx as u32));
        }
    }

    trap_dead_transitions
}

#[cfg(test)]
mod tests {
    use crate::petri_net::{Arc, PlaceInfo, TransitionInfo};

    use super::*;

    fn place(id: &str) -> PlaceInfo {
        PlaceInfo {
            id: id.to_string(),
            name: Some(id.to_string()),
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
            name: Some(id.to_string()),
            inputs,
            outputs,
        }
    }

    #[test]
    fn test_find_sink_transitions_pure_consumer_detected() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![
                trans("t_sink", vec![arc(0, 1)], vec![]),
                trans("t_real", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 1],
        };

        let detected = find_sink_transitions(&net, &[], &[false, false]);
        assert_eq!(detected, vec![TransitionIdx(0)]);
    }

    #[test]
    fn test_find_sink_transitions_protected_and_spontaneous_skipped() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![
                trans("t_protected", vec![arc(0, 1)], vec![]),
                trans("t_spontaneous", vec![], vec![]),
                trans("t_sink", vec![arc(1, 2)], vec![]),
            ],
            initial_marking: vec![1, 2],
        };

        let detected = find_sink_transitions(&net, &[], &[true, false]);
        assert_eq!(detected, vec![TransitionIdx(2)]);
    }

    #[test]
    fn test_find_sink_transitions_dead_transition_skipped() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0")],
            transitions: vec![trans("t_dead_sink", vec![arc(0, 1)], vec![])],
            initial_marking: vec![0],
        };

        let detected = find_sink_transitions(&net, &[TransitionIdx(0)], &[false]);
        assert!(detected.is_empty());
    }

    #[test]
    fn test_find_simple_chain_places_weighted_chain_detected() {
        let net = PetriNet {
            name: None,
            places: vec![
                place("p_in"),
                place("p_mid"),
                place("p_out0"),
                place("p_out1"),
            ],
            transitions: vec![
                trans("t_in", vec![arc(0, 2)], vec![arc(1, 2)]),
                trans("t_out", vec![arc(1, 2)], vec![arc(2, 1), arc(3, 1)]),
            ],
            initial_marking: vec![2, 0, 0, 0],
        };

        let detected = find_simple_chain_places(&net, &[], &[false; 4]);
        assert_eq!(
            detected,
            vec![SimpleChainPlace {
                place: PlaceIdx(1),
                producer: TransitionIdx(0),
                consumer: TransitionIdx(1),
                weight: 2,
            }]
        );
    }

    #[test]
    fn test_find_simple_chain_places_false_self_loop_blocked() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p_mid"), place("p_out")],
            transitions: vec![
                trans("t_in", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t_out", vec![arc(1, 1)], vec![arc(0, 1), arc(2, 1)]),
            ],
            initial_marking: vec![1, 0, 0],
        };

        let detected = find_simple_chain_places(&net, &[], &[false; 3]);
        assert!(detected.is_empty());
    }

    #[test]
    fn test_find_simple_chain_places_weight_mismatch_and_protection_skipped() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1"), place("p2")],
            transitions: vec![
                trans("t_in", vec![arc(0, 2)], vec![arc(1, 2)]),
                trans("t_out", vec![arc(1, 1)], vec![arc(2, 1)]),
            ],
            initial_marking: vec![2, 0, 0],
        };

        assert!(find_simple_chain_places(&net, &[], &[false; 3]).is_empty());
        assert!(find_simple_chain_places(&net, &[], &[false, true, false]).is_empty());
    }

    #[test]
    fn test_find_trap_dead_transitions_zero_marked_cycle_detected() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![
                trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![0, 0],
        };

        let detected = find_trap_dead_transitions(&net, &[]);
        assert_eq!(detected, vec![TransitionIdx(0), TransitionIdx(1)]);
    }

    #[test]
    fn test_find_trap_dead_transitions_external_producer_breaks_trap() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1"), place("p_src")],
            transitions: vec![
                trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
                trans("t_src", vec![arc(2, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![0, 0, 1],
        };

        let detected = find_trap_dead_transitions(&net, &[]);
        assert!(detected.is_empty());
    }

    #[test]
    fn test_find_trap_dead_transitions_mixed_input_consumer_detected() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1"), place("p_live"), place("p_out")],
            transitions: vec![
                trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
                trans("t2", vec![arc(0, 1), arc(2, 1)], vec![arc(3, 1)]),
            ],
            initial_marking: vec![0, 0, 1, 0],
        };

        let detected = find_trap_dead_transitions(&net, &[]);
        assert_eq!(
            detected,
            vec![TransitionIdx(0), TransitionIdx(1), TransitionIdx(2)]
        );
    }
}
