// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};

use super::analysis_agglomeration::build_place_connectivity;

/// Directed cycle of simple token-moving transitions (Tapaal Rule H).
///
/// `places[i]` is the output place of `transitions[i]`, which is also the
/// input place of `transitions[(i + 1) % transitions.len()]`.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TokenCycle {
    pub transitions: Vec<TransitionIdx>,
    pub places: Vec<PlaceIdx>,
    pub survivor: PlaceIdx,
}

fn dead_transition_mask(net: &PetriNet, dead_transitions: &[TransitionIdx]) -> Vec<bool> {
    let mut is_dead = vec![false; net.num_transitions()];
    for &TransitionIdx(t) in dead_transitions {
        is_dead[t as usize] = true;
    }
    is_dead
}

fn simple_transition_outputs(
    net: &PetriNet,
    dead_transitions: &[TransitionIdx],
) -> Vec<Option<PlaceIdx>> {
    let is_dead = dead_transition_mask(net, dead_transitions);
    let mut outputs = vec![None; net.num_transitions()];

    for (tidx, transition) in net.transitions.iter().enumerate() {
        if is_dead[tidx] {
            continue;
        }
        if transition.inputs.len() != 1 || transition.outputs.len() != 1 {
            continue;
        }
        let input = &transition.inputs[0];
        let output = &transition.outputs[0];
        if input.weight != 1 || output.weight != 1 {
            continue;
        }
        if input.place == output.place {
            continue;
        }
        outputs[tidx] = Some(output.place);
    }

    outputs
}

fn is_protected_place(protected_places: &[bool], place: PlaceIdx) -> bool {
    protected_places
        .get(place.0 as usize)
        .copied()
        .unwrap_or(false)
}

fn record_cycle(
    cycle_transitions: &[TransitionIdx],
    simple_outputs: &[Option<PlaceIdx>],
    protected_places: &[bool],
    seen_cycles: &mut HashSet<Vec<TransitionIdx>>,
    cycles: &mut Vec<TokenCycle>,
) {
    if cycle_transitions.len() < 2 {
        return;
    }

    let mut normalized_transitions = cycle_transitions.to_vec();
    let mut normalized_places = Vec::with_capacity(cycle_transitions.len());
    for &transition in &normalized_transitions {
        let Some(place) = simple_outputs[transition.0 as usize] else {
            return;
        };
        normalized_places.push(place);
    }

    if normalized_places
        .iter()
        .any(|&place| is_protected_place(protected_places, place))
    {
        return;
    }

    let Some((min_pos, _)) = normalized_transitions
        .iter()
        .enumerate()
        .min_by_key(|(_, transition)| transition.0)
    else {
        return;
    };
    normalized_transitions.rotate_left(min_pos);
    normalized_places.rotate_left(min_pos);

    if !seen_cycles.insert(normalized_transitions.clone()) {
        return;
    }

    let Some(survivor) = normalized_places
        .iter()
        .min_by_key(|place| place.0)
        .copied()
    else {
        return;
    };

    cycles.push(TokenCycle {
        transitions: normalized_transitions,
        places: normalized_places,
        survivor,
    });
}

fn dfs_token_cycles(
    transition: TransitionIdx,
    consumers: &[Vec<(TransitionIdx, u64)>],
    simple_outputs: &[Option<PlaceIdx>],
    protected_places: &[bool],
    stack: &mut Vec<TransitionIdx>,
    stack_positions: &mut HashMap<TransitionIdx, usize>,
    seen_cycles: &mut HashSet<Vec<TransitionIdx>>,
    cycles: &mut Vec<TokenCycle>,
) {
    let depth = stack.len();
    stack.push(transition);
    stack_positions.insert(transition, depth);

    let Some(output_place) = simple_outputs[transition.0 as usize] else {
        stack.pop();
        stack_positions.remove(&transition);
        return;
    };

    for &(next_transition, _) in &consumers[output_place.0 as usize] {
        if simple_outputs[next_transition.0 as usize].is_none() {
            continue;
        }

        if let Some(&cycle_start) = stack_positions.get(&next_transition) {
            record_cycle(
                &stack[cycle_start..],
                simple_outputs,
                protected_places,
                seen_cycles,
                cycles,
            );
            continue;
        }

        dfs_token_cycles(
            next_transition,
            consumers,
            simple_outputs,
            protected_places,
            stack,
            stack_positions,
            seen_cycles,
            cycles,
        );
    }

    stack.pop();
    stack_positions.remove(&transition);
}

/// Find all token-passing cycles of simple transitions (Tapaal Rule H detection).
///
/// A "simple" transition has exactly one input arc (weight 1), exactly one
/// output arc (weight 1), distinct input and output places, and is not dead.
/// A cycle is a sequence of simple transitions `t0, t1, ..., t_{k-1}` where the
/// output place of `t_i` is the input place of `t_{(i+1) mod k}`.
///
/// Returns cycles with:
/// - `transitions` rotated so the minimum-index transition is first,
/// - `places[i]` = output place of `transitions[i]` (equivalently input of
///   `transitions[(i+1) mod k]`),
/// - `survivor` = the minimum-index place among `places` (merge target).
///
/// Cycles containing any place in `protected_places` (set to `true`) are
/// excluded — query-protected places must not be merged.
///
/// This is the **detection pass only**. The transform (merging places and
/// redirecting arcs) is a follow-up slice.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn find_token_cycles(
    net: &PetriNet,
    dead_transitions: &[TransitionIdx],
    protected_places: &[bool],
) -> Vec<TokenCycle> {
    let simple_outputs = simple_transition_outputs(net, dead_transitions);
    let connectivity = build_place_connectivity(net, dead_transitions);
    let mut seen_cycles = HashSet::new();
    let mut cycles = Vec::new();

    for tidx in 0..net.num_transitions() {
        if simple_outputs[tidx].is_none() {
            continue;
        }

        let mut stack = Vec::new();
        let mut stack_positions = HashMap::new();
        dfs_token_cycles(
            TransitionIdx(tidx as u32),
            &connectivity.consumers,
            &simple_outputs,
            protected_places,
            &mut stack,
            &mut stack_positions,
            &mut seen_cycles,
            &mut cycles,
        );
    }

    cycles
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
    fn test_finds_two_transition_cycle() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![
                trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 0],
        };

        let cycles = find_token_cycles(&net, &[], &[false, false]);
        assert_eq!(cycles.len(), 1);
        assert_eq!(
            cycles[0],
            TokenCycle {
                transitions: vec![TransitionIdx(0), TransitionIdx(1)],
                places: vec![PlaceIdx(1), PlaceIdx(0)],
                survivor: PlaceIdx(0),
            }
        );
    }

    #[test]
    fn test_skips_cycle_with_protected_place() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![
                trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 0],
        };

        let cycles = find_token_cycles(&net, &[], &[true, false]);
        assert!(cycles.is_empty());
    }

    #[test]
    fn test_skips_cycle_through_dead_transition() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![
                trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 0],
        };

        let cycles = find_token_cycles(&net, &[TransitionIdx(1)], &[false, false]);
        assert!(cycles.is_empty());
    }

    #[test]
    fn test_skips_non_unit_weight() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![
                trans("t0", vec![arc(0, 1)], vec![arc(1, 2)]),
                trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 0],
        };

        let cycles = find_token_cycles(&net, &[], &[false, false]);
        assert!(cycles.is_empty());
    }

    #[test]
    fn test_skips_multi_arc_transition() {
        let multi_output_net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1"), place("p2")],
            transitions: vec![
                trans("t0", vec![arc(0, 1)], vec![arc(1, 1), arc(2, 1)]),
                trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 0, 0],
        };
        assert!(find_token_cycles(&multi_output_net, &[], &[false, false, false]).is_empty());

        let multi_input_net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1"), place("p2")],
            transitions: vec![
                trans("t0", vec![arc(0, 1), arc(1, 1)], vec![arc(2, 1)]),
                trans("t1", vec![arc(2, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 1, 0],
        };
        assert!(find_token_cycles(&multi_input_net, &[], &[false, false, false]).is_empty());
    }

    #[test]
    fn test_finds_three_transition_cycle() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1"), place("p2")],
            transitions: vec![
                trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
                trans("t2", vec![arc(2, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 0, 0],
        };

        let cycles = find_token_cycles(&net, &[], &[false, false, false]);
        assert_eq!(cycles.len(), 1);
        assert_eq!(
            cycles[0],
            TokenCycle {
                transitions: vec![TransitionIdx(0), TransitionIdx(1), TransitionIdx(2)],
                places: vec![PlaceIdx(1), PlaceIdx(2), PlaceIdx(0)],
                survivor: PlaceIdx(0),
            }
        );
    }

    #[test]
    fn test_ignores_non_cyclic_chain() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1"), place("p2")],
            transitions: vec![
                trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            ],
            initial_marking: vec![1, 0, 0],
        };

        let cycles = find_token_cycles(&net, &[], &[false, false, false]);
        assert!(cycles.is_empty());
    }

    #[test]
    fn test_cycle_normalization() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
            transitions: vec![
                trans("t0", vec![arc(0, 1)], vec![arc(2, 1)]),
                trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
                trans("t2", vec![arc(2, 1)], vec![arc(3, 1)]),
                trans("t3", vec![arc(3, 1)], vec![arc(1, 1)]),
            ],
            initial_marking: vec![1, 0, 0, 0],
        };

        let cycles = find_token_cycles(&net, &[], &[false, false, false, false]);
        assert_eq!(cycles.len(), 1);
        assert_eq!(
            cycles[0].transitions,
            vec![TransitionIdx(1), TransitionIdx(2), TransitionIdx(3)]
        );
    }
}
