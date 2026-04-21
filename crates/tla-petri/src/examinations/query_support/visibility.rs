// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! POR visibility helpers for selecting transitions relevant to a query support set.

use crate::petri_net::{PetriNet, TransitionIdx};

use super::types::QuerySupport;

pub(crate) fn visible_transitions_for_support(
    net: &PetriNet,
    support: &QuerySupport,
) -> Option<Vec<TransitionIdx>> {
    let num_transitions = net.num_transitions();
    let mut visible = vec![false; num_transitions];

    mark_transitions_touching_places(net, &support.places, &mut visible);

    let mut fireability_places = vec![false; net.num_places()];
    for (idx, targeted) in support.transitions.iter().enumerate() {
        if *targeted {
            for arc in &net.transitions[idx].inputs {
                fireability_places[arc.place.0 as usize] = true;
            }
        }
    }
    mark_transitions_touching_places(net, &fireability_places, &mut visible);

    let visible_indices: Vec<TransitionIdx> = visible
        .into_iter()
        .enumerate()
        .filter_map(|(idx, marked)| marked.then_some(TransitionIdx(idx as u32)))
        .collect();

    if visible_indices.is_empty() || visible_indices.len() >= num_transitions {
        None
    } else {
        Some(visible_indices)
    }
}

fn mark_transitions_touching_places(
    net: &PetriNet,
    relevant_places: &[bool],
    visible: &mut [bool],
) {
    for (idx, transition) in net.transitions.iter().enumerate() {
        let touches_relevant_place = transition
            .inputs
            .iter()
            .chain(transition.outputs.iter())
            .any(|arc| relevant_places[arc.place.0 as usize]);
        if touches_relevant_place {
            visible[idx] = true;
        }
    }
}
