// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Graph traversals for computing closure and relevance cones on reduced nets.

use std::collections::VecDeque;

use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};

use super::types::QuerySupport;

pub(crate) fn closure_on_reduced_net(net: &PetriNet, seeds: QuerySupport) -> QuerySupport {
    let mut closure = seeds;
    let mut pending = VecDeque::new();

    for (idx, keep) in closure.places.iter().enumerate() {
        if *keep {
            pending.push_back(PendingNode::Place(PlaceIdx(idx as u32)));
        }
    }
    for (idx, keep) in closure.transitions.iter().enumerate() {
        if *keep {
            pending.push_back(PendingNode::Transition(TransitionIdx(idx as u32)));
        }
    }

    while let Some(node) = pending.pop_front() {
        match node {
            PendingNode::Place(place) => {
                for (idx, transition) in net.transitions.iter().enumerate() {
                    let touches_place = transition
                        .inputs
                        .iter()
                        .chain(transition.outputs.iter())
                        .any(|arc| arc.place == place);
                    if touches_place && !closure.transitions[idx] {
                        closure.transitions[idx] = true;
                        pending.push_back(PendingNode::Transition(TransitionIdx(idx as u32)));
                    }
                }
            }
            PendingNode::Transition(transition_idx) => {
                let transition = &net.transitions[transition_idx.0 as usize];
                for arc in transition.inputs.iter().chain(transition.outputs.iter()) {
                    let place_idx = arc.place.0 as usize;
                    if !closure.places[place_idx] {
                        closure.places[place_idx] = true;
                        pending.push_back(PendingNode::Place(arc.place));
                    }
                }
            }
        }
    }

    closure
}

enum PendingNode {
    Place(PlaceIdx),
    Transition(TransitionIdx),
}

/// Compute the backward-relevance cone of seed places and transitions.
///
/// Unlike [`closure_on_reduced_net`] which grows symmetrically (including both
/// preset and postset of each relevant transition), this function only follows
/// the enabling direction:
///
/// 1. Relevant place → keep every transition that reads or writes that place
/// 2. Relevant transition → keep only its **preset** (input) places
///
/// This drops forward-only sink tails: transitions that write to an irrelevant
/// output place are still kept (because they touch a relevant place), but those
/// output places are dropped unless they feed back into the preset of another
/// relevant transition.
///
/// The result is strictly ⊆ the connected-component closure on nets with
/// forward-only sinks.
pub(crate) fn relevance_cone_on_reduced_net(net: &PetriNet, seeds: QuerySupport) -> QuerySupport {
    let mut cone = seeds;
    let mut pending = VecDeque::new();

    for (idx, keep) in cone.places.iter().enumerate() {
        if *keep {
            pending.push_back(PendingNode::Place(PlaceIdx(idx as u32)));
        }
    }
    for (idx, keep) in cone.transitions.iter().enumerate() {
        if *keep {
            pending.push_back(PendingNode::Transition(TransitionIdx(idx as u32)));
        }
    }

    while let Some(node) = pending.pop_front() {
        match node {
            PendingNode::Place(place) => {
                // Same as closure: keep every transition that touches this place.
                for (idx, transition) in net.transitions.iter().enumerate() {
                    let touches_place = transition
                        .inputs
                        .iter()
                        .chain(transition.outputs.iter())
                        .any(|arc| arc.place == place);
                    if touches_place && !cone.transitions[idx] {
                        cone.transitions[idx] = true;
                        pending.push_back(PendingNode::Transition(TransitionIdx(idx as u32)));
                    }
                }
            }
            PendingNode::Transition(transition_idx) => {
                // DIFFERENCE from closure: only keep INPUT places (preset),
                // not output places (postset). This is the backward direction.
                let transition = &net.transitions[transition_idx.0 as usize];
                for arc in &transition.inputs {
                    let place_idx = arc.place.0 as usize;
                    if !cone.places[place_idx] {
                        cone.places[place_idx] = true;
                        pending.push_back(PendingNode::Place(arc.place));
                    }
                }
            }
        }
    }

    cone
}
