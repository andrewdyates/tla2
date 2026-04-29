// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::petri_net::PlaceInfo;

fn place(id: &str) -> PlaceInfo {
    PlaceInfo {
        id: id.into(),
        name: None,
    }
}

fn arc(p: u32, w: u64) -> Arc {
    Arc {
        place: PlaceIdx(p),
        weight: w,
    }
}

fn trans(id: &str, inputs: Vec<Arc>, outputs: Vec<Arc>) -> TransitionInfo {
    TransitionInfo {
        id: id.into(),
        name: None,
        inputs,
        outputs,
    }
}

fn simple_loop_net() -> PetriNet {
    PetriNet {
        name: Some("simple-loop".into()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![3, 2],
    }
}

fn identity_slice(net: &PetriNet) -> QuerySlice {
    let np = net.num_places();
    let nt = net.num_transitions();
    QuerySlice {
        net: net.clone(),
        reduced_place_map: (0..np).map(|i| Some(PlaceIdx(i as u32))).collect(),
        place_unmap: (0..np).map(|i| PlaceIdx(i as u32)).collect(),
        reduced_transition_map: (0..nt).map(|i| Some(TransitionIdx(i as u32))).collect(),
        transition_unmap: (0..nt).map(|i| TransitionIdx(i as u32)).collect(),
    }
}

#[test]
fn test_circulation_loop_contracts_simple_loop() {
    let net = simple_loop_net();
    let slice = identity_slice(&net);
    let protected = vec![false; net.num_places()];

    let result = reduce_query_local_circulation_loops_fixpoint(slice, &protected)
        .expect("simple loop should be contractable");

    assert_eq!(result.net.num_places(), 1);
    assert_eq!(result.net.initial_marking[0], 5);
    assert!(result.net.num_transitions() <= 1);
}

#[test]
fn test_circulation_loop_no_contraction_when_protected() {
    let net = simple_loop_net();
    let slice = identity_slice(&net);
    let protected = vec![true; net.num_places()];

    assert!(
        reduce_query_local_circulation_loops_fixpoint(slice, &protected).is_none(),
        "no contraction when all places are protected"
    );
}

#[test]
fn test_circulation_loop_preserves_marking_sum() {
    let net = PetriNet {
        name: Some("three-loop".into()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t2", vec![arc(2, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![5, 3, 2],
    };
    let slice = identity_slice(&net);
    let protected = vec![false; 3];

    let result = reduce_query_local_circulation_loops_fixpoint(slice, &protected)
        .expect("three-place loop should contract");

    let total: u64 = result.net.initial_marking.iter().sum();
    assert_eq!(total, 10, "total tokens = 5+3+2 = 10");
    assert!(result.net.num_places() < 3);
}

#[test]
fn test_circulation_loop_skips_heavy_weight_arcs() {
    let net = PetriNet {
        name: Some("heavy-loop".into()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 2)], vec![arc(1, 2)]),
            trans("t1", vec![arc(1, 2)], vec![arc(0, 2)]),
        ],
        initial_marking: vec![4, 2],
    };
    let slice = identity_slice(&net);
    let protected = vec![false; 2];

    assert!(
        reduce_query_local_circulation_loops_fixpoint(slice, &protected).is_none(),
        "heavy arcs should not be contracted"
    );
}

#[test]
fn test_circulation_loop_two_independent_loops() {
    let net = PetriNet {
        name: Some("two-loops".into()),
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
            trans("t2", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t3", vec![arc(3, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![1, 2, 3, 4],
    };
    let slice = identity_slice(&net);
    let protected = vec![false; 4];

    let result = reduce_query_local_circulation_loops_fixpoint(slice, &protected)
        .expect("both loops should be contractable");

    assert_eq!(result.net.num_places(), 2);
    let total: u64 = result.net.initial_marking.iter().sum();
    assert_eq!(total, 10);
}

#[test]
fn test_circulation_loop_protected_neighbor_prevents_contraction() {
    let net = PetriNet {
        name: Some("protected-neighbor".into()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
            trans("t_ext", vec![arc(2, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 1, 1],
    };
    let slice = identity_slice(&net);
    let protected = vec![false, false, true];

    assert!(
        reduce_query_local_circulation_loops_fixpoint(slice, &protected).is_none(),
        "protected neighbor should prevent contraction"
    );
}
