// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::petri_net::PetriNet;
use crate::reduction::{reduce, ReducedNet};

use super::support::{arc, assert_same_reduced_net, place, trans};

#[test]
fn test_expand_marking_roundtrip() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![trans("t0", vec![arc(0, 1), arc(1, 1)], vec![arc(0, 1)])],
        initial_marking: vec![5, 3, 42],
    };

    let reduced = reduce(&net);
    assert_eq!(reduced.net.initial_marking, vec![3]);

    let expanded = reduced
        .expand_marking(&[3])
        .expect("marking expansion should succeed");
    assert_eq!(expanded, vec![5, 3, 42]);
}

#[test]
fn test_cascade_expand_marking_preserves_cascade_isolated_values() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans("t0_dead", vec![arc(0, 100)], vec![arc(1, 1)]),
            trans("t1_live", vec![arc(2, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![7, 0, 3, 0],
    };

    let reduced = reduce(&net);
    // t0 dead → p0 and p1 cascade-isolated → p3 LP-redundant (never constrains).
    assert_eq!(reduced.net.num_places(), 1);
    assert_eq!(reduced.net.places[0].id, "p2");

    // p3 is reconstructed from P-invariant: p3 = 3 - p2.
    let expanded = reduced
        .expand_marking(&[3])
        .expect("marking expansion should succeed");
    assert_eq!(expanded, vec![7, 0, 3, 0]);
}

#[test]
fn test_compose_identity_reductions_is_identity() {
    let net = PetriNet {
        name: Some("identity".into()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![1, 0],
    };

    let identity = ReducedNet::identity(&net);
    let composed = identity
        .compose(&ReducedNet::identity(&net))
        .expect("identity composition should succeed");
    assert_same_reduced_net(&composed, &identity);
}

#[test]
fn test_compose_real_reduction_with_identity_preserves_result() {
    let net = PetriNet {
        name: Some("compose-real".into()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![trans("t0", vec![arc(0, 1), arc(1, 1)], vec![arc(0, 1)])],
        initial_marking: vec![5, 3, 42],
    };

    let reduced = reduce(&net);
    let composed_after = reduced
        .compose(&ReducedNet::identity(&reduced.net))
        .expect("composition should succeed");
    assert_same_reduced_net(&composed_after, &reduced);

    let composed_before = ReducedNet::identity(&net)
        .compose(&reduced)
        .expect("composition should succeed");
    assert_same_reduced_net(&composed_before, &reduced);
}
