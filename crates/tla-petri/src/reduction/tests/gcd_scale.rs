// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::error::PnmlError;
use crate::marking::{PreparedMarking, TokenWidth};
use crate::petri_net::{PetriNet, TransitionIdx};
use crate::reduction::{reduce_iterative, reduce_iterative_structural, ReducedNet};

use super::super::gcd_scale::apply_final_place_gcd_scaling;
use super::support::{arc, place, trans};

fn weighted_cycle_net(weight: u64, initial_tokens: u64) -> PetriNet {
    PetriNet {
        name: Some(format!("weighted-cycle-{weight}")),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, weight)], vec![arc(1, weight)]),
            trans("t1", vec![arc(1, weight)], vec![arc(0, weight)]),
        ],
        initial_marking: vec![initial_tokens, 0],
    }
}

fn mixed_scale_net() -> PetriNet {
    PetriNet {
        name: Some("mixed-scale".into()),
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans("t0", vec![arc(0, 4)], vec![arc(1, 4)]),
            trans("t1", vec![arc(1, 4)], vec![arc(0, 4)]),
            trans("t2", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t3", vec![arc(3, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![8, 0, 1, 0],
    }
}

#[test]
fn test_final_gcd_scaling_divides_incident_arcs_and_initial_marking() {
    let reduced = reduce_iterative(&weighted_cycle_net(2, 4)).expect("reduction should succeed");

    assert_eq!(reduced.net.initial_marking, vec![2, 0]);
    assert_eq!(reduced.place_scales, vec![2, 2]);
    assert_eq!(reduced.net.transitions[0].inputs[0].weight, 1);
    assert_eq!(reduced.net.transitions[0].outputs[0].weight, 1);
    assert_eq!(reduced.net.transitions[1].inputs[0].weight, 1);
    assert_eq!(reduced.net.transitions[1].outputs[0].weight, 1);
}

#[test]
fn test_expand_marking_restores_original_scale_after_gcd_reduction() {
    let net = weighted_cycle_net(2, 4);
    let reduced = reduce_iterative(&net).expect("reduction should succeed");

    let original_successor = net.fire(&net.initial_marking, TransitionIdx(0));
    let reduced_successor = reduced
        .net
        .fire(&reduced.net.initial_marking, TransitionIdx(0));

    assert_eq!(reduced_successor, vec![1, 1]);
    assert_eq!(
        reduced
            .expand_marking(&reduced_successor)
            .expect("marking expansion should succeed"),
        original_successor
    );
}

#[test]
fn test_gcd_scaling_skips_places_without_nontrivial_factor() {
    let reduced = reduce_iterative(&mixed_scale_net()).expect("reduction should succeed");

    assert_eq!(reduced.place_scales, vec![4, 4, 1, 1]);
    assert_eq!(reduced.net.initial_marking, vec![2, 0, 1, 0]);
    assert_eq!(reduced.net.transitions[0].inputs[0].weight, 1);
    assert_eq!(reduced.net.transitions[0].outputs[0].weight, 1);
    assert_eq!(reduced.net.transitions[1].inputs[0].weight, 1);
    assert_eq!(reduced.net.transitions[1].outputs[0].weight, 1);
    assert_eq!(reduced.net.transitions[2].inputs[0].weight, 1);
    assert_eq!(reduced.net.transitions[2].outputs[0].weight, 1);
    assert_eq!(reduced.net.transitions[3].inputs[0].weight, 1);
    assert_eq!(reduced.net.transitions[3].outputs[0].weight, 1);
}

#[test]
fn test_reduce_iterative_keeps_transition_maps_identity_under_scaling() {
    let reduced = reduce_iterative(&weighted_cycle_net(2, 4)).expect("reduction should succeed");

    assert_eq!(
        reduced.transition_map,
        vec![Some(TransitionIdx(0)), Some(TransitionIdx(1))]
    );
    assert_eq!(
        reduced.transition_unmap,
        vec![TransitionIdx(0), TransitionIdx(1)]
    );
}

#[test]
fn test_reduce_iterative_gcd_scaling_can_shrink_marking_width() {
    let net = weighted_cycle_net(256, 512);
    let structural =
        reduce_iterative_structural(&net).expect("structural reduction should succeed");
    let scaled = reduce_iterative(&net).expect("reduction should succeed");

    assert_eq!(
        PreparedMarking::analyze(&structural.net).width,
        TokenWidth::U16
    );
    assert_eq!(PreparedMarking::analyze(&scaled.net).width, TokenWidth::U8);
    assert_eq!(scaled.net.initial_marking, vec![2, 0]);
    assert_eq!(scaled.place_scales, vec![256, 256]);
}

#[test]
fn test_gcd_scaling_returns_error_on_place_scale_overflow() {
    use super::support::{arc, place, trans};

    // Build a ReducedNet whose place_scales are already near u64::MAX,
    // then apply GCD scaling with factor > 1 to trigger checked_mul overflow.
    let net = PetriNet {
        name: Some("gcd-overflow".into()),
        places: vec![place("p0")],
        transitions: vec![trans("t0", vec![arc(0, 2)], vec![arc(0, 2)])],
        initial_marking: vec![4],
    };
    let mut reduced = ReducedNet::identity(&net);
    // Pre-set the place scale to near u64::MAX so that GCD factor=2 overflows.
    reduced.place_scales = vec![u64::MAX / 2 + 1];

    let error = apply_final_place_gcd_scaling(&mut reduced)
        .expect_err("GCD scale overflow should fail closed");
    assert!(matches!(
        error,
        PnmlError::ReductionOverflow { ref context }
            if context.contains("place scale overflow")
    ));
}
