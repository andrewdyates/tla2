// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Petri net core operations: apply_delta/undo_delta roundtrip,
//! is_enabled boundary conditions, and multi-input enablement.

use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionIdx, TransitionInfo};

fn arc(place: u32, weight: u64) -> Arc {
    Arc {
        place: PlaceIdx(place),
        weight,
    }
}

fn place(id: &str) -> PlaceInfo {
    PlaceInfo {
        id: id.to_string(),
        name: None,
    }
}

fn trans(id: &str, inputs: Vec<Arc>, outputs: Vec<Arc>) -> TransitionInfo {
    TransitionInfo {
        id: id.to_string(),
        name: None,
        inputs,
        outputs,
    }
}

#[test]
fn test_apply_delta_undo_delta_roundtrip() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![trans("t0", vec![arc(0, 2)], vec![arc(1, 1), arc(2, 3)])],
        initial_marking: vec![5, 0, 0],
    };

    let mut marking = net.initial_marking.clone();
    let original = marking.clone();

    // Apply: [5,0,0] → [3,1,3]
    net.apply_delta(&mut marking, TransitionIdx(0));
    assert_eq!(marking, vec![3, 1, 3]);

    // Undo: [3,1,3] → [5,0,0]
    net.undo_delta(&mut marking, TransitionIdx(0));
    assert_eq!(marking, original);
}

#[test]
fn test_apply_delta_matches_fire() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![trans("t0", vec![arc(0, 2)], vec![arc(1, 1), arc(2, 3)])],
        initial_marking: vec![5, 0, 0],
    };

    let fire_result = net.fire(&net.initial_marking, TransitionIdx(0));
    let mut delta_marking = net.initial_marking.clone();
    net.apply_delta(&mut delta_marking, TransitionIdx(0));
    assert_eq!(fire_result, delta_marking);
}

#[test]
fn test_is_enabled_exact_threshold() {
    // Transition requires exactly 3 tokens from p0
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 3)], vec![arc(1, 1)])],
        initial_marking: vec![3, 0],
    };

    // Exactly enough tokens
    assert!(net.is_enabled(&[3, 0], TransitionIdx(0)));
    // One fewer than required
    assert!(!net.is_enabled(&[2, 0], TransitionIdx(0)));
    // More than required
    assert!(net.is_enabled(&[4, 0], TransitionIdx(0)));
}

#[test]
fn test_is_enabled_multiple_inputs() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![trans("t0", vec![arc(0, 2), arc(1, 1)], vec![arc(2, 1)])],
        initial_marking: vec![2, 1, 0],
    };

    // Both inputs satisfied
    assert!(net.is_enabled(&[2, 1, 0], TransitionIdx(0)));
    // First input fails
    assert!(!net.is_enabled(&[1, 1, 0], TransitionIdx(0)));
    // Second input fails
    assert!(!net.is_enabled(&[2, 0, 0], TransitionIdx(0)));
}
