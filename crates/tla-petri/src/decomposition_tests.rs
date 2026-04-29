// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Petri net component decomposition.

use super::*;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};

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

/// Build a 3-stage pipeline:
///
/// ```text
///  p0 -> t0 -> p1 -> t1 -> p2 -> t2 -> p3 -> t3 -> p4 -> t4 -> p5
/// ```
///
/// Each stage is loosely coupled to the next by a single place.
/// With min_component_size=2, this should decompose into multiple components.
fn make_pipeline_3stage() -> PetriNet {
    PetriNet {
        name: Some("pipeline_3stage".to_string()),
        places: vec![
            place("p0"), // stage 1 input
            place("p1"), // stage 1 internal
            place("p2"), // stage 1-2 interface
            place("p3"), // stage 2 internal
            place("p4"), // stage 2-3 interface
            place("p5"), // stage 3 output
        ],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]), // stage 1 internal
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]), // stage 1 -> 2
            trans("t2", vec![arc(2, 1)], vec![arc(3, 1)]), // stage 2 internal
            trans("t3", vec![arc(3, 1)], vec![arc(4, 1)]), // stage 2 -> 3
            trans("t4", vec![arc(4, 1)], vec![arc(5, 1)]), // stage 3 internal
        ],
        initial_marking: vec![3, 0, 0, 0, 0, 0],
    }
}

/// Build a tightly coupled net where every place connects to every other
/// through shared transitions.
fn make_tightly_coupled() -> PetriNet {
    PetriNet {
        name: Some("tight".to_string()),
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            // Every transition touches 3+ places => tight coupling
            trans("t0", vec![arc(0, 1), arc(1, 1)], vec![arc(2, 1), arc(3, 1)]),
            trans("t1", vec![arc(2, 1), arc(3, 1)], vec![arc(0, 1), arc(1, 1)]),
            trans("t2", vec![arc(0, 1), arc(2, 1)], vec![arc(1, 1), arc(3, 1)]),
            trans("t3", vec![arc(1, 1), arc(3, 1)], vec![arc(0, 1), arc(2, 1)]),
        ],
        initial_marking: vec![2, 2, 0, 0],
    }
}

/// Build a net with two clearly independent subsystems connected by
/// a single lightweight transition. Each subsystem has enough internal
/// transitions (heavy weights) to make the bridge's normalized cut well
/// below THETA.
///
/// ```text
///  Subsystem A: p0 <-> t0 <-> p1, p0 <-> t3 <-> p1   (heavy internal)
///  Subsystem B: p2 <-> t1 <-> p3, p2 <-> t4 <-> p3   (heavy internal)
///  Bridge:      p1 -> t2 -> p2                         (weak link, weight 1)
/// ```
fn make_two_component() -> PetriNet {
    PetriNet {
        name: Some("two_component".to_string()),
        places: vec![
            place("p0"), // subsystem A
            place("p1"), // subsystem A (interface)
            place("p2"), // subsystem B (interface)
            place("p3"), // subsystem B
        ],
        transitions: vec![
            trans("t0", vec![arc(0, 5)], vec![arc(1, 5)]), // A internal (heavy)
            trans("t1", vec![arc(2, 5)], vec![arc(3, 5)]), // B internal (heavy)
            trans("t2", vec![arc(1, 1)], vec![arc(2, 1)]), // bridge A->B (light)
            trans("t3", vec![arc(1, 5)], vec![arc(0, 5)]), // A internal (heavy)
            trans("t4", vec![arc(3, 5)], vec![arc(2, 5)]), // B internal (heavy)
        ],
        initial_marking: vec![10, 0, 0, 0],
    }
}

#[test]
fn test_decompose_pipeline_produces_multiple_components() {
    let net = make_pipeline_3stage();
    let components = decompose(&net, 2);

    // Pipeline should decompose into 2+ components since stages are
    // loosely coupled via single places
    assert!(
        components.len() >= 2,
        "pipeline should decompose into at least 2 components, got {}",
        components.len()
    );

    // Every place must appear in exactly one component
    let mut all_places: Vec<u32> = components
        .iter()
        .flat_map(|c| c.places.iter().map(|p| p.0))
        .collect();
    all_places.sort();
    all_places.dedup();
    assert_eq!(
        all_places.len(),
        net.num_places(),
        "every place must appear in exactly one component"
    );

    // Every transition must appear in exactly one component
    let mut all_transitions: Vec<u32> = components
        .iter()
        .flat_map(|c| c.transitions.iter().map(|t| t.0))
        .collect();
    all_transitions.sort();
    all_transitions.dedup();
    assert_eq!(
        all_transitions.len(),
        net.num_transitions(),
        "every transition must appear in exactly one component"
    );

    // At least one component should have interface places (the partition boundary)
    let has_interface = components.iter().any(|c| !c.interface_places.is_empty());
    assert!(
        has_interface,
        "decomposed pipeline should have interface places"
    );
}

#[test]
fn test_decompose_tight_coupling_no_split() {
    let net = make_tightly_coupled();
    let components = decompose(&net, 2);

    // Tightly coupled net should remain as a single component because
    // the normalized cut cost exceeds THETA
    assert_eq!(
        components.len(),
        1,
        "tightly coupled net should NOT decompose, got {} components",
        components.len()
    );

    // Single component should contain all places and transitions
    assert_eq!(components[0].places.len(), net.num_places());
    assert_eq!(components[0].transitions.len(), net.num_transitions());
    assert!(components[0].interface_places.is_empty());
}

#[test]
fn test_decompose_two_component_structure() {
    let net = make_two_component();
    let components = decompose(&net, 1);

    // Should decompose into 2 components
    assert!(
        components.len() >= 2,
        "two-component net should decompose, got {} components",
        components.len()
    );

    // Verify coverage: all places accounted for
    let total_places: usize = components.iter().map(|c| c.places.len()).sum();
    assert_eq!(total_places, net.num_places());

    // Verify coverage: all transitions accounted for
    let total_transitions: usize = components.iter().map(|c| c.transitions.len()).sum();
    assert_eq!(total_transitions, net.num_transitions());
}

#[test]
fn test_decompose_trivially_small_net() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![1, 0],
    };

    // With min_component_size=2, a 2-place net should not decompose
    let components = decompose(&net, 2);
    assert_eq!(components.len(), 1);
    assert_eq!(components[0].places.len(), 2);
}

#[test]
fn test_route_techniques_bounded_small() {
    // Small bounded net -> BFS
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![3, 0],
    };

    let components = decompose(&net, 10);
    let routed = route_techniques(&net, &components);

    assert_eq!(routed.len(), 1);
    // Small bounded net with only 4 possible states -> should route to BFS
    assert_eq!(
        routed[0].1,
        RecommendedTechnique::Bfs,
        "small bounded net should route to BFS"
    );
}

#[test]
fn test_estimate_state_space_basic() {
    // 2 places with bounds 3 and 5 => (3+1) * (5+1) = 24
    let bounds = vec![Some(3), Some(5)];
    let places = vec![PlaceIdx(0), PlaceIdx(1)];
    assert_eq!(estimate_state_space(&bounds, &places), Some(24));
}

#[test]
fn test_estimate_state_space_unbounded() {
    let bounds = vec![Some(3), None];
    let places = vec![PlaceIdx(0), PlaceIdx(1)];
    assert_eq!(estimate_state_space(&bounds, &places), None);
}

#[test]
fn test_hypergraph_construction() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![trans("t0", vec![arc(0, 2)], vec![arc(1, 1), arc(2, 3)])],
        initial_marking: vec![5, 0, 0],
    };

    let hyperedges = build_hypergraph(&net);
    assert_eq!(hyperedges.len(), 1);
    assert_eq!(hyperedges[0].weight, 6); // 2 + 1 + 3
    assert_eq!(hyperedges[0].places.len(), 3);
}

#[test]
fn test_component_places_sorted() {
    let net = make_pipeline_3stage();
    let components = decompose(&net, 2);

    for comp in &components {
        let sorted: Vec<u32> = comp.places.iter().map(|p| p.0).collect();
        let mut check = sorted.clone();
        check.sort();
        assert_eq!(sorted, check, "component places should be sorted");

        let sorted_t: Vec<u32> = comp.transitions.iter().map(|t| t.0).collect();
        let mut check_t = sorted_t.clone();
        check_t.sort();
        assert_eq!(sorted_t, check_t, "component transitions should be sorted");
    }
}
