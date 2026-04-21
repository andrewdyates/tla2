// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::invariant::{compute_p_invariants, find_implied_places};
use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};
use crate::reduction::{reduce, reduce_iterative};

use super::support::{arc, place, trans};

/// Redundant capacity net.
///
/// 3 places: p_cap(5), p_use(0), p_res(3)
/// t_use:     {p_cap→1, p_res→1} → {p_use→1}
/// t_release: {p_use→1}          → {p_cap→1, p_res→1}
///
/// P-invariants: p_cap + p_use = 5, p_use + p_res = 3.
/// p_cap is LP-redundant: M(p_cap) = M(p_res) + 2, so whenever t_use
/// can fire (M(p_res) >= 1), M(p_cap) >= 3 >= 1. p_cap never constrains.
/// p_res is NOT redundant: M(p_res) = M(p_cap) - 2 can reach 0 < 1.
fn make_redundant_capacity_net() -> PetriNet {
    PetriNet {
        name: Some("redundant-capacity".into()),
        places: vec![place("p_cap"), place("p_use"), place("p_res")],
        transitions: vec![
            trans("t_use", vec![arc(0, 1), arc(2, 1)], vec![arc(1, 1)]),
            trans("t_release", vec![arc(1, 1)], vec![arc(0, 1), arc(2, 1)]),
        ],
        initial_marking: vec![5, 0, 3],
    }
}

#[test]
fn test_redundant_place_detected_and_removed() {
    let net = make_redundant_capacity_net();
    let reduced = reduce(&net);

    // p_cap (index 0) should be detected as LP-redundant and removed.
    assert_eq!(
        reduced.report.redundant_places,
        vec![PlaceIdx(0)],
        "p_cap should be the only redundant place"
    );

    // Reduced net should have 2 places: p_use, p_res.
    assert_eq!(reduced.net.num_places(), 2);
    assert_eq!(reduced.net.places[0].id, "p_use");
    assert_eq!(reduced.net.places[1].id, "p_res");

    // p_cap should NOT be in constant_values (it's not constant).
    assert!(
        reduced.constant_values.is_empty(),
        "redundant places should not have constant values"
    );

    // Transitions should only reference the 2 surviving places.
    assert_eq!(reduced.net.num_transitions(), 2);
    for t in &reduced.net.transitions {
        for input_arc in &t.inputs {
            assert!(input_arc.place.0 < 2, "arc references removed place");
        }
        for output_arc in &t.outputs {
            assert!(output_arc.place.0 < 2, "arc references removed place");
        }
    }
}

#[test]
fn test_redundant_place_marking_expansion() {
    let net = make_redundant_capacity_net();
    let reduced = reduce(&net);

    // Initial marking expansion: reduced [0, 3] → full [5, 0, 3]
    // p_cap = 5 - p_use (from invariant p_cap + p_use = 5)
    let expanded = reduced
        .expand_marking(&reduced.net.initial_marking)
        .expect("marking expansion should succeed");
    assert_eq!(expanded, vec![5, 0, 3], "initial marking expansion");

    // After one t_use: reduced [1, 2] → full [4, 1, 2]
    // p_cap = 5 - 1 = 4
    let marking_after_use = reduced
        .net
        .fire(&reduced.net.initial_marking, TransitionIdx(0));
    assert_eq!(marking_after_use, vec![1, 2]);
    let expanded = reduced
        .expand_marking(&marking_after_use)
        .expect("marking expansion should succeed");
    assert_eq!(expanded, vec![4, 1, 2], "marking after one t_use");

    // After two t_use: reduced [2, 1] → full [3, 2, 1]
    let marking_after_2 = reduced.net.fire(&marking_after_use, TransitionIdx(0));
    assert_eq!(marking_after_2, vec![2, 1]);
    let expanded = reduced
        .expand_marking(&marking_after_2)
        .expect("marking expansion should succeed");
    assert_eq!(expanded, vec![3, 2, 1], "marking after two t_use");

    // After three t_use: reduced [3, 0] → full [2, 3, 0]
    let marking_after_3 = reduced.net.fire(&marking_after_2, TransitionIdx(0));
    assert_eq!(marking_after_3, vec![3, 0]);
    let expanded = reduced
        .expand_marking(&marking_after_3)
        .expect("marking expansion should succeed");
    assert_eq!(expanded, vec![2, 3, 0], "marking after three t_use");

    // Release from [1, 2]: reduced → [0, 3] → full [5, 0, 3]
    let marking_released = reduced.net.fire(&marking_after_use, TransitionIdx(1));
    assert_eq!(marking_released, vec![0, 3]);
    let expanded = reduced
        .expand_marking(&marking_released)
        .expect("marking expansion should succeed");
    assert_eq!(expanded, vec![5, 0, 3], "marking back to initial");
}

#[test]
fn test_no_redundant_places_in_simple_mutex() {
    // Mutex: p_free(1) ↔ p_cs(0). Invariant: p_free + p_cs = 1.
    // Neither place is LP-redundant (each constrains its respective transition).
    let net = PetriNet {
        name: None,
        places: vec![place("p_free"), place("p_cs")],
        transitions: vec![
            trans("t_enter", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_exit", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    let reduced = reduce(&net);

    assert!(
        reduced.report.redundant_places.is_empty(),
        "mutex places should not be redundant"
    );
    assert_eq!(reduced.net.num_places(), 2);
    assert!(!reduced.report.has_reductions());
}

#[test]
fn test_redundant_place_iterative_with_constant() {
    // Combine constant place removal with redundant place removal.
    // p_const(7): self-loop on both transitions (constant).
    // p_cap(5), p_use(0), p_res(3): redundant capacity pattern.
    //
    // Pass 1: p_const detected as constant, p_cap as LP-redundant.
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_const"),
            place("p_cap"),
            place("p_use"),
            place("p_res"),
        ],
        transitions: vec![
            trans(
                "t_use",
                vec![arc(0, 1), arc(1, 1), arc(3, 1)],
                vec![arc(0, 1), arc(2, 1)],
            ),
            trans(
                "t_release",
                vec![arc(0, 1), arc(2, 1)],
                vec![arc(0, 1), arc(1, 1), arc(3, 1)],
            ),
        ],
        initial_marking: vec![7, 5, 0, 3],
    };

    let reduced = reduce_iterative(&net).expect("reduction should succeed");

    // p_const removed (constant), p_cap removed (redundant).
    assert_eq!(reduced.net.num_places(), 2);
    assert_eq!(reduced.net.places[0].id, "p_use");
    assert_eq!(reduced.net.places[1].id, "p_res");

    // Verify marking expansion reconstructs both removed places.
    let expanded = reduced
        .expand_marking(&reduced.net.initial_marking)
        .expect("marking expansion should succeed");
    assert_eq!(expanded, vec![7, 5, 0, 3]);
}

#[test]
fn test_redundant_place_reconstruction_buf_reuse() {
    let net = make_redundant_capacity_net();
    let reduced = reduce(&net);

    let mut buf = Vec::new();

    // First call: reduced [0, 3] → full [5, 0, 3]
    reduced
        .expand_marking_into(&[0, 3], &mut buf)
        .expect("marking expansion should succeed");
    assert_eq!(buf, vec![5, 0, 3]);

    // Second call reuses buffer: reduced [1, 2] → full [4, 1, 2]
    reduced
        .expand_marking_into(&[1, 2], &mut buf)
        .expect("marking expansion should succeed");
    assert_eq!(buf, vec![4, 1, 2]);
}

#[test]
fn test_redundant_place_not_in_constant_values() {
    // Verify redundant places are excluded from constant_values
    // (their values vary by marking, not fixed).
    let net = make_redundant_capacity_net();
    let reduced = reduce(&net);

    for (place, _) in &reduced.constant_values {
        assert_ne!(*place, PlaceIdx(0), "p_cap is redundant, not constant");
    }
}

#[test]
fn test_debug_invariants_for_redundant_net() {
    let net = make_redundant_capacity_net();
    let invariants = compute_p_invariants(&net);
    eprintln!("=== P-invariants ===");
    for (i, inv) in invariants.iter().enumerate() {
        eprintln!(
            "  Inv {i}: weights={:?}, token_count={}",
            inv.weights, inv.token_count
        );
    }
    let implied = find_implied_places(&invariants);
    eprintln!("=== Implied places ===");
    for ip in &implied {
        eprintln!(
            "  Place {}: constant={}, divisor={}, terms={:?}",
            ip.place,
            ip.reconstruction.constant,
            ip.reconstruction.divisor,
            ip.reconstruction.terms
        );
    }
    assert!(!invariants.is_empty(), "should find P-invariants");
    assert!(!implied.is_empty(), "should find implied places");
}
