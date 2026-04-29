// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_t_semiflow_liveness_cycle_returns_none() {
    // Cycle net: all transitions covered by T-semiflows -> None.
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };
    assert_eq!(structural_not_live_t_semiflows(&net), None);
}

#[test]
fn test_t_semiflow_liveness_linear_bounded_returns_false() {
    // Linear net: p0(1) -> t0 -> p1. t0 uncovered, net is bounded
    // (P-invariant covers both places) -> Some(false).
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![1, 0],
    };
    assert_eq!(structural_not_live_t_semiflows(&net), Some(false));
}

#[test]
fn test_t_semiflow_liveness_non_free_choice_bounded() {
    // Non-free-choice dining philosophers: all transitions are in
    // repeatable cycles (pickup/putdown), so T-semiflows cover them.
    let net = PetriNet {
        name: None,
        places: vec![
            place("phil1_think"),
            place("phil2_think"),
            place("fork1"),
            place("fork2"),
            place("phil1_eat"),
            place("phil2_eat"),
        ],
        transitions: vec![
            trans(
                "phil1_pickup",
                vec![arc(0, 1), arc(2, 1), arc(3, 1)],
                vec![arc(4, 1)],
            ),
            trans(
                "phil1_putdown",
                vec![arc(4, 1)],
                vec![arc(0, 1), arc(2, 1), arc(3, 1)],
            ),
            trans(
                "phil2_pickup",
                vec![arc(1, 1), arc(2, 1), arc(3, 1)],
                vec![arc(5, 1)],
            ),
            trans(
                "phil2_putdown",
                vec![arc(5, 1)],
                vec![arc(1, 1), arc(2, 1), arc(3, 1)],
            ),
        ],
        initial_marking: vec![1, 1, 1, 1, 0, 0],
    };
    // structural_live returns None (non-free-choice), but T-semiflow
    // check also returns None (all transitions covered).
    assert_eq!(structural_not_live_t_semiflows(&net), None);
}

#[test]
fn test_t_semiflow_liveness_mixed_net() {
    // p0(1) -> t0 -> p1, p1 -> t1 -> p2, p2 -> t2 -> p1.
    // t1+t2 form a cycle (covered). t0 is linear (uncovered).
    // Net is bounded (P-invariants exist).
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t2", vec![arc(2, 1)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![1, 0, 0],
    };
    assert_eq!(structural_not_live_t_semiflows(&net), Some(false));
}
