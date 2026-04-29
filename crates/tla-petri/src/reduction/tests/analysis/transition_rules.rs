// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::petri_net::{PetriNet, TransitionIdx};
use crate::reduction::analyze;

use super::super::support::{arc, place, trans};

#[test]
fn test_duplicate_transition_class_detected() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_back", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    let report = analyze(&net);
    assert!(report.dead_transitions.is_empty());
    assert_eq!(report.duplicate_transitions.len(), 1);
    assert_eq!(report.duplicate_transitions[0].canonical, TransitionIdx(0));
    assert_eq!(
        report.duplicate_transitions[0].duplicates,
        vec![TransitionIdx(1)]
    );
    assert_eq!(report.transitions_removed(), 1);
}

#[test]
fn test_non_duplicate_weight_difference_not_removed() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(0, 1)], vec![arc(1, 2)]),
            trans("t_back", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![2, 1],
    };

    let report = analyze(&net);
    assert!(report.duplicate_transitions.is_empty());
}

#[test]
fn test_dead_duplicate_not_reported_as_duplicate_class() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(0, 1)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![0, 0],
    };

    let report = analyze(&net);
    assert_eq!(
        report.dead_transitions,
        vec![TransitionIdx(0), TransitionIdx(1)]
    );
    assert!(report.duplicate_transitions.is_empty());
}

// ---------------------------------------------------------------------------
// Self-loop transition detection
// ---------------------------------------------------------------------------

#[test]
fn test_self_loop_single_place() {
    // t0: p0 ->(1) t0 ->(1) p0 (self-loop, no net effect)
    // t1: p0 ->(1) t1 ->(1) p1 (real transition)
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t_loop", vec![arc(0, 1)], vec![arc(0, 1)]),
            trans("t_real", vec![arc(0, 1)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![5, 0],
    };

    let report = analyze(&net);
    assert_eq!(report.self_loop_transitions, vec![TransitionIdx(0)]);
}

#[test]
fn test_self_loop_multi_place() {
    // t0 consumes [p0:2, p1:3] and produces [p0:2, p1:3] -> zero net effect.
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans(
                "t_loop",
                vec![arc(0, 2), arc(1, 3)],
                vec![arc(0, 2), arc(1, 3)],
            ),
            trans("t_real", vec![arc(0, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![5, 5, 0],
    };

    let report = analyze(&net);
    assert_eq!(report.self_loop_transitions, vec![TransitionIdx(0)]);
}

#[test]
fn test_not_self_loop_asymmetric() {
    // t0 consumes 2 from p0, produces 1 to p0 and 1 to p1 -> net effect nonzero.
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t_asym", vec![arc(0, 2)], vec![arc(0, 1), arc(1, 1)])],
        initial_marking: vec![5, 0],
    };

    let report = analyze(&net);
    assert!(report.self_loop_transitions.is_empty());
}

#[test]
fn test_self_loop_dead_excluded() {
    // t_dead_loop self-loops on p0, but also reads from p_blocker which has
    // no producer and zero initial tokens -> dead. Not a self-loop transition
    // anyway (net effect nonzero: consumes from p_blocker without producing).
    // t_real_loop is a self-loop and alive.
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p_blocker"), place("p2")],
        transitions: vec![
            trans(
                "t_dead_notloop",
                vec![arc(0, 1), arc(1, 1)],
                vec![arc(0, 1)],
            ),
            trans("t_real_loop", vec![arc(2, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![5, 0, 5],
    };

    let report = analyze(&net);
    assert_eq!(report.dead_transitions, vec![TransitionIdx(0)]);
    assert!(
        report.self_loop_transitions.is_empty()
            || !report.self_loop_transitions.contains(&TransitionIdx(0)),
        "dead transition should not appear in self_loop_transitions"
    );
    // t_real_loop is alive and has zero net effect -> self-loop
    assert_eq!(report.self_loop_transitions, vec![TransitionIdx(1)]);
}
