// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_structural_live_free_choice_cycle() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    assert_eq!(structural_live(&net), Some(true));
}

#[test]
fn test_structural_live_reports_uncovered_siphon_on_linear_net() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![1, 0],
    };

    assert_eq!(structural_live(&net), Some(false));
}

#[test]
fn test_structural_live_rejects_non_free_choice_net() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(2, 1)]),
            trans("t1", vec![arc(0, 1), arc(1, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![1, 1, 0, 0],
    };

    assert_eq!(structural_live(&net), None);
}

#[test]
fn test_structural_live_rejects_weighted_net() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 2)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 2)]),
        ],
        initial_marking: vec![2, 0],
    };

    assert_eq!(structural_live(&net), None);
}
