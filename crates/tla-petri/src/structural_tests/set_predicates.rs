// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_is_trap_basic() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };
    // {p0, p1} is a trap: t0 consumes from p0 and produces into p1 (in set),
    // t1 consumes from p1 and produces into p0 (in set).
    assert!(is_trap(&net, &[true, true]));
    // {p0} alone is NOT a trap: t0 consumes from p0 but produces into p1.
    assert!(!is_trap(&net, &[true, false]));
}

#[test]
fn test_is_siphon_basic() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };
    // {p0, p1} is a siphon
    assert!(is_siphon(&net, &[true, true]));
    // {p0}: t0 consumes from p0. Is there a transition that produces
    // into {p0}? t1 produces into p0, and t1 consumes from p1 which
    // is NOT in {p0}. So siphon condition: for all t: t* intersect S != empty -> *t intersect S != empty.
    // t1: t1* intersect {p0} = {p0} != empty, *t1 intersect {p0} = empty. Condition violated.
    assert!(!is_siphon(&net, &[true, false]));
}
