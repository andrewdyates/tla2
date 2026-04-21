// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::error::PnmlError;
use crate::petri_net::{PetriNet, TransitionIdx};
use crate::reduction::{apply_query_guarded_prefire, ReducedNet};

use super::super::support::{arc, place, trans};

#[test]
fn test_query_guarded_prefire_fires_transition_maximally_without_removing_it() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 2)], vec![arc(1, 1)])],
        initial_marking: vec![5, 0],
    };

    let mut reduced = ReducedNet::identity(&net);
    let changed =
        apply_query_guarded_prefire(&mut reduced, &[false, false]).expect("prefire should succeed");

    assert!(changed);
    assert_eq!(reduced.net.initial_marking, vec![1, 2]);
    assert_eq!(reduced.net.num_transitions(), 1);
    assert_eq!(reduced.transition_map, vec![Some(TransitionIdx(0))]);
}

#[test]
fn test_query_guarded_prefire_skips_protected_places() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![3, 0],
    };

    let mut reduced = ReducedNet::identity(&net);
    let changed =
        apply_query_guarded_prefire(&mut reduced, &[true, false]).expect("prefire should succeed");

    assert!(!changed);
    assert_eq!(reduced.net.initial_marking, vec![3, 0]);
}

#[test]
fn test_query_guarded_prefire_skips_overlapping_preset_and_postset() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(0, 1)])],
        initial_marking: vec![3],
    };

    let mut reduced = ReducedNet::identity(&net);
    let changed =
        apply_query_guarded_prefire(&mut reduced, &[false]).expect("prefire should succeed");

    assert!(!changed);
    assert_eq!(reduced.net.initial_marking, vec![3]);
}

#[test]
fn test_prefire_returns_error_on_output_overflow() {
    // t0: p0→(1) t0 →(u64::MAX) p1. With p0=2, prefire fires twice,
    // producing 2 * u64::MAX which overflows checked_mul.
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, u64::MAX)])],
        initial_marking: vec![2, 0],
    };

    let mut reduced = ReducedNet::identity(&net);
    let error = apply_query_guarded_prefire(&mut reduced, &[false, false])
        .expect_err("prefire output overflow should fail closed");
    assert!(matches!(
        error,
        PnmlError::ReductionOverflow { ref context }
            if context.contains("prefire")
    ));
}

#[test]
fn test_prefire_returns_error_on_marking_add_overflow() {
    // t0: p0→(1) t0 →(1) p1. With p0=1, p1=u64::MAX, prefire fires once,
    // adding 1 to p1=u64::MAX which overflows checked_add.
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![1, u64::MAX],
    };

    let mut reduced = ReducedNet::identity(&net);
    let error = apply_query_guarded_prefire(&mut reduced, &[false, false])
        .expect_err("prefire marking overflow should fail closed");
    assert!(matches!(
        error,
        PnmlError::ReductionOverflow { ref context }
            if context.contains("prefire")
    ));
}
