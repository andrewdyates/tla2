// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::examinations::quasi_liveness::QuasiLivenessObserver;
use crate::explorer::{explore, explore_observer};
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};

use super::fixtures::{
    cyclic_safe_net, default_config, immediate_deadlock_net, linear_deadlock_net,
};

#[test]
fn test_quasi_liveness_cyclic_net_all_fire() {
    let net = cyclic_safe_net();
    let config = default_config();
    let mut observer = QuasiLivenessObserver::new(net.num_transitions());
    let result = explore(&net, &config, &mut observer);

    assert!(observer.all_fired());
    assert!(result.completed || result.stopped_by_observer);
}

#[test]
fn test_quasi_liveness_linear_net_single_transition() {
    let net = linear_deadlock_net();
    let config = default_config();
    let mut observer = QuasiLivenessObserver::new(net.num_transitions());
    let result = explore(&net, &config, &mut observer);

    assert!(observer.all_fired());
    assert!(result.stopped_by_observer);
}

#[test]
fn test_quasi_liveness_no_transitions_vacuous_true() {
    let net = immediate_deadlock_net();
    let config = default_config();
    let mut observer = QuasiLivenessObserver::new(net.num_transitions());
    let _result = explore(&net, &config, &mut observer);

    assert!(observer.all_fired());
}

#[test]
fn test_quasi_liveness_unreachable_transition_false() {
    let net = PetriNet {
        name: Some("unreachable-trans".into()),
        places: vec![
            PlaceInfo {
                id: "P0".into(),
                name: None,
            },
            PlaceInfo {
                id: "P1".into(),
                name: None,
            },
            PlaceInfo {
                id: "P2".into(),
                name: None,
            },
            PlaceInfo {
                id: "P3".into(),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "T0".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "T1".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(3),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![1, 0, 0, 0],
    };
    let config = default_config();
    let mut observer = QuasiLivenessObserver::new(net.num_transitions());
    let result = explore(&net, &config, &mut observer);

    assert!(!observer.all_fired());
    assert!(result.completed);
}

#[test]
fn test_quasi_liveness_parallel_matches_sequential_result() {
    let net = cyclic_safe_net();
    let sequential_config = default_config();
    let mut sequential = QuasiLivenessObserver::new(net.num_transitions());
    let sequential_result = explore_observer(&net, &sequential_config, &mut sequential);

    let parallel_config = default_config().with_workers(4);
    let mut parallel = QuasiLivenessObserver::new(net.num_transitions());
    let parallel_result = explore_observer(&net, &parallel_config, &mut parallel);

    assert_eq!(parallel.all_fired(), sequential.all_fired());
    assert_eq!(parallel_result.completed, sequential_result.completed);
}
