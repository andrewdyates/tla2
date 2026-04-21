// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core UpperBounds tests: observer basics, fail-closed, ordering, parallel parity.

use crate::explorer::{ExplorationConfig, ExplorationObserver};
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
use crate::property_xml::{Formula, Property};

use super::super::model::BoundTracker;
use super::super::observer::UpperBoundsObserver;
use super::super::pipeline::check_upper_bounds_properties;
use super::fixtures::*;

#[test]
fn test_upper_bounds_single_place() {
    let mut obs = single_tracker_observer("test-UpperBounds-00", vec![PlaceIdx(0)]);

    // Simulate markings: [3,0], [2,1], [1,2], [0,3]
    obs.on_new_state(&[3, 0]);
    obs.on_new_state(&[2, 1]);
    obs.on_new_state(&[1, 2]);
    obs.on_new_state(&[0, 3]);

    let trackers = obs.into_trackers();
    assert_eq!(trackers.len(), 1);
    assert_eq!(trackers[0].id, "test-UpperBounds-00");
    assert_eq!(trackers[0].max_bound, 3);
}

#[test]
fn test_upper_bounds_multi_place_sum() {
    let mut obs = single_tracker_observer("test-UpperBounds-00", vec![PlaceIdx(0), PlaceIdx(1)]);

    // Sum of p0+p1 is always 3 in this conserving net
    obs.on_new_state(&[3, 0]);
    obs.on_new_state(&[2, 1]);
    obs.on_new_state(&[0, 3]);

    let trackers = obs.into_trackers();
    assert_eq!(trackers[0].max_bound, 3);
}

#[test]
fn test_check_upper_bounds_unresolved_place_returns_cannot_compute() {
    let net = simple_net();
    let props = vec![Property {
        id: "test-UpperBounds-00".to_string(),
        formula: Formula::PlaceBound(vec!["nonexistent".to_string()]),
    }];

    let results = check_upper_bounds_properties(&net, &props, &default_config());
    assert_eq!(results, vec![(String::from("test-UpperBounds-00"), None)]);
}

#[test]
fn test_check_upper_bounds_preserves_order_for_mixed_validity() {
    let net = simple_net();
    let props = vec![
        Property {
            id: "test-UpperBounds-00".to_string(),
            formula: Formula::PlaceBound(vec!["p0".to_string()]),
        },
        Property {
            id: "test-UpperBounds-01".to_string(),
            formula: Formula::PlaceBound(vec!["missing".to_string()]),
        },
        Property {
            id: "test-UpperBounds-02".to_string(),
            formula: Formula::PlaceBound(vec!["p1".to_string()]),
        },
    ];

    let results = check_upper_bounds_properties(&net, &props, &default_config());
    assert_eq!(
        results,
        vec![
            (String::from("test-UpperBounds-00"), Some(3)),
            (String::from("test-UpperBounds-01"), None),
            (String::from("test-UpperBounds-02"), Some(3)),
        ]
    );
}

#[test]
fn test_check_upper_bounds_parallel_matches_sequential() {
    let net = simple_net();
    let props = vec![
        Property {
            id: "test-UpperBounds-00".to_string(),
            formula: Formula::PlaceBound(vec!["p0".to_string()]),
        },
        Property {
            id: "test-UpperBounds-01".to_string(),
            formula: Formula::PlaceBound(vec!["p1".to_string()]),
        },
    ];

    let sequential = check_upper_bounds_properties(&net, &props, &default_config());
    let parallel = check_upper_bounds_properties(&net, &props, &parallel_config());

    assert_eq!(parallel, sequential);
}

#[test]
fn test_check_upper_bounds_incomplete_exploration_returns_cannot_compute() {
    // Non-conserving net: no P-invariant covers p1, so structural
    // fallback cannot help when exploration is incomplete.
    let net = PetriNet {
        name: Some("non-conserving".to_string()),
        places: vec![
            PlaceInfo {
                id: "p0".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "p1".to_string(),
                name: None,
            },
        ],
        transitions: vec![
            // T0: produces tokens from nothing into p1
            TransitionInfo {
                id: "t0".to_string(),
                name: None,
                inputs: vec![],
                outputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
            },
            // T1: p0 → (sink, to keep p0 interesting)
            TransitionInfo {
                id: "t1".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
                outputs: vec![],
            },
        ],
        initial_marking: vec![3, 0],
    };
    let props = vec![Property {
        id: "test-UpperBounds-00".to_string(),
        formula: Formula::PlaceBound(vec!["p1".to_string()]),
    }];
    let config = ExplorationConfig::new(1);

    let results = check_upper_bounds_properties(&net, &props, &config);
    assert_eq!(results, vec![(String::from("test-UpperBounds-00"), None)]);
}

#[test]
fn test_observer_is_done_with_structural_bounds() {
    let mut obs = UpperBoundsObserver::new(vec![
        BoundTracker {
            id: "b0".to_string(),
            place_indices: vec![PlaceIdx(0)],
            max_bound: 0,
            structural_bound: Some(3),
            lp_bound: None,
        },
        BoundTracker {
            id: "b1".to_string(),
            place_indices: vec![PlaceIdx(1)],
            max_bound: 0,
            structural_bound: Some(3),
            lp_bound: None,
        },
    ]);

    // Not done yet: no bounds reached
    assert!(!obs.is_done());

    // First tracker reaches bound
    obs.on_new_state(&[3, 0]);
    assert!(!obs.is_done());

    // Both trackers reach bound → done
    obs.on_new_state(&[0, 3]);
    assert!(obs.is_done());
}

#[test]
fn test_observer_is_done_without_structural_bounds() {
    let obs = UpperBoundsObserver::new(vec![BoundTracker {
        id: "b0".to_string(),
        place_indices: vec![PlaceIdx(0)],
        max_bound: 0,
        structural_bound: None,
        lp_bound: None,
    }]);

    // Without structural bounds, never done early
    assert!(!obs.is_done());
}
