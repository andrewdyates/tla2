// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::fixtures::{simple_linear_net, two_component_net, CountingObserver};
use super::*;
use crate::invariant::compute_p_invariants;
use crate::marking::{determine_width, determine_width_with_invariants, TokenWidth};
use crate::reduction::reduce_iterative;

#[test]
fn test_invariant_aware_width_tighter_than_conservation() {
    let net = two_component_net();

    let base_width = determine_width(&net);
    assert_eq!(base_width, TokenWidth::U16);

    let invariants = compute_p_invariants(&net);
    let inv_width = determine_width_with_invariants(&net, &invariants);
    assert_eq!(inv_width, TokenWidth::U8);

    let config = ExplorationConfig::new(1000);
    let mut observer = CountingObserver::new();
    let result = explore(&net, &config, &mut observer);

    assert!(result.completed);
    assert_eq!(result.states_visited, 4);
    assert_eq!(observer.deadlocks, 0);
}

#[test]
fn test_invariant_aware_auto_sizing_more_states() {
    let net = two_component_net();
    let info = ExplorationConfig::describe_auto(&net, Some(0.01));

    assert_eq!(info.bytes_per_place, 1);
    assert_eq!(info.num_places, 4);
    assert_eq!(info.packed_places, 2);
}

#[test]
fn test_auto_sized_accounts_for_implied_places() {
    let net = two_component_net();
    let info = ExplorationConfig::describe_auto(&net, Some(0.01));

    assert_eq!(info.num_places, 4);
    assert_eq!(info.packed_places, 2);
    let bytes_per_state = info.packed_places * info.bytes_per_place + 48;
    assert_eq!(bytes_per_state, 50);
    assert!(info.max_states >= 1, "should compute at least 1 state");
}

#[test]
fn test_refitted_for_net_increases_max_states_after_reduction() {
    let net = PetriNet {
        name: Some("refitting".into()),
        places: (0..20)
            .map(|i| PlaceInfo {
                id: format!("P{i}"),
                name: None,
            })
            .collect(),
        transitions: vec![TransitionInfo {
            id: "T0".into(),
            name: None,
            inputs: vec![
                Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                },
                Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                },
            ],
            outputs: vec![
                Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                },
                Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                },
            ],
        }],
        initial_marking: vec![5; 20],
    };

    let config =
        ExplorationConfig::auto_sized(&net, None, Some(0.01)).with_fingerprint_dedup(false);
    let original_max = config.max_states();

    let reduced = reduce_iterative(&net).expect("reduction should succeed");
    assert!(
        reduced.net.num_places() < net.num_places(),
        "reduction should remove places: {} < {}",
        reduced.net.num_places(),
        net.num_places(),
    );

    let refitted = config.refitted_for_net(&reduced.net);
    assert!(
        refitted.max_states() > original_max,
        "refitted max_states ({}) should exceed original ({}) \
         because reduced net has fewer places ({} vs {})",
        refitted.max_states(),
        original_max,
        reduced.net.num_places(),
        net.num_places(),
    );
}

#[test]
fn test_refitted_for_net_noop_with_fingerprint_dedup() {
    let net = PetriNet {
        name: Some("fp-refit".into()),
        places: (0..20)
            .map(|i| PlaceInfo {
                id: format!("P{i}"),
                name: None,
            })
            .collect(),
        transitions: vec![TransitionInfo {
            id: "T0".into(),
            name: None,
            inputs: vec![
                Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                },
                Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                },
            ],
            outputs: vec![
                Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                },
                Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                },
            ],
        }],
        initial_marking: vec![5; 20],
    };

    let config = ExplorationConfig::auto_sized(&net, None, Some(0.01));
    assert!(
        config.fingerprint_dedup(),
        "default should be fingerprint on"
    );
    let original_max = config.max_states();

    let reduced = reduce_iterative(&net).expect("reduction should succeed");
    let refitted = config.refitted_for_net(&reduced.net);
    assert_eq!(
        refitted.max_states(),
        original_max,
        "with fingerprint dedup, refitting should not change max_states \
         (32 bytes/state regardless of place count)"
    );
}

#[test]
fn test_refitted_for_net_noop_on_explicit_config() {
    let net = simple_linear_net();
    let config = ExplorationConfig::new(42);
    let refitted = config.refitted_for_net(&net);
    assert_eq!(refitted.max_states(), 42);
}

#[test]
fn test_refitted_for_full_graph_tightens_auto_sized_budget() {
    let net = PetriNet {
        name: Some("full-graph-refit".into()),
        places: (0..200)
            .map(|i| PlaceInfo {
                id: format!("P{i}"),
                name: None,
            })
            .collect(),
        transitions: vec![TransitionInfo {
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
        }],
        initial_marking: vec![1; 200],
    };

    let config = ExplorationConfig::auto_sized(&net, None, Some(0.01));
    let refitted = config.refitted_for_full_graph(&net);
    assert!(
        refitted.max_states() < config.max_states(),
        "full-graph refit should tighten the auto-sized budget: {} < {}",
        refitted.max_states(),
        config.max_states(),
    );
}

#[test]
fn test_refitted_for_full_graph_noop_on_explicit_config() {
    let net = simple_linear_net();
    let config = ExplorationConfig::new(42);
    let refitted = config.refitted_for_full_graph(&net);
    assert_eq!(refitted.max_states(), 42);
}
