// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests verifying that diff-based BFS produces identical state
//! counts and observer callbacks as the full-materialization BFS path.

use super::fixtures::{
    counting_net, cyclic_net, deadlock_net, ring_net_3, simple_linear_net, two_component_net,
    two_independent_deadlocking_processes, CountingObserver,
};
use super::*;

/// Run both standard and diff-based BFS on the same net and assert that
/// state counts, deadlock counts, and completion status match.
fn assert_diff_matches_standard(net: &PetriNet, label: &str) {
    let config_std = ExplorationConfig::default();
    let config_diff = ExplorationConfig::default().with_diff_successors(true);

    let mut obs_std = CountingObserver::new();
    let mut obs_diff = CountingObserver::new();

    let result_std = explore(&net, &config_std, &mut obs_std);
    let result_diff = explore_observer(&net, &config_diff, &mut obs_diff);

    assert_eq!(
        result_std.states_visited, result_diff.states_visited,
        "{label}: state count mismatch (standard={}, diff={})",
        result_std.states_visited, result_diff.states_visited,
    );
    assert_eq!(
        obs_std.states, obs_diff.states,
        "{label}: observer state count mismatch (standard={}, diff={})",
        obs_std.states, obs_diff.states,
    );
    assert_eq!(
        obs_std.deadlocks, obs_diff.deadlocks,
        "{label}: deadlock count mismatch (standard={}, diff={})",
        obs_std.deadlocks, obs_diff.deadlocks,
    );
    assert_eq!(
        result_std.completed, result_diff.completed,
        "{label}: completed mismatch (standard={}, diff={})",
        result_std.completed, result_diff.completed,
    );
}

#[test]
fn test_diff_bfs_linear_net_matches_standard() {
    assert_diff_matches_standard(&simple_linear_net(), "linear");
}

#[test]
fn test_diff_bfs_cyclic_net_matches_standard() {
    assert_diff_matches_standard(&cyclic_net(), "cyclic");
}

#[test]
fn test_diff_bfs_deadlock_net_matches_standard() {
    assert_diff_matches_standard(&deadlock_net(), "deadlock");
}

#[test]
fn test_diff_bfs_counting_net_5_matches_standard() {
    assert_diff_matches_standard(&counting_net(5), "counting_5");
}

#[test]
fn test_diff_bfs_counting_net_20_matches_standard() {
    assert_diff_matches_standard(&counting_net(20), "counting_20");
}

#[test]
fn test_diff_bfs_two_independent_matches_standard() {
    assert_diff_matches_standard(&two_independent_deadlocking_processes(), "two_independent");
}

#[test]
fn test_diff_bfs_two_component_net_matches_standard() {
    assert_diff_matches_standard(&two_component_net(), "two_component");
}

#[test]
fn test_diff_bfs_ring3_matches_standard() {
    assert_diff_matches_standard(&ring_net_3(), "ring3");
}

#[test]
fn test_diff_bfs_state_limit_matches_standard() {
    let net = counting_net(100);
    let config_std = ExplorationConfig::new(10);
    let config_diff = ExplorationConfig::new(10).with_diff_successors(true);

    let mut obs_std = CountingObserver::new();
    let mut obs_diff = CountingObserver::new();

    let result_std = explore(&net, &config_std, &mut obs_std);
    let result_diff = crate::explorer::diff_bfs::explore_diff(&net, &config_diff, &mut obs_diff);

    assert_eq!(
        result_std.completed, result_diff.completed,
        "state_limit: completed mismatch"
    );
    assert!(
        !result_std.completed,
        "state_limit: should not complete with limit=10"
    );
    // Both should be capped at approximately the same count.
    assert!(
        (result_std.states_visited as i64 - result_diff.states_visited as i64).unsigned_abs() <= 1,
        "state_limit: state count divergence (standard={}, diff={})",
        result_std.states_visited,
        result_diff.states_visited,
    );
}

#[test]
fn test_diff_bfs_config_getter() {
    let config = ExplorationConfig::default();
    assert!(!config.diff_successors(), "should default to false");

    let config = config.with_diff_successors(true);
    assert!(config.diff_successors(), "should be true after enabling");

    let config = config.with_diff_successors(false);
    assert!(!config.diff_successors(), "should be false after disabling");
}

/// Larger net: producer-consumer with buffer. Tests that diff BFS handles
/// nets with more complex transition structure.
#[test]
fn test_diff_bfs_producer_consumer_matches_standard() {
    // P0: producer ready, P1: buffer, P2: consumer ready, P3: consumed
    // T0: produce (P0 -> P1), T1: consume (P1 + P2 -> P3)
    let net = PetriNet {
        name: Some("producer_consumer".into()),
        places: vec![
            PlaceInfo {
                id: "ready".into(),
                name: None,
            },
            PlaceInfo {
                id: "buffer".into(),
                name: None,
            },
            PlaceInfo {
                id: "consumer".into(),
                name: None,
            },
            PlaceInfo {
                id: "consumed".into(),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "produce".into(),
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
                id: "consume".into(),
                name: None,
                inputs: vec![
                    Arc {
                        place: PlaceIdx(1),
                        weight: 1,
                    },
                    Arc {
                        place: PlaceIdx(2),
                        weight: 1,
                    },
                ],
                outputs: vec![Arc {
                    place: PlaceIdx(3),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![3, 0, 2, 0],
    };
    assert_diff_matches_standard(&net, "producer_consumer");
}

/// Self-loop net: transition reads and writes back to the same place.
/// Tests that zero-delta places are correctly excluded from diffs.
#[test]
fn test_diff_bfs_self_loop_matches_standard() {
    let net = PetriNet {
        name: Some("self_loop".into()),
        places: vec![
            PlaceInfo {
                id: "P0".into(),
                name: None,
            },
            PlaceInfo {
                id: "P1".into(),
                name: None,
            },
        ],
        transitions: vec![TransitionInfo {
            id: "T0".into(),
            name: None,
            inputs: vec![Arc {
                place: PlaceIdx(0),
                weight: 1,
            }],
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
        initial_marking: vec![1, 0],
    };
    assert_diff_matches_standard(&net, "self_loop");
}
