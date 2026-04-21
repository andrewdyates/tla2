// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::fixtures::{ring_net_3, two_component_net, CountingObserver};
use super::*;
use crate::invariant::{compute_p_invariants, find_implied_places};

#[test]
fn test_explore_implied_place_verdict_parity() {
    let net = two_component_net();
    let config = ExplorationConfig::new(1000);
    let mut observer = CountingObserver::new();
    let result = explore(&net, &config, &mut observer);

    assert!(result.completed);
    assert_eq!(result.states_visited, 4);
    assert_eq!(observer.deadlocks, 0);
}

#[test]
fn test_explore_full_implied_places_correct_markings() {
    let net = two_component_net();
    let config = ExplorationConfig::new(1000);
    let full = explore_full(&net, &config);

    assert!(full.graph.completed);
    assert_eq!(full.graph.num_states, 4);
    assert_eq!(full.markings.len(), 4);

    for m in &full.markings {
        assert_eq!(m[0] + m[1], 200, "invariant [1,1,0,0] violated: {m:?}");
        assert_eq!(m[2] + m[3], 200, "invariant [0,0,1,1] violated: {m:?}");
    }

    let mut sorted: Vec<Vec<u64>> = full.markings.clone();
    sorted.sort();
    assert_eq!(
        sorted,
        vec![
            vec![0, 200, 0, 200],
            vec![0, 200, 200, 0],
            vec![200, 0, 0, 200],
            vec![200, 0, 200, 0],
        ]
    );
}

#[test]
fn test_explore_ring_net_implied_place_parity() {
    let net = ring_net_3();

    let invariants = compute_p_invariants(&net);
    let implied = find_implied_places(&invariants);
    assert!(
        !implied.is_empty(),
        "ring net should have at least one implied place"
    );

    let config = ExplorationConfig::new(1000);
    let mut observer = CountingObserver::new();
    let result = explore(&net, &config, &mut observer);

    assert!(result.completed);
    assert_eq!(result.states_visited, 3);
    assert_eq!(observer.deadlocks, 0);
}

#[test]
fn test_explore_full_ring_net_markings_exact() {
    let net = ring_net_3();
    let config = ExplorationConfig::new(1000);
    let full = explore_full(&net, &config);

    assert!(full.graph.completed);
    assert_eq!(full.markings.len(), 3);

    for m in &full.markings {
        assert_eq!(m[0] + m[1] + m[2], 1, "invariant violated: {m:?}");
    }

    let mut sorted: Vec<Vec<u64>> = full.markings.clone();
    sorted.sort();
    assert_eq!(sorted, vec![vec![0, 0, 1], vec![0, 1, 0], vec![1, 0, 0]]);
}
