// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::fixtures::{cyclic_net, two_component_net};
use super::*;

#[test]
fn test_explore_and_build_graph_deduplicates_cyclic_successors() {
    let graph = explore_and_build_graph(&cyclic_net(), &ExplorationConfig::default());

    assert!(graph.completed);
    assert_eq!(graph.num_states, 2);
    assert_eq!(graph.adj, vec![vec![(1, 0)], vec![(0, 1)]]);
}

#[test]
fn test_explore_and_build_graph_exact_budget_still_completes() {
    let graph = explore_and_build_graph(&cyclic_net(), &ExplorationConfig::new(2));

    assert!(graph.completed);
    assert_eq!(graph.num_states, 2);
    assert_eq!(graph.adj, vec![vec![(1, 0)], vec![(0, 1)]]);
}

#[test]
fn test_explore_full_deduplicates_cyclic_markings() {
    let full = explore_full(&cyclic_net(), &ExplorationConfig::default());

    assert!(full.graph.completed);
    assert_eq!(full.graph.num_states, 2);
    assert_eq!(full.markings, vec![vec![1, 0], vec![0, 1]]);
    assert_eq!(full.graph.adj, vec![vec![(1, 0)], vec![(0, 1)]]);
}

#[test]
fn test_explore_full_exact_budget_still_completes() {
    let full = explore_full(&cyclic_net(), &ExplorationConfig::new(2));

    assert!(full.graph.completed);
    assert_eq!(full.graph.num_states, 2);
    assert_eq!(full.markings, vec![vec![1, 0], vec![0, 1]]);
    assert_eq!(full.graph.adj, vec![vec![(1, 0)], vec![(0, 1)]]);
}

#[test]
fn test_explore_and_build_graph_implied_places_same_structure() {
    let net = two_component_net();
    let config = ExplorationConfig::new(1000);
    let graph = explore_and_build_graph(&net, &config);

    assert!(graph.completed);
    assert_eq!(graph.num_states, 4);

    for edges in &graph.adj {
        assert!(!edges.is_empty(), "deadlock found in cyclic net");
    }
}
