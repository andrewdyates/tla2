// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::fixtures::{
    counting_net, two_component_net, two_independent_deadlocking_processes, CountingObserver,
};
use super::*;
use crate::stubborn::{compute_stubborn_set, DependencyGraph};

#[test]
fn test_enabled_transitions_into_uses_stubborn_subset_when_por_applies() {
    let net = two_independent_deadlocking_processes();
    let dep_graph = DependencyGraph::build(&net);
    let expected = compute_stubborn_set(
        &net,
        &net.initial_marking,
        &dep_graph,
        &PorStrategy::DeadlockPreserving,
    )
    .expect("POR helper should expose the reduced stubborn subset");
    let mut enabled = vec![TransitionIdx(u32::MAX)];

    enabled_transitions_into(
        &net,
        &net.initial_marking,
        net.num_transitions(),
        Some(&dep_graph),
        &PorStrategy::DeadlockPreserving,
        &mut enabled,
    );

    assert_eq!(enabled, expected);
    assert!(!enabled.is_empty());
    assert!(enabled.len() < net.num_transitions());
}

#[test]
fn test_enabled_transitions_into_falls_back_to_enabled_scan_without_por() {
    let net = two_independent_deadlocking_processes();
    let dep_graph = DependencyGraph::build(&net);
    let mut enabled = vec![TransitionIdx(u32::MAX)];

    enabled_transitions_into(
        &net,
        &net.initial_marking,
        net.num_transitions(),
        Some(&dep_graph),
        &PorStrategy::None,
        &mut enabled,
    );

    assert_eq!(enabled, vec![TransitionIdx(0), TransitionIdx(1)]);
}

#[test]
fn test_enabled_transitions_into_returns_empty_for_deadlock() {
    let net = super::fixtures::deadlock_net();
    let dep_graph = DependencyGraph::build(&net);
    let mut enabled = vec![TransitionIdx(u32::MAX)];

    enabled_transitions_into(
        &net,
        &net.initial_marking,
        net.num_transitions(),
        Some(&dep_graph),
        &PorStrategy::DeadlockPreserving,
        &mut enabled,
    );

    assert!(enabled.is_empty());
}

#[test]
fn test_explore_observer_workers_one_matches_direct_explore() {
    let net = two_component_net();
    let sequential_config = ExplorationConfig::new(1000);
    let mut direct = CountingObserver::new();
    let direct_result = explore(&net, &sequential_config, &mut direct);

    let mut dispatched = CountingObserver::new();
    let dispatched_result = explore_observer(&net, &sequential_config, &mut dispatched);

    assert_eq!(dispatched_result.completed, direct_result.completed);
    assert_eq!(
        dispatched_result.states_visited,
        direct_result.states_visited
    );
    assert_eq!(
        dispatched_result.stopped_by_observer,
        direct_result.stopped_by_observer
    );
    assert_eq!(dispatched.states, direct.states);
    assert_eq!(dispatched.deadlocks, direct.deadlocks);
    assert_eq!(dispatched.firings, direct.firings);
}

#[test]
fn test_analyze_observer_parallelism_small_net_stays_sequential() {
    let net = two_component_net();
    let config = ExplorationConfig::new(1000).with_workers(4);

    let analysis = analyze_observer_parallelism(&net, &config);

    assert_eq!(analysis.sampled_states, 4);
    assert_eq!(analysis.estimated_states, 4);
    assert_eq!(analysis.strategy, Strategy::Sequential);
}

#[test]
fn test_explore_observer_small_net_downshifts_to_sequential() {
    let net = two_component_net();
    let sequential_config = ExplorationConfig::new(1000);
    let mut sequential = CountingObserver::new();
    let sequential_result = explore(&net, &sequential_config, &mut sequential);

    let adaptive_config = ExplorationConfig::new(1000).with_workers(4);
    let mut adaptive = CountingObserver::new();
    let adaptive_result = explore_observer(&net, &adaptive_config, &mut adaptive);

    assert_eq!(adaptive_result.completed, sequential_result.completed);
    assert_eq!(
        adaptive_result.states_visited,
        sequential_result.states_visited
    );
    assert_eq!(adaptive.states, sequential.states);
    assert_eq!(adaptive.deadlocks, sequential.deadlocks);
    assert_eq!(adaptive.firings, sequential.firings);
    assert_eq!(adaptive.merged_summaries, 0);
}

#[test]
fn test_analyze_observer_parallelism_large_net_uses_parallel_cap() {
    let net = counting_net(100);
    let config = ExplorationConfig::new(10_000_000).with_workers(4);

    let analysis = analyze_observer_parallelism(&net, &config);

    assert_eq!(analysis.sampled_states, PILOT_SAMPLE_SIZE);
    assert_eq!(analysis.avg_branching_factor, 1.0);
    assert_eq!(analysis.strategy, Strategy::Parallel(4));
}

#[test]
fn test_analyze_observer_parallelism_respects_state_budget() {
    let net = counting_net(100);
    let config = ExplorationConfig::new(10).with_workers(4);

    let analysis = analyze_observer_parallelism(&net, &config);

    assert_eq!(analysis.sampled_states, 10);
    assert_eq!(analysis.avg_branching_factor, 1.0);
    assert_eq!(analysis.strategy, Strategy::Sequential);
}

#[test]
fn test_explore_observer_large_net_uses_parallel_dispatch_and_preserves_counts() {
    let net = counting_net(100);
    let sequential_config = ExplorationConfig::new(10_000_000);
    let mut sequential = CountingObserver::new();
    let sequential_result = explore(&net, &sequential_config, &mut sequential);

    let adaptive_config = ExplorationConfig::new(10_000_000).with_workers(4);
    let mut adaptive = CountingObserver::new();
    let adaptive_result = explore_observer(&net, &adaptive_config, &mut adaptive);

    assert_eq!(adaptive_result.completed, sequential_result.completed);
    assert_eq!(
        adaptive_result.states_visited,
        sequential_result.states_visited
    );
    assert_eq!(adaptive.states, sequential.states);
    assert_eq!(adaptive.deadlocks, sequential.deadlocks);
    assert_eq!(adaptive.firings, sequential.firings);
    assert!(adaptive.merged_summaries > 0);
}

#[test]
fn test_explore_observer_small_state_budget_downshifts_to_sequential() {
    let net = counting_net(100);
    let sequential_config = ExplorationConfig::new(10);
    let mut sequential = CountingObserver::new();
    let sequential_result = explore(&net, &sequential_config, &mut sequential);

    let adaptive_config = ExplorationConfig::new(10).with_workers(4);
    let mut adaptive = CountingObserver::new();
    let adaptive_result = explore_observer(&net, &adaptive_config, &mut adaptive);

    assert_eq!(adaptive_result.completed, sequential_result.completed);
    assert_eq!(
        adaptive_result.states_visited,
        sequential_result.states_visited
    );
    assert_eq!(adaptive.states, sequential.states);
    assert_eq!(adaptive.deadlocks, sequential.deadlocks);
    assert_eq!(adaptive.firings, sequential.firings);
    assert_eq!(adaptive.merged_summaries, 0);
}

#[test]
fn test_explore_observer_parallel_preserves_por_semantics() {
    let net = two_independent_deadlocking_processes();

    let sequential_config = ExplorationConfig::new(1000).with_por(PorStrategy::DeadlockPreserving);
    let mut sequential = CountingObserver::new();
    let sequential_result = explore(&net, &sequential_config, &mut sequential);

    let parallel_config = ExplorationConfig::new(1000)
        .with_workers(4)
        .with_por(PorStrategy::DeadlockPreserving);
    let mut parallel = CountingObserver::new();
    let parallel_result = explore_observer(&net, &parallel_config, &mut parallel);

    assert!(sequential_result.completed);
    assert!(parallel_result.completed);
    assert_eq!(
        parallel_result.states_visited,
        sequential_result.states_visited
    );
    assert_eq!(parallel.states, sequential.states);
    assert_eq!(parallel.deadlocks, sequential.deadlocks);
    assert_eq!(parallel.firings, sequential.firings);
}

#[test]
fn test_explore_observer_parallel_state_limit_is_exact() {
    let net = counting_net(100);
    let config = ExplorationConfig::new(10).with_workers(4);
    let mut observer = CountingObserver::new();
    let result = explore_observer(&net, &config, &mut observer);

    assert!(!result.completed);
    assert_eq!(result.states_visited, 10);
    assert_eq!(observer.states, 10);
}

#[test]
fn test_parallel_por_explores_fewer_states_than_parallel_no_por() {
    let net = two_independent_deadlocking_processes();

    let no_por_config = ExplorationConfig::new(1000).with_workers(4);
    let mut no_por = CountingObserver::new();
    let no_por_result = explore_observer(&net, &no_por_config, &mut no_por);

    let por_config = ExplorationConfig::new(1000)
        .with_workers(4)
        .with_por(PorStrategy::DeadlockPreserving);
    let mut por = CountingObserver::new();
    let por_result = explore_observer(&net, &por_config, &mut por);

    assert!(no_por_result.completed);
    assert!(por_result.completed);
    assert!(
        por_result.states_visited < no_por_result.states_visited,
        "POR ({}) should visit fewer states than no-POR ({})",
        por_result.states_visited,
        no_por_result.states_visited
    );
    assert_eq!(por.deadlocks, no_por.deadlocks);
}
