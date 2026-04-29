// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::fixtures::{cyclic_net, deadlock_net, simple_linear_net, CountingObserver};
use super::*;

#[test]
fn test_explore_linear_net() {
    let net = simple_linear_net();
    let config = ExplorationConfig::default();
    let mut observer = CountingObserver::new();
    let result = explore(&net, &config, &mut observer);

    assert_eq!(result.states_visited, 2);
    assert!(result.completed);
    assert_eq!(observer.states, 2);
    assert_eq!(observer.deadlocks, 1);
    assert_eq!(observer.firings, 1);
}

#[test]
fn test_explore_cyclic_net() {
    let net = cyclic_net();
    let config = ExplorationConfig::default();
    let mut observer = CountingObserver::new();
    let result = explore(&net, &config, &mut observer);

    assert_eq!(result.states_visited, 2);
    assert!(result.completed);
    assert_eq!(observer.deadlocks, 0);
}

#[test]
fn test_explore_deadlock_net() {
    let net = deadlock_net();
    let config = ExplorationConfig::default();
    let mut observer = CountingObserver::new();
    let result = explore(&net, &config, &mut observer);

    assert_eq!(result.states_visited, 1);
    assert!(result.completed);
    assert_eq!(observer.deadlocks, 1);
}

#[test]
fn test_explore_state_limit() {
    let net = PetriNet {
        name: Some("counting".into()),
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
            outputs: vec![Arc {
                place: PlaceIdx(1),
                weight: 1,
            }],
        }],
        initial_marking: vec![100, 0],
    };
    let config = ExplorationConfig::new(10);
    let mut observer = CountingObserver::new();
    let result = explore(&net, &config, &mut observer);

    assert!(!result.completed);
    assert!(result.states_visited <= 11);
}

#[test]
fn test_explore_early_termination() {
    struct StopAfterTwo {
        count: usize,
    }

    impl ExplorationObserver for StopAfterTwo {
        fn on_new_state(&mut self, _marking: &[u64]) -> bool {
            self.count += 1;
            self.count < 2
        }

        fn on_transition_fire(&mut self, _trans: TransitionIdx) -> bool {
            true
        }

        fn on_deadlock(&mut self, _marking: &[u64]) {}

        fn is_done(&self) -> bool {
            self.count >= 2
        }
    }

    let net = PetriNet {
        name: None,
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
            outputs: vec![Arc {
                place: PlaceIdx(1),
                weight: 1,
            }],
        }],
        initial_marking: vec![100, 0],
    };
    let config = ExplorationConfig::default();
    let mut observer = StopAfterTwo { count: 0 };
    let result = explore(&net, &config, &mut observer);

    assert!(result.stopped_by_observer);
    assert!(!result.completed);
}
