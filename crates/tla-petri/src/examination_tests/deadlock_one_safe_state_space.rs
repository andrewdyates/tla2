// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::examinations::deadlock::DeadlockObserver;
use crate::examinations::one_safe::OneSafeObserver;
use crate::examinations::state_space::StateSpaceObserver;
use crate::explorer::{explore, explore_observer, ExplorationConfig};
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
use crate::stubborn::PorStrategy;

use super::fixtures::{
    counting_net, cyclic_safe_net, default_config, immediate_deadlock_net, linear_deadlock_net,
    not_safe_net,
};

#[test]
fn test_deadlock_observer_finds_deadlock_in_linear_net() {
    let net = linear_deadlock_net();
    let config = default_config();
    let mut observer = DeadlockObserver::new();
    let result = explore(&net, &config, &mut observer);

    assert!(observer.found_deadlock());
    assert!(result.stopped_by_observer);
}

#[test]
fn test_deadlock_observer_no_deadlock_in_cyclic_net() {
    let net = cyclic_safe_net();
    let config = default_config();
    let mut observer = DeadlockObserver::new();
    let result = explore(&net, &config, &mut observer);

    assert!(!observer.found_deadlock());
    assert!(result.completed);
    assert!(!result.stopped_by_observer);
}

#[test]
fn test_deadlock_observer_immediate_deadlock() {
    let net = immediate_deadlock_net();
    let config = default_config();
    let mut observer = DeadlockObserver::new();
    let result = explore(&net, &config, &mut observer);

    assert!(observer.found_deadlock());
    assert!(result.stopped_by_observer);
    assert_eq!(result.states_visited, 1);
}

#[test]
fn test_one_safe_observer_safe_cyclic_net() {
    let net = cyclic_safe_net();
    let config = default_config();
    let mut observer = OneSafeObserver::new();
    let result = explore(&net, &config, &mut observer);

    assert!(observer.is_safe());
    assert!(result.completed);
    assert_eq!(result.states_visited, 2);
}

#[test]
fn test_one_safe_observer_detects_unsafe_net() {
    let net = not_safe_net();
    let config = default_config();
    let mut observer = OneSafeObserver::new();
    let result = explore(&net, &config, &mut observer);

    assert!(!observer.is_safe());
    assert!(result.stopped_by_observer);
}

#[test]
fn test_one_safe_observer_initial_marking_safe() {
    let net = immediate_deadlock_net();
    let config = default_config();
    let mut observer = OneSafeObserver::new();
    let result = explore(&net, &config, &mut observer);

    assert!(observer.is_safe());
    assert!(result.completed);
}

#[test]
fn test_one_safe_observer_unsafe_at_initial() {
    let net = PetriNet {
        name: None,
        places: vec![PlaceInfo {
            id: "P0".into(),
            name: None,
        }],
        transitions: vec![],
        initial_marking: vec![2],
    };
    let config = default_config();
    let mut observer = OneSafeObserver::new();
    let result = explore(&net, &config, &mut observer);

    assert!(!observer.is_safe());
    assert!(result.stopped_by_observer);
    assert_eq!(result.states_visited, 1);
}

fn delayed_source_place_overflow_net() -> PetriNet {
    let mut places: Vec<PlaceInfo> = (0..=17)
        .map(|idx| PlaceInfo {
            id: format!("p{idx}"),
            name: None,
        })
        .collect();
    let accumulator = PlaceIdx(18);
    places.push(PlaceInfo {
        id: "p_acc".into(),
        name: None,
    });

    let transitions: Vec<TransitionInfo> = (0..=16)
        .map(|idx| {
            let mut outputs = vec![Arc {
                place: PlaceIdx((idx + 1) as u32),
                weight: 1,
            }];
            if idx >= 15 {
                outputs.push(Arc {
                    place: accumulator,
                    weight: 1,
                });
            }
            TransitionInfo {
                id: format!("t{idx}"),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(idx as u32),
                    weight: 1,
                }],
                outputs,
            }
        })
        .collect();

    let mut initial_marking = vec![0; places.len()];
    initial_marking[0] = 1;

    PetriNet {
        name: Some("delayed-source-place-overflow".into()),
        places,
        transitions,
        initial_marking,
    }
}

#[test]
fn test_state_space_observer_linear_net() {
    let net = linear_deadlock_net();
    let config = default_config();
    let mut observer = StateSpaceObserver::new(&net.initial_marking);
    let result = explore(&net, &config, &mut observer);

    assert!(result.completed);
    let stats = observer.stats();
    assert_eq!(stats.states, 2);
    assert_eq!(stats.edges, 1);
    assert_eq!(stats.max_token_in_place, 1);
    assert_eq!(stats.max_token_sum, 1);
}

#[test]
fn test_one_safe_verdict_detects_delayed_source_place_overflow() {
    let net = delayed_source_place_overflow_net();
    let config = ExplorationConfig::new(64);

    assert!(
        matches!(
            super::super::one_safe_verdict(&net, &config, &[]),
            crate::output::Verdict::False | crate::output::Verdict::CannotCompute
        ),
        "delayed source-place overflow must not report OneSafe = TRUE"
    );
}

#[test]
fn test_state_space_observer_counting_net() {
    let net = counting_net();
    let config = default_config();
    let mut observer = StateSpaceObserver::new(&net.initial_marking);
    let result = explore(&net, &config, &mut observer);

    assert!(result.completed);
    let stats = observer.stats();
    assert_eq!(stats.states, 4);
    assert_eq!(stats.edges, 3);
    assert_eq!(stats.max_token_in_place, 3);
    assert_eq!(stats.max_token_sum, 3);
}

#[test]
fn test_state_space_observer_immediate_deadlock() {
    let net = immediate_deadlock_net();
    let config = default_config();
    let mut observer = StateSpaceObserver::new(&net.initial_marking);
    let result = explore(&net, &config, &mut observer);

    assert!(result.completed);
    let stats = observer.stats();
    assert_eq!(stats.states, 1);
    assert_eq!(stats.edges, 0);
    assert_eq!(stats.max_token_in_place, 1);
    assert_eq!(stats.max_token_sum, 1);
}

#[test]
fn test_state_space_never_stops_early() {
    let net = cyclic_safe_net();
    let config = default_config();
    let mut observer = StateSpaceObserver::new(&net.initial_marking);
    let result = explore(&net, &config, &mut observer);

    assert!(!result.stopped_by_observer);
    assert!(result.completed);
}

#[test]
fn test_deadlock_observer_parallel_matches_sequential_verdict() {
    let net = linear_deadlock_net();
    let sequential_config = default_config();
    let mut sequential = DeadlockObserver::new();
    let sequential_result = explore_observer(&net, &sequential_config, &mut sequential);

    let parallel_config = default_config().with_workers(4);
    let mut parallel = DeadlockObserver::new();
    let parallel_result = explore_observer(&net, &parallel_config, &mut parallel);

    assert_eq!(parallel.found_deadlock(), sequential.found_deadlock());
    assert_eq!(
        parallel_result.stopped_by_observer,
        sequential_result.stopped_by_observer
    );
}

#[test]
fn test_state_space_observer_parallel_matches_sequential_stats() {
    let net = counting_net();
    let sequential_config = default_config();
    let mut sequential = StateSpaceObserver::new(&net.initial_marking);
    let sequential_result = explore_observer(&net, &sequential_config, &mut sequential);

    let parallel_config = default_config().with_workers(4);
    let mut parallel = StateSpaceObserver::new(&net.initial_marking);
    let parallel_result = explore_observer(&net, &parallel_config, &mut parallel);

    assert_eq!(parallel_result.completed, sequential_result.completed);
    let sequential_stats = sequential.stats();
    let parallel_stats = parallel.stats();
    assert_eq!(parallel_stats.states, sequential_stats.states);
    assert_eq!(parallel_stats.edges, sequential_stats.edges);
    assert_eq!(
        parallel_stats.max_token_in_place,
        sequential_stats.max_token_in_place
    );
    assert_eq!(parallel_stats.max_token_sum, sequential_stats.max_token_sum);
}

// ── Structural deadlock-freedom shortcut ─────────────────────────────────

/// Cyclic net (token cycles p0→p1→p0) is structurally deadlock-free.
/// `deadlock_verdict` should return FALSE via siphon/trap without BFS.
#[test]
fn test_deadlock_verdict_structural_shortcut_cyclic_net() {
    let net = cyclic_safe_net();
    // Use a tiny budget — if the structural shortcut works, no BFS needed.
    let config = ExplorationConfig::new(1);
    assert_eq!(
        super::super::deadlock_verdict(&net, &config),
        crate::output::Verdict::False
    );
}

/// Linear net (p0→t0→p1, no cycle) has a siphon vulnerability.
/// Structural analysis returns `Some(false)` (inconclusive), so BFS runs
/// and finds the actual deadlock.
#[test]
fn test_deadlock_verdict_falls_through_to_bfs_on_linear_net() {
    let net = linear_deadlock_net();
    let config = default_config();
    assert_eq!(
        super::super::deadlock_verdict(&net, &config),
        crate::output::Verdict::True
    );
}

/// Immediate deadlock net (no transitions) — structural analysis returns
/// `Some(false)` (not deadlock-free), BFS confirms deadlock.
#[test]
fn test_deadlock_verdict_immediate_deadlock_structural_then_bfs() {
    let net = immediate_deadlock_net();
    let config = default_config();
    assert_eq!(
        super::super::deadlock_verdict(&net, &config),
        crate::output::Verdict::True
    );
}

/// Non-free-choice net with a reachable deadlock.
///
/// P0(1) and P1(1) feed two conflicting transitions:
///   T0: {P0} → {P2}        (needs only P0)
///   T1: {P0, P1} → {P3}    (needs both P0 and P1)
///
/// P0 is shared between T0 (input set {P0}) and T1 (input set {P0, P1}),
/// making this non-free-choice. Both nondeterministic paths deadlock:
///   - T0 fires → (0,1,1,0): nothing enabled
///   - T1 fires → (0,0,0,1): nothing enabled
///
/// Regression for 29f42ed79: `structural_deadlock_free` must return `None`
/// (non-free-choice guard), so `deadlock_verdict` falls through to BFS.
#[test]
fn test_deadlock_verdict_non_free_choice_net_falls_through_to_bfs() {
    let net = PetriNet {
        name: Some("non-free-choice-deadlock".into()),
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
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "T1".into(),
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
                outputs: vec![Arc {
                    place: PlaceIdx(3),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![1, 1, 0, 0],
    };
    let config = default_config();
    assert_eq!(
        super::super::deadlock_verdict(&net, &config),
        crate::output::Verdict::True
    );
}

// ── POR (stubborn set) integration tests ────────────────────────────────

/// Two independent processes (p0→t0→p1, p2→t1→p3) both leading to deadlock.
/// Full BFS explores 4 states (all interleavings). Deadlock-preserving POR
/// should explore fewer states (only one interleaving order) while still
/// finding the same deadlock.
fn two_independent_deadlocking_processes() -> PetriNet {
    PetriNet {
        name: Some("two-independent-deadlock".into()),
        places: vec![
            PlaceInfo {
                id: "p0".into(),
                name: None,
            },
            PlaceInfo {
                id: "p1".into(),
                name: None,
            },
            PlaceInfo {
                id: "p2".into(),
                name: None,
            },
            PlaceInfo {
                id: "p3".into(),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "t0".into(),
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
                id: "t1".into(),
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
        initial_marking: vec![1, 0, 1, 0],
    }
}

#[test]
fn test_por_deadlock_preserving_reduces_state_count() {
    let net = two_independent_deadlocking_processes();

    // Full BFS (no POR): explores all interleavings
    let full_config = ExplorationConfig::new(1000);
    let mut full_observer = DeadlockObserver::new();
    let full_result = explore(&net, &full_config, &mut full_observer);

    // POR BFS (deadlock-preserving): explores reduced state space
    let por_config = ExplorationConfig::new(1000).with_por(PorStrategy::DeadlockPreserving);
    let mut por_observer = DeadlockObserver::new();
    let por_result = explore(&net, &por_config, &mut por_observer);

    // Both find the deadlock (observer stops early once found)
    assert!(
        full_observer.found_deadlock(),
        "full BFS should find deadlock"
    );
    assert!(
        por_observer.found_deadlock(),
        "POR BFS should find deadlock"
    );

    // POR should explore strictly fewer states on independent processes.
    // Full BFS: 4 states (initial, t0→only, t1→only, both-fired deadlock).
    // POR: 3 states (one interleaving: initial → t0-fired → both-fired deadlock).
    assert!(
        por_result.states_visited < full_result.states_visited,
        "POR should explore fewer states: POR={}, full={}",
        por_result.states_visited,
        full_result.states_visited,
    );
}

#[test]
fn test_por_no_reduction_on_shared_resource_gives_same_deadlock() {
    // Two transitions competing for one token: t0 reads p0→p1, t1 reads p0→p2.
    // Since both share p0, the stubborn set = all enabled = no reduction.
    // POR and full BFS should give identical results.
    let net = PetriNet {
        name: Some("shared-resource".into()),
        places: vec![
            PlaceInfo {
                id: "p0".into(),
                name: None,
            },
            PlaceInfo {
                id: "p1".into(),
                name: None,
            },
            PlaceInfo {
                id: "p2".into(),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "t0".into(),
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
                id: "t1".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![1, 0, 0],
    };

    let full_config = ExplorationConfig::new(1000);
    let mut full_obs = DeadlockObserver::new();
    let full_result = explore(&net, &full_config, &mut full_obs);

    let por_config = ExplorationConfig::new(1000).with_por(PorStrategy::DeadlockPreserving);
    let mut por_obs = DeadlockObserver::new();
    let por_result = explore(&net, &por_config, &mut por_obs);

    assert_eq!(full_result.completed, por_result.completed);
    assert_eq!(full_obs.found_deadlock(), por_obs.found_deadlock());
    assert_eq!(full_result.states_visited, por_result.states_visited);
}

/// Net where P-invariants give no bounds but LP proves all places ≤ 1.
///
/// t0: p0 → p1, t1: p1 → (consumed, no output)
/// P-invariant: y^T·C = 0 has only trivial solution (y=0) because the
/// incidence matrix has rank 2 and both rows are linearly independent.
/// LP state equation: M_p0 = 1 - x_t0 ≥ 0 → x_t0 ≤ 1 → M_p0 ≤ 1;
/// M_p1 = x_t0 - x_t1 ≥ 0 and x_t0 ≤ 1 → M_p1 ≤ 1.
#[test]
fn test_one_safe_lp_structural_proof_when_p_invariants_insufficient() {
    let net = PetriNet {
        name: None,
        places: vec![
            PlaceInfo {
                id: "p0".into(),
                name: Some("p0".into()),
            },
            PlaceInfo {
                id: "p1".into(),
                name: Some("p1".into()),
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "t0".into(),
                name: Some("t0".into()),
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
                id: "t1".into(),
                name: Some("t1".into()),
                inputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
                outputs: vec![],
            },
        ],
        initial_marking: vec![1, 0],
    };

    // Verify P-invariants are insufficient: no P-invariant bounds either place.
    let invariants = crate::invariant::compute_p_invariants(&net);
    let p0_bound = crate::invariant::structural_place_bound(&invariants, 0);
    let p1_bound = crate::invariant::structural_place_bound(&invariants, 1);
    assert!(
        p0_bound.is_none() || p1_bound.is_none(),
        "At least one place should not be bounded by P-invariants"
    );

    // But LP should prove both places ≤ 1.
    use crate::lp_state_equation::lp_upper_bound;
    let lp_p0 = lp_upper_bound(&net, &[PlaceIdx(0)]);
    let lp_p1 = lp_upper_bound(&net, &[PlaceIdx(1)]);
    assert_eq!(lp_p0, Some(1), "LP should bound p0 to 1");
    assert_eq!(lp_p1, Some(1), "LP should bound p1 to 1");

    // The verdict should be TRUE (1-safe) via the LP structural path.
    let config = ExplorationConfig::new(64);
    let verdict = super::super::one_safe_verdict(&net, &config, &[]);
    assert_eq!(verdict, crate::output::Verdict::True);
}

// ── Worker-budget contract parity tests (#1520) ──────────────────────

/// `deadlock_verdict` must give the same answer regardless of worker count.
/// On a deadlocking net, both sequential (workers=1) and portfolio (workers=4)
/// paths must return TRUE.
#[test]
fn test_deadlock_verdict_parity_linear_deadlock_workers_1_vs_4() {
    let net = linear_deadlock_net();
    let v1 = super::super::deadlock_verdict(&net, &ExplorationConfig::new(1024));
    let v4 = super::super::deadlock_verdict(&net, &ExplorationConfig::new(1024).with_workers(4));
    assert_eq!(v1, crate::output::Verdict::True);
    assert_eq!(v4, crate::output::Verdict::True);
}

/// Structurally deadlock-free cyclic net: both paths must return FALSE.
/// This is resolved by the structural shortcut before the budget split matters,
/// but the test confirms the full path is consistent.
#[test]
fn test_deadlock_verdict_parity_cyclic_safe_workers_1_vs_4() {
    let net = cyclic_safe_net();
    let v1 = super::super::deadlock_verdict(&net, &ExplorationConfig::new(1024));
    let v4 = super::super::deadlock_verdict(&net, &ExplorationConfig::new(1024).with_workers(4));
    assert_eq!(v1, crate::output::Verdict::False);
    assert_eq!(v4, crate::output::Verdict::False);
}

/// Immediate deadlock net: both paths must return TRUE.
#[test]
fn test_deadlock_verdict_parity_immediate_deadlock_workers_1_vs_4() {
    let net = immediate_deadlock_net();
    let v1 = super::super::deadlock_verdict(&net, &ExplorationConfig::new(1024));
    let v4 = super::super::deadlock_verdict(&net, &ExplorationConfig::new(1024).with_workers(4));
    assert_eq!(v1, crate::output::Verdict::True);
    assert_eq!(v4, crate::output::Verdict::True);
}
