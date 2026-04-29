// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::examinations::stable_marking::StableMarkingObserver;
use crate::explorer::explore;
use crate::output::Verdict;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};

use super::super::stable_marking_verdict;
use super::fixtures::{counting_net, cyclic_safe_net, default_config, immediate_deadlock_net};

#[test]
fn test_stable_marking_immediate_deadlock_all_stable() {
    let net = immediate_deadlock_net();
    let config = default_config();
    let mut observer = StableMarkingObserver::new(&net.initial_marking);
    let result = explore(&net, &config, &mut observer);

    assert!(!observer.all_unstable());
    assert!(result.completed);
}

#[test]
fn test_stable_marking_cyclic_net_all_unstable() {
    let net = cyclic_safe_net();
    let config = default_config();
    let mut observer = StableMarkingObserver::new(&net.initial_marking);
    let result = explore(&net, &config, &mut observer);

    assert!(observer.all_unstable());
    assert!(result.stopped_by_observer);
}

#[test]
fn test_stable_marking_counting_net_all_unstable() {
    let net = counting_net();
    let config = default_config();
    let mut observer = StableMarkingObserver::new(&net.initial_marking);
    let result = explore(&net, &config, &mut observer);

    assert!(observer.all_unstable());
    assert!(result.stopped_by_observer);
}

#[test]
fn test_stable_marking_with_isolated_stable_place() {
    let net = PetriNet {
        name: Some("isolated-stable".into()),
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
        initial_marking: vec![1, 0, 5],
    };
    let config = default_config();
    let mut observer = StableMarkingObserver::new(&net.initial_marking);
    let result = explore(&net, &config, &mut observer);

    assert!(!observer.all_unstable());
    assert!(result.completed);
}

/// Verify the isolated-place shortcut works through `stable_marking_verdict`.
/// The net from `test_stable_marking_with_isolated_stable_place` has P2 isolated
/// with initial marking 5, which is structurally stable.
#[test]
fn test_stable_marking_verdict_with_isolated_place_returns_true() {
    let net = PetriNet {
        name: Some("isolated-stable".into()),
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
        initial_marking: vec![1, 0, 5],
    };
    let config = default_config();
    let verdict = stable_marking_verdict(&net, &config, &[]);
    assert_eq!(
        verdict,
        Verdict::True,
        "StableMarking should be TRUE when an isolated place exists"
    );
}

/// Net with ONLY pre-agglomeration reduction (no constant or isolated places).
///
/// P0(1) → T0 → P1(0) → T1 → P2(0)
///
/// P1 is pre-agglomeratable (sole producer T0, initial=0, consumer T1 reads 1).
/// No constant places (P0 net effect -1, P1 net effect +1/-1, P2 net effect +1).
/// No isolated places (all connected to alive transitions).
///
/// In the original net, every place changes marking:
///   P0: 1→0, P1: 0→1→0, P2: 0→1
/// So StableMarking should be FALSE (no place has m(p) = m₀(p) for all reachable m).
///
/// Regression test: previously, `places_removed() > 0` short-circuited to TRUE
/// because the agglomerated place was counted as structurally stable, but
/// agglomerated places are NOT stable (their marking changes when transitions fire).
#[test]
fn test_stable_marking_agglomeration_only_not_false_positive() {
    let net = PetriNet {
        name: Some("agg-only-all-unstable".into()),
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
                    place: PlaceIdx(1),
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

    let config = default_config();

    // Verify pre-agglomeration is detected: P1 has sole producer T0,
    // initial=0, consumer T1 reads 1, and T0's input (P0) does not
    // overlap with T1's output (P2). Berthelot condition 6 satisfied.
    let report = crate::reduction::analyze(&net);
    assert!(
        !report.pre_agglomerations.is_empty(),
        "net should have pre-agglomeration candidates"
    );
    assert!(
        report.constant_places.is_empty(),
        "net should have no constant places"
    );
    assert!(
        report.isolated_places.is_empty(),
        "net should have no isolated places"
    );

    // The verdict must be FALSE: all places change marking.
    // The old code returned TRUE here (wrong) because it checked
    // places_removed() which included agglomerated places.
    let verdict = stable_marking_verdict(&net, &config, &[]);
    assert_eq!(
        verdict,
        Verdict::False,
        "StableMarking should be FALSE when only agglomerated places are removed"
    );
}

/// Regression test for #1442: multi-round reduction reveals stable places
/// that single-round `analyze()` misses.
///
/// P_target(5) is connected to T_dead (dead, delta +1) and T_selfloop
/// (self-loop transition, delta 0). Single-round `analyze()` finds P_target
/// neither constant nor cascade-isolated. Multi-round `reduce_iterative`
/// removes T_dead (dead) and T_selfloop (Rule J) in round 1, then finds
/// P_target isolated in round 2. The fix checks the composed report and
/// returns TRUE; without it, BFS on the reduced net returns FALSE (wrong).
#[test]
fn test_stable_marking_multi_round_reduction_reveals_stable_place() {
    let net = PetriNet {
        name: Some("cascade-stable-multi-round".into()),
        places: vec![
            PlaceInfo {
                id: "P_target".into(),
                name: None,
            },
            PlaceInfo {
                id: "P_feeder".into(),
                name: None,
            },
            PlaceInfo {
                id: "P_c".into(),
                name: None,
            },
            PlaceInfo {
                id: "P_a".into(),
                name: None,
            },
            PlaceInfo {
                id: "P_b".into(),
                name: None,
            },
        ],
        transitions: vec![
            // T_dead: needs P_feeder(2) but initial=1, no producer → dead.
            // Output to P_target makes P_target non-constant in original net.
            TransitionInfo {
                id: "T_dead".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 2,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
            },
            // T_selfloop: pure self-loop on P_target (Rule J removes it).
            TransitionInfo {
                id: "T_selfloop".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
            },
            // T_alive: keeps P_feeder non-cascade-isolated after T_dead removal.
            TransitionInfo {
                id: "T_alive".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
            // T_live: makes P_a and P_b unstable.
            TransitionInfo {
                id: "T_live".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(3),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(4),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![5, 1, 0, 1, 0],
    };

    // Pre-check must NOT find P_target.
    let report = crate::reduction::analyze(&net);
    assert!(
        report.constant_places.is_empty(),
        "no constant places in original net"
    );
    assert!(
        report.isolated_places.is_empty(),
        "no isolated places in original net"
    );

    // Multi-round reduction must find P_target in composed report.
    let reduced = crate::reduction::reduce_iterative(&net).unwrap();
    assert!(
        !reduced.report.constant_places.is_empty() || !reduced.report.isolated_places.is_empty(),
        "composed report should have stable removed places from multi-round reduction"
    );

    // Verdict must be TRUE: P_target(5) is stable.
    let config = default_config();
    let verdict = stable_marking_verdict(&net, &config, &[]);
    assert_eq!(
        verdict,
        Verdict::True,
        "StableMarking should be TRUE: P_target is stable (multi-round reduction reveals it)"
    );
}
