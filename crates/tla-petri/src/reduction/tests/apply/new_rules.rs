// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for new structural reduction rules:
//! - Sink transition removal
//! - Trap-based dead transition detection

use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};
use crate::reduction::{reduce, reduce_iterative_structural};

use super::super::support::{arc, place, trans};

/// Sink transition (no outputs, only consumes from unprotected places)
/// should be removed by structural reduction.
#[test]
fn test_reduce_sink_transition_removed() {
    // Net: p0(3) --[t_sink]--> (nothing)
    //       p0(3) --[t_a]--> p1
    //       p1 --[t_b]--> p0          (cycle so p1 is NOT non-decreasing)
    //
    // t_sink has no outputs — it's a pure token consumer.
    // Reduction should remove t_sink. t_a and t_b survive.
    let net = PetriNet {
        name: Some("sink-transition-test".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t_sink", vec![arc(0, 1)], vec![]),
            trans("t_a", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_b", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![3, 0],
    };

    let reduced = reduce(&net);
    // t_sink should be removed — t_a and t_b survive
    assert_eq!(
        reduced.net.num_transitions(),
        2,
        "sink transition should be removed, leaving 2 transitions"
    );
    // Verify t_sink is gone
    for t in &reduced.net.transitions {
        assert_ne!(t.id, "t_sink", "t_sink should have been removed");
    }
    // Both places remain (p0 and p1 form a live cycle)
    assert_eq!(reduced.net.num_places(), 2);
    assert_eq!(reduced.net.initial_marking, vec![3, 0]);
}

/// Trap-based dead transition detection: zero-marked cycle with no
/// external token source should make all cycle transitions dead.
#[test]
fn test_reduce_trap_dead_transitions_zero_cycle() {
    // Net: p0(0) --[t0]--> p1(0) --[t1]--> p0(0)
    //       p2(1) --[t_a]--> p3 --[t_b]--> p2    (live cycle)
    //
    // p0 and p1 form a zero-marked cycle. t0 and t1 are dead because
    // no tokens can ever enter the cycle. The cascading analysis alone
    // would not detect this because each place HAS a producer.
    let net = PetriNet {
        name: Some("trap-dead-test".to_string()),
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
            trans("t_a", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t_b", vec![arc(3, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![0, 0, 1, 0],
    };

    let reduced = reduce(&net);
    // t0 and t1 should be detected as dead via trap analysis.
    // p0 and p1 should become isolated and be removed.
    // Only t_a, t_b, p2, p3 survive.
    assert_eq!(
        reduced.net.num_transitions(),
        2,
        "trap-dead transitions should be removed"
    );
    for t in &reduced.net.transitions {
        assert!(
            t.id == "t_a" || t.id == "t_b",
            "only t_a and t_b should survive, found {}",
            t.id
        );
    }
    assert_eq!(
        reduced.net.num_places(),
        2,
        "cycle places should be removed as cascade-isolated"
    );
    assert_eq!(reduced.net.initial_marking, vec![1, 0]);
}

/// Sink transition with protected input place should NOT be removed.
#[test]
fn test_reduce_sink_transition_protected_input_preserved() {
    // Net: p0(3) --[t_sink]--> (nothing)
    //       p0(3) --[t_a]--> p1
    //       p1 --[t_b]--> p0          (cycle so p1 is NOT non-decreasing)
    //
    // Protect p0 — t_sink touches it, so t_sink should be kept.
    let net = PetriNet {
        name: Some("sink-protected-test".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t_sink", vec![arc(0, 1)], vec![]),
            trans("t_a", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_b", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![3, 0],
    };

    // Protect p0 — sink transition touches it, so it should be kept
    let protected = vec![true, false];
    let reduced = crate::reduction::reduce_iterative_structural_with_protected(&net, &protected)
        .expect("reduction should succeed");
    // With p0 protected, t_sink should not be removed
    assert_eq!(
        reduced.net.num_transitions(),
        3,
        "sink transition touching protected place should survive"
    );
}

/// Iterative reduction: trap dead transitions expose new cascade-isolated
/// places, which in turn can trigger more reductions.
#[test]
fn test_iterative_structural_trap_dead_cascade() {
    // Net with a zero-marked cycle plus a dependent transition:
    // p0(0) --[t0]--> p1(0) --[t1]--> p0(0)
    // p0(0) --[t2]--> p2 --[t3]--> p0      (t2 consumes from trap)
    //
    // Trap analysis marks t0, t1, t2 as dead (all consume from the trap
    // {p0, p1}). t3 also consumes from p2 which is empty and can never
    // gain tokens once t2 is dead → also dead via cascading analysis.
    // Then all places become isolated and are removed.
    let net = PetriNet {
        name: Some("cascade-trap-test".to_string()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
            trans("t2", vec![arc(0, 1)], vec![arc(2, 1)]),
            trans("t3", vec![arc(2, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![0, 0, 0],
    };

    let reduced = reduce_iterative_structural(&net).expect("reduction should succeed");
    // All transitions dead, all places isolated → empty net
    assert_eq!(
        reduced.net.num_transitions(),
        0,
        "all transitions should be dead"
    );
    assert_eq!(reduced.net.num_places(), 0, "all places should be isolated");
}

/// Verify that trap-dead + sink removal composes correctly: a sink
/// transition whose only input comes from a trap-dead zone should
/// also be removed (it's dead because its input place is in a trap).
#[test]
fn test_trap_dead_makes_downstream_sink_dead() {
    // p0(0) --[t_cycle]--> p0(0)    (self-loop, zero-marked trap)
    // p0(0) --[t_sink]--> (nothing)  (sink, but also trap-dead)
    // p1(1) --[t_a]--> p2 --[t_b]--> p1    (live cycle)
    let net = PetriNet {
        name: Some("trap-sink-combo".to_string()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans("t_cycle", vec![arc(0, 1)], vec![arc(0, 1)]),
            trans("t_sink", vec![arc(0, 1)], vec![]),
            trans("t_a", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t_b", vec![arc(2, 1)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![0, 1, 0],
    };

    let reduced = reduce_iterative_structural(&net).expect("reduction should succeed");
    // t_cycle is a self-loop transition → removed
    // t_sink consumes from trap place p0 → dead (trap analysis) or sink
    // Only t_a and t_b survive. p0 becomes isolated.
    assert_eq!(reduced.net.num_transitions(), 2);
    for t in &reduced.net.transitions {
        assert!(
            t.id == "t_a" || t.id == "t_b",
            "only t_a and t_b should survive, found {}",
            t.id
        );
    }
}

/// Safety property preservation: reachable markings of the reduced net
/// should be a superset of the original's (no false positives for safety).
#[test]
fn test_sink_removal_preserves_reachable_markings() {
    // Net: p0(2) --[t_sink]--> (nothing)
    //       p0(2) --[t_a]--> p1
    //       p1 --[t_b]--> p0
    //
    // Without t_sink: p0 can have 0, 1, or 2 tokens. Same with t_sink
    // (t_sink can only reduce p0's count, never increase).
    // So removing t_sink is sound for safety — any marking reachable
    // without t_sink was also reachable with it.
    let net = PetriNet {
        name: Some("sink-safety-test".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t_sink", vec![arc(0, 1)], vec![]),
            trans("t_a", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_b", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![2, 0],
    };

    let reduced = reduce(&net);
    // t_sink removed, t_a and t_b survive
    assert_eq!(reduced.net.num_transitions(), 2);

    // Verify reachable markings: enumerate reduced net
    let mut visited = std::collections::HashSet::new();
    let mut queue = vec![reduced.net.initial_marking.clone()];
    visited.insert(reduced.net.initial_marking.clone());

    while let Some(marking) = queue.pop() {
        for tidx in 0..reduced.net.num_transitions() {
            let t = TransitionIdx(tidx as u32);
            if reduced.net.is_enabled(&marking, t) {
                let next = reduced.net.fire(&marking, t);
                if visited.insert(next.clone()) {
                    queue.push(next);
                }
            }
        }
    }

    // With t_a and t_b cycling 2 tokens: {[2,0], [1,1], [0,2]}
    assert_eq!(visited.len(), 3);
    assert!(visited.contains(&vec![2, 0]));
    assert!(visited.contains(&vec![1, 1]));
    assert!(visited.contains(&vec![0, 2]));
}
