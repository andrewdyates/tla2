// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::explorer::ExplorationConfig;
use crate::output::Verdict;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
use crate::reduction::{reduce, reduce_iterative};

use super::super::{deadlock_verdict, liveness_verdict, quasi_liveness_verdict};

fn place(id: &str) -> PlaceInfo {
    PlaceInfo {
        id: id.into(),
        name: None,
    }
}

fn arc(place: u32, weight: u64) -> Arc {
    Arc {
        place: PlaceIdx(place),
        weight,
    }
}

fn transition(id: &str, inputs: Vec<Arc>, outputs: Vec<Arc>) -> TransitionInfo {
    TransitionInfo {
        id: id.into(),
        name: None,
        inputs,
        outputs,
    }
}

#[test]
fn test_deadlock_verdict_skips_blocked_constant_self_loop() {
    let net = PetriNet {
        name: Some("blocked-constant-self-loop".into()),
        places: vec![place("p_const"), place("p_live"), place("p_done")],
        transitions: vec![
            transition("t_loop", vec![arc(0, 2)], vec![arc(0, 2)]),
            transition("t_once", vec![arc(1, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![1, 1, 0],
    };

    let reduced = reduce_iterative(&net).expect("reduction should succeed");
    assert_eq!(reduced.report.self_loop_transitions.len(), 1);
    assert_eq!(reduced.constant_value(PlaceIdx(0)), Some(1));
    assert_eq!(reduced.net.transitions.len(), 1);

    let config = ExplorationConfig::new(4);
    assert_eq!(deadlock_verdict(&net, &config), Verdict::True);
}

#[test]
fn test_deadlock_verdict_restores_constant_self_loop() {
    let net = PetriNet {
        name: Some("constant-self-loop".into()),
        places: vec![place("p0")],
        transitions: vec![transition("t_loop", vec![arc(0, 1)], vec![arc(0, 1)])],
        initial_marking: vec![1],
    };

    let reduced = reduce_iterative(&net).expect("reduction should succeed");
    assert_eq!(reduced.report.self_loop_transitions.len(), 1);
    assert_eq!(reduced.constant_value(PlaceIdx(0)), Some(1));
    assert!(reduced.net.transitions.is_empty());

    let config = ExplorationConfig::new(4);
    assert_eq!(deadlock_verdict(&net, &config), Verdict::False);
}

/// Net with one self-loop transition (always fireable) and one normal transition.
/// The self-loop IS quasi-live (it can fire from the initial marking).
/// Without self-loop restoration, the observer would not see it fire and might
/// incorrectly report the wrong transition count.
#[test]
fn test_quasi_liveness_restores_self_loop() {
    // p0(1): self-loop t_loop reads and writes 1 token
    // p0(1) → p1(0): normal transition t_move
    // Both transitions are quasi-live (both can fire at least once).
    let net = PetriNet {
        name: Some("quasi-live-self-loop".into()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            transition("t_loop", vec![arc(0, 1)], vec![arc(0, 1)]),
            transition("t_move", vec![arc(0, 1)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    let reduced = reduce_iterative(&net).expect("reduction should succeed");
    assert_eq!(reduced.report.self_loop_transitions.len(), 1);

    let config = ExplorationConfig::new(100);
    assert_eq!(quasi_liveness_verdict(&net, &config), Verdict::True);
}

/// Net where a self-loop cannot fire (weight > initial marking, no other producer).
/// This self-loop is NOT quasi-live — it can never fire.
#[test]
fn test_quasi_liveness_blocked_self_loop_is_not_quasi_live() {
    // p_big(0): self-loop t_loop reads/writes 5 (cannot fire — needs 5 tokens, has 0)
    // p_live(1) → p_done(0): normal transition t_once (fires once, then dead)
    // The self-loop can never fire, so the net is NOT quasi-live.
    let net = PetriNet {
        name: Some("blocked-self-loop-not-quasi-live".into()),
        places: vec![place("p_big"), place("p_live"), place("p_done")],
        transitions: vec![
            transition("t_loop", vec![arc(0, 5)], vec![arc(0, 5)]),
            transition("t_once", vec![arc(1, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![0, 1, 0],
    };

    let reduced = reduce_iterative(&net).expect("reduction should succeed");
    assert_eq!(reduced.report.self_loop_transitions.len(), 1);

    let config = ExplorationConfig::new(100);
    assert_eq!(quasi_liveness_verdict(&net, &config), Verdict::False);
}

/// Net where a self-loop is always enabled → it should not prevent a TRUE
/// liveness verdict (all transitions fire from every reachable marking).
#[test]
fn test_liveness_restores_self_loop_in_live_net() {
    // Mutex-like net: p_free(1) ↔ p_cs(0) with a self-loop on p_free.
    // t_enter: p_free→p_cs, t_exit: p_cs→p_free, t_loop: p_free↔p_free
    // All three transitions are live (fireable from every reachable marking):
    // State [1,0]: t_enter enabled, t_loop enabled; t_exit reachable via t_enter
    // State [0,1]: t_exit enabled; t_enter and t_loop reachable via t_exit
    let net = PetriNet {
        name: Some("live-with-self-loop".into()),
        places: vec![place("p_free"), place("p_cs")],
        transitions: vec![
            transition("t_enter", vec![arc(0, 1)], vec![arc(1, 1)]),
            transition("t_exit", vec![arc(1, 1)], vec![arc(0, 1)]),
            transition("t_loop", vec![arc(0, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    let reduced = reduce_iterative(&net).expect("reduction should succeed");
    assert_eq!(reduced.report.self_loop_transitions.len(), 1);

    let config = ExplorationConfig::new(100);
    assert_eq!(liveness_verdict(&net, &config), Verdict::True);
}

/// Net where a self-loop is NOT live (cannot fire from all reachable markings).
/// The self-loop on p_free is disabled when p_free=0 (state [0,1]).
/// Without self-loop restoration, liveness would incorrectly report TRUE.
#[test]
fn test_liveness_self_loop_not_live_from_all_markings() {
    // p_free(1) → p_cs(0), only t_enter (irreversible).
    // t_loop: p_free↔p_free (self-loop, weight 1).
    // State [1,0]: t_enter enabled, t_loop enabled.
    // State [0,1]: neither t_enter nor t_loop enabled — deadlock.
    // Net is NOT live (t_loop cannot fire from [0,1]).
    let net = PetriNet {
        name: Some("self-loop-not-live".into()),
        places: vec![place("p_free"), place("p_cs")],
        transitions: vec![
            transition("t_enter", vec![arc(0, 1)], vec![arc(1, 1)]),
            transition("t_loop", vec![arc(0, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    let reduced = reduce_iterative(&net).expect("reduction should succeed");
    assert_eq!(reduced.report.self_loop_transitions.len(), 1);

    let config = ExplorationConfig::new(100);
    assert_eq!(liveness_verdict(&net, &config), Verdict::False);
}

/// Self-loop on a place that would be LP-redundant — now fixed by
/// protecting self-loop-touching places from LP-redundancy.
///
/// Net: p0(4), p1(2)
///   t_loop: p0(2) → p0(2)  [self-loop on p0, weight 2]
///   t_add:  p1(2) → p0(2)  [adds tokens to p0]
///
/// P-invariant: p0 + p1 = 6. Without protection, p0 would be LP-redundant
/// (never constrains t_add). With the fix, p0 is protected because t_loop
/// touches it, so it survives in the reduced net and the self-loop is
/// correctly restored.
///
/// Expected: FALSE (self-loop at [p1=0, p0=6] prevents deadlock).
#[test]
fn test_deadlock_self_loop_on_lp_redundant_place_fixed() {
    let net = PetriNet {
        name: Some("lp-redundant-self-loop".into()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            transition("t_loop", vec![arc(0, 2)], vec![arc(0, 2)]),
            transition("t_add", vec![arc(1, 2)], vec![arc(0, 2)]),
        ],
        initial_marking: vec![4, 2],
    };

    let reduced = reduce_iterative(&net).expect("reduction should succeed");
    assert_eq!(
        reduced.report.self_loop_transitions.len(),
        1,
        "t_loop should be identified as a self-loop"
    );

    // FIX: p0 is now protected from LP-redundancy because it touches
    // the self-loop transition t_loop. It survives in the reduced net.
    assert!(
        reduced.place_map[0].is_some(),
        "p0 should survive (protected from LP-redundancy by self-loop)"
    );

    let config = ExplorationConfig::new(100);
    // FIXED: self-loop correctly restored via place_map → no deadlock.
    // State [p1=0, p0=6]: t_loop needs p0>=2, p0=6 → self-loop enabled.
    assert_eq!(
        deadlock_verdict(&net, &config),
        Verdict::False,
        "self-loop on p0 prevents deadlock (p0=6 >= weight=2)"
    );
}

/// Self-loop touching two places: one constant (p_const) and one active (p_active).
/// The constant place is removed during reduction, the active one stays.
/// The self-loop must handle the mixed case: drop the constant-place arc
/// (sufficient tokens) and remap the active-place arc.
///
/// Net: p_const(3), p_active(1), p_sink(0)
///   t_loop:   p_const(1), p_active(1) → p_const(1), p_active(1) [self-loop on both]
///   t_consume: p_active(1) → p_sink(1)
///
/// p_const has zero net effect from both transitions → constant (value 3).
/// After reduction: p_const removed, t_loop removed.
/// Reduced: p_active(1), p_sink(0), t_consume: p_active(1) → p_sink(1).
///
/// State [1,0]: t_consume fires → [0,1]. Self-loop needs p_active(1) but p_active=0.
/// Expected: TRUE (deadlock reachable at [0,1]).
#[test]
fn test_deadlock_self_loop_mixed_constant_and_active_places() {
    let net = PetriNet {
        name: Some("mixed-constant-active-self-loop".into()),
        places: vec![place("p_const"), place("p_active"), place("p_sink")],
        transitions: vec![
            transition(
                "t_loop",
                vec![arc(0, 1), arc(1, 1)],
                vec![arc(0, 1), arc(1, 1)],
            ),
            transition("t_consume", vec![arc(1, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![3, 1, 0],
    };

    let reduced = reduce_iterative(&net).expect("reduction should succeed");
    assert_eq!(reduced.report.self_loop_transitions.len(), 1);
    assert_eq!(
        reduced.constant_value(PlaceIdx(0)),
        Some(3),
        "p_const should be constant"
    );

    let config = ExplorationConfig::new(100);
    assert_eq!(deadlock_verdict(&net, &config), Verdict::True);
}

/// Self-loop on a place that coexists with a dead transition.
///
/// Net: p_dead(0), p_shared(2), p_sink(0)
///   t_dead: p_dead(1) → p_shared(1)  [dead: needs p_dead(1) but p_dead=0]
///   t_loop: p_shared(1) → p_shared(1) [self-loop on p_shared]
///   t_sink: p_shared(1) → p_sink(1)
///
/// t_dead is dead → removed. p_dead cascade-isolated → removed.
/// t_loop is self-loop → removed. p_shared stays in the reduced net
/// (touched by t_sink). Self-loop restoration finds p_shared in place_map.
///
/// States: [2,0] → [1,1] → [0,2]. Self-loop needs p_shared≥1.
/// At [0,2]: self-loop disabled. Expected: TRUE (deadlock reachable).
#[test]
fn test_deadlock_self_loop_after_dead_transition_removal() {
    let net = PetriNet {
        name: Some("self-loop-with-dead-transition".into()),
        places: vec![place("p_dead"), place("p_shared"), place("p_sink")],
        transitions: vec![
            transition("t_dead", vec![arc(0, 1)], vec![arc(1, 1)]),
            transition("t_loop", vec![arc(1, 1)], vec![arc(1, 1)]),
            transition("t_sink", vec![arc(1, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![0, 2, 0],
    };

    let reduced = reduce_iterative(&net).expect("reduction should succeed");
    assert_eq!(reduced.report.self_loop_transitions.len(), 1);

    // p_dead should be removed (cascade-isolated after dead transition removal).
    assert_eq!(reduced.place_map[0], None, "p_dead should be removed");
    // p_shared stays in the reduced net.
    assert!(reduced.place_map[1].is_some(), "p_shared should survive");

    let config = ExplorationConfig::new(100);
    assert_eq!(
        deadlock_verdict(&net, &config),
        Verdict::True,
        "self-loop needs p_shared(1) which reaches 0 → deadlock reachable"
    );
}

/// Self-loop on LP-redundant place — now fixed by protecting self-loop
/// places from LP-redundancy.
///
/// The self-loop IS quasi-live (can fire from initial marking where
/// p0=4 >= weight=4). p0 is protected from LP-redundancy → self-loop
/// correctly restored → quasi-liveness TRUE.
#[test]
fn test_quasi_liveness_self_loop_on_lp_redundant_place_fixed() {
    let net = PetriNet {
        name: Some("lp-redundant-quasi-live".into()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            transition("t_loop", vec![arc(0, 4)], vec![arc(0, 4)]),
            transition("t_add", vec![arc(1, 4)], vec![arc(0, 4)]),
        ],
        initial_marking: vec![4, 4],
    };

    let reduced = reduce_iterative(&net).expect("reduction should succeed");
    assert_eq!(reduced.report.self_loop_transitions.len(), 1);

    let config = ExplorationConfig::new(100);
    // FIXED: p0 protected from LP-redundancy → self-loop restored → quasi-live.
    assert_eq!(
        quasi_liveness_verdict(&net, &config),
        Verdict::True,
        "self-loop IS quasi-live (p0=4 >= weight=4)"
    );
}

/// Verify single-round reduce captures the self-loop transition without
/// iterative reduction. Baseline sanity check.
#[test]
fn test_single_round_reduce_captures_self_loop() {
    let net = PetriNet {
        name: Some("single-round-self-loop".into()),
        places: vec![place("p0")],
        transitions: vec![transition("t_loop", vec![arc(0, 1)], vec![arc(0, 1)])],
        initial_marking: vec![1],
    };

    let reduced = reduce(&net);
    assert_eq!(
        reduced.report.self_loop_transitions,
        vec![crate::petri_net::TransitionIdx(0)],
        "single-round reduce should identify self-loop"
    );
    assert!(
        reduced.net.transitions.is_empty(),
        "self-loop should be removed from reduced net"
    );
}

#[test]
fn test_single_round_reduce_keeps_self_loop_places_out_of_parallel_merge() {
    let net = PetriNet {
        name: Some("self-loop-parallel-protected".into()),
        places: vec![place("p0"), place("p1"), place("p_aux")],
        transitions: vec![
            transition(
                "t_loop",
                vec![arc(0, 1), arc(1, 1)],
                vec![arc(0, 1), arc(1, 1)],
            ),
            transition("t_consume", vec![arc(0, 1), arc(1, 1)], vec![arc(2, 1)]),
            transition("t_restore", vec![arc(2, 1)], vec![arc(0, 1), arc(1, 1)]),
        ],
        initial_marking: vec![1, 1, 1],
    };

    let reduced = reduce(&net);
    assert_eq!(
        reduced.report.self_loop_transitions.len(),
        1,
        "t_loop should still be recognized as a self-loop"
    );
    assert!(
        reduced.report.parallel_places.is_empty(),
        "self-loop-touched places must not be merged by Rule B"
    );

    let p0 = reduced.place_map[0].expect("p0 should survive reduction");
    let p1 = reduced.place_map[1].expect("p1 should survive reduction");
    assert_ne!(
        p0, p1,
        "self-loop-touched places should remain distinct, not canonical/duplicate aliases"
    );
}
