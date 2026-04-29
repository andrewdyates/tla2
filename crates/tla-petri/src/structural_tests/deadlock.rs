// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_simple_deadlock_free_mutex() {
    // Mutex pattern: p0(1) -> t0 -> p1, p1 -> t1 -> p0.
    // Token cycles, no deadlock.
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };
    assert_eq!(structural_deadlock_free(&net), Some(true));
}

#[test]
fn test_deadlock_net() {
    // p0(1) -> t0 -> p1. No way back. Deadlocks after t0 fires.
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![1, 0],
    };
    // {p1} is a siphon (no transition produces into p1... wait, t0 does).
    // Actually: {p0} is not a siphon. {p1} - t0 produces into p1, and
    // t0's inputs are {p0} which is NOT in {p1}. So {p1} is not a siphon.
    // {p0} - t0 consumes from p0, but no transition produces into {p0}.
    // Wait, t0's outputs are {p1}, not p0. So {p0}: is it a siphon?
    // Siphon: for all t: t* intersect S != empty -> *t intersect S != empty.
    // No transition produces into {p0}, so the condition is vacuously true.
    // {p0} is a siphon!
    // Wait, t0 doesn't produce into {p0}. But is there a transition that
    // does? No. So {p0} is a siphon (vacuously - no transition
    // produces into it). But {p0} has initial token 1, so the siphon is
    // initially marked. However, a siphon once empty stays empty -
    // but it's currently marked, so we need a TRAP within it.
    // {p0}: is it a trap? for all t: *t intersect T != empty -> t* intersect T != empty.
    // t0 consumes from p0 (*t0 intersect {p0} != empty) but t0 produces into p1
    // (t0* intersect {p0} = empty). So {p0} is NOT a trap.
    // Therefore {p0} is a siphon without a marked trap -> vulnerability.
    let result = structural_deadlock_free(&net);
    assert_eq!(result, Some(false));
}

#[test]
fn test_producer_consumer_deadlock_free() {
    // Producer: p_buf(5) -> t_produce -> p_item, p_item -> t_consume -> p_buf
    // Token cycles between buffer and item. Deadlock-free.
    let net = PetriNet {
        name: None,
        places: vec![place("p_buf"), place("p_item")],
        transitions: vec![
            trans("t_produce", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_consume", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![5, 0],
    };
    assert_eq!(structural_deadlock_free(&net), Some(true));
}

#[test]
fn test_empty_transition_net_is_deadlocked() {
    // No transitions -> initial marking is always a deadlock.
    let net = PetriNet {
        name: None,
        places: vec![place("p0")],
        transitions: vec![],
        initial_marking: vec![1],
    };
    assert_eq!(structural_deadlock_free(&net), Some(false));
}

#[test]
fn test_dining_philosophers_2() {
    // 2 philosophers, 2 forks. Classic deadlock-prone net.
    // p0=phil1_thinking(1), p1=phil2_thinking(1),
    // p2=fork1(1), p3=fork2(1),
    // p4=phil1_eating(0), p5=phil2_eating(0)
    // t0: phil1 picks up forks: p0+p2+p3 -> p4
    // t1: phil1 puts down forks: p4 -> p0+p2+p3
    // t2: phil2 picks up forks: p1+p2+p3 -> p5
    // t3: phil2 puts down forks: p5 -> p1+p2+p3
    // Actually this is the non-deadlocking version (each philosopher
    // atomically picks up both forks). The deadlocking version would
    // have separate "pick left" and "pick right" transitions.
    // This version is deadlock-free.
    let net = PetriNet {
        name: None,
        places: vec![
            place("phil1_think"),
            place("phil2_think"),
            place("fork1"),
            place("fork2"),
            place("phil1_eat"),
            place("phil2_eat"),
        ],
        transitions: vec![
            trans(
                "phil1_pickup",
                vec![arc(0, 1), arc(2, 1), arc(3, 1)],
                vec![arc(4, 1)],
            ),
            trans(
                "phil1_putdown",
                vec![arc(4, 1)],
                vec![arc(0, 1), arc(2, 1), arc(3, 1)],
            ),
            trans(
                "phil2_pickup",
                vec![arc(1, 1), arc(2, 1), arc(3, 1)],
                vec![arc(5, 1)],
            ),
            trans(
                "phil2_putdown",
                vec![arc(5, 1)],
                vec![arc(1, 1), arc(2, 1), arc(3, 1)],
            ),
        ],
        initial_marking: vec![1, 1, 1, 1, 0, 0],
    };
    // This net is deadlock-free, but it is NOT free-choice (fork places
    // are shared between philosophers), so the siphon/trap shortcut
    // does not apply and returns None.
    assert_eq!(structural_deadlock_free(&net), None);
}
