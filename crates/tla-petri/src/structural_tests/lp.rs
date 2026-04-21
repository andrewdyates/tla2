// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{arc, place, trans, PetriNet};
use crate::structural::{lp_dead_transition, lp_deadlock_free};

/// Conserving net: p0(3) -t0-> p1, p1 -t1-> p0.
/// Token sum = 3 always. Both transitions always have input >= 1 when
/// the other place has tokens. But NOT always enabled: p0 can be 0 or p1 can be 0.
fn conserving_cycle() -> PetriNet {
    PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![3, 0],
    }
}

/// Net with a source transition (no inputs) — always enabled.
fn source_transition_net() -> PetriNet {
    PetriNet {
        name: None,
        places: vec![place("p0")],
        transitions: vec![trans("t_source", vec![], vec![arc(0, 1)])],
        initial_marking: vec![0],
    }
}

/// Net where p0 has LP upper bound 1 but t0 requires weight 2.
/// t0 is dead (can never fire). p0(1) conserved: p0 + p1 = 1.
fn dead_transition_net() -> PetriNet {
    PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t_live", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_dead", vec![arc(1, 2)], vec![arc(0, 2)]),
        ],
        initial_marking: vec![1, 0],
    }
}

/// Mutual exclusion: 2 processes competing for 1 mutex.
/// p_mutex(1) + p_idle_a(1) + p_idle_b(1).
/// Non-free-choice (2 transitions share p_mutex as input).
fn mutual_exclusion() -> PetriNet {
    PetriNet {
        name: None,
        places: vec![
            place("p_mutex"),  // 0
            place("p_idle_a"), // 1
            place("p_cs_a"),   // 2
            place("p_idle_b"), // 3
            place("p_cs_b"),   // 4
        ],
        transitions: vec![
            // acquire_a: p_mutex + p_idle_a -> p_cs_a
            trans("acquire_a", vec![arc(0, 1), arc(1, 1)], vec![arc(2, 1)]),
            // release_a: p_cs_a -> p_mutex + p_idle_a
            trans("release_a", vec![arc(2, 1)], vec![arc(0, 1), arc(1, 1)]),
            // acquire_b: p_mutex + p_idle_b -> p_cs_b
            trans("acquire_b", vec![arc(0, 1), arc(3, 1)], vec![arc(4, 1)]),
            // release_b: p_cs_b -> p_mutex + p_idle_b
            trans("release_b", vec![arc(4, 1)], vec![arc(0, 1), arc(3, 1)]),
        ],
        initial_marking: vec![1, 1, 0, 1, 0],
    }
}

#[test]
fn test_lp_deadlock_free_source_transition() {
    // Source transition has no inputs → always enabled → deadlock-free.
    let net = source_transition_net();
    assert_eq!(lp_deadlock_free(&net), Some(true));
}

#[test]
fn test_lp_deadlock_free_conserving_cycle_inconclusive() {
    // Both transitions can be disabled (when their input place is 0).
    // LP can't prove either is always enabled since the LP allows m(p0)=0.
    let net = conserving_cycle();
    assert_eq!(lp_deadlock_free(&net), None);
}

#[test]
fn test_lp_deadlock_free_mutex_inconclusive() {
    // Non-free-choice mutual exclusion. No transition is always enabled.
    // LP should return None (inconclusive).
    let net = mutual_exclusion();
    assert_eq!(lp_deadlock_free(&net), None);
}

#[test]
fn test_lp_dead_transition_found() {
    // t_dead requires 2 tokens from p1, but p1's LP upper bound is 1.
    let net = dead_transition_net();
    assert_eq!(lp_dead_transition(&net), Some(false));
}

#[test]
fn test_lp_dead_transition_none_when_all_can_fire() {
    // Conserving cycle: both transitions can fire → no dead transitions.
    let net = conserving_cycle();
    assert_eq!(lp_dead_transition(&net), None);
}

#[test]
fn test_lp_dead_transition_none_for_source() {
    // Source transition has no inputs → can always fire.
    let net = source_transition_net();
    assert_eq!(lp_dead_transition(&net), None);
}

#[test]
fn test_lp_deadlock_free_empty_transitions() {
    // Net with no transitions — always deadlocked, LP returns None
    // (not Some(true)) because there's no transition to prove always-enabled.
    let net = PetriNet {
        name: None,
        places: vec![place("p0")],
        transitions: vec![],
        initial_marking: vec![1],
    };
    assert_eq!(lp_deadlock_free(&net), None);
}

#[test]
fn test_lp_deadlock_free_unbounded_always_enabled() {
    // p0(1) -t0(needs 1)-> p0(gets 2). Net effect: +1 to p0.
    // p0 starts at 1, grows unboundedly. t0 always has input >= 1.
    // LP should prove t0 always enabled (LP lower bound of p0 is 1,
    // since p0 = 1 + x and x >= 0).
    let net = PetriNet {
        name: None,
        places: vec![place("p0")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(0, 2)])],
        initial_marking: vec![1],
    };
    assert_eq!(lp_deadlock_free(&net), Some(true));
}
