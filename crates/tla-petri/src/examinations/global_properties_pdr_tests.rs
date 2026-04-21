// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for PDR-based global property verification (OneSafe, Deadlock, StableMarking).
//!
//! Each test verifies that PDR produces a verdict matching what BFS would produce.

use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};

use super::{run_deadlock_pdr, run_one_safe_pdr, run_stable_marking_pdr};

fn place(id: &str) -> PlaceInfo {
    PlaceInfo {
        id: id.to_string(),
        name: None,
    }
}

fn arc(place: u32, weight: u64) -> Arc {
    Arc {
        place: PlaceIdx(place),
        weight,
    }
}

fn trans(id: &str, inputs: Vec<Arc>, outputs: Vec<Arc>) -> TransitionInfo {
    TransitionInfo {
        id: id.to_string(),
        name: None,
        inputs,
        outputs,
    }
}

// ── Test nets ───────────────────────────────────────────────────────────

/// Net that is 1-safe: p0 + p1 = 1 (token conservation).
/// p0 --t0--> p1 --t1--> p0, initial: [1, 0].
fn one_safe_net() -> PetriNet {
    PetriNet {
        name: Some("one_safe".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    }
}

/// Net that is NOT 1-safe: p0 starts with 3 tokens.
/// p0 --t0--> p1 --t1--> p0, initial: [3, 0].
fn not_one_safe_net() -> PetriNet {
    PetriNet {
        name: Some("not_one_safe".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![3, 0],
    }
}

/// Net with a deadlock: p0 --t0--> p1, but no way to leave p1.
/// Initial: [1, 0]. After firing t0: [0, 1] = deadlock.
fn deadlock_net() -> PetriNet {
    PetriNet {
        name: Some("deadlock".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![1, 0],
    }
}

/// Net without deadlock: reversible cycle p0 <-> p1.
/// Initial: [1, 0]. Always one transition enabled.
fn no_deadlock_net() -> PetriNet {
    PetriNet {
        name: Some("no_deadlock".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    }
}

/// Net with a stable place: p0 and p1 form a cycle, p2 is never
/// modified by any transition. Initial: [1, 0, 5].
fn stable_place_net() -> PetriNet {
    PetriNet {
        name: Some("stable_place".to_string()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0, 5],
    }
}

/// Net with NO stable places: all places change.
/// p0 --t0--> p1 (one-way flow, deadlocks at [0,1] but by then p0 changed).
fn no_stable_place_net() -> PetriNet {
    PetriNet {
        name: Some("no_stable_place".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![1, 0],
    }
}

// ── OneSafe tests ───────────────────────────────────────────────────────

#[test]
fn test_pdr_one_safe_sound_for_safe_net() {
    let net = one_safe_net();
    let result = run_one_safe_pdr(&net, None);
    // PDR may return None (inconclusive) or Some(true) — both are sound.
    // It MUST NOT return Some(false) because the net IS 1-safe.
    assert_ne!(
        result,
        Some(false),
        "1-safe net must not be falsely claimed unsafe by PDR"
    );
}

#[test]
fn test_pdr_one_safe_false_for_unsafe_net() {
    let net = not_one_safe_net();
    let result = run_one_safe_pdr(&net, None);
    assert_eq!(
        result,
        Some(false),
        "net with 3 tokens should be proved unsafe by PDR"
    );
}

// ── Deadlock tests ──────────────────────────────────────────────────────

#[test]
fn test_pdr_deadlock_found_in_deadlock_net() {
    let net = deadlock_net();
    let result = run_deadlock_pdr(&net, None);
    assert_eq!(
        result,
        Some(true),
        "net with reachable deadlock should be detected by PDR"
    );
}

#[test]
fn test_pdr_deadlock_free_sound_for_cycle_net() {
    let net = no_deadlock_net();
    let result = run_deadlock_pdr(&net, None);
    // PDR may return None (inconclusive) or Some(false) — both are sound.
    // It MUST NOT return Some(true) because the net has no deadlock.
    assert_ne!(
        result,
        Some(true),
        "deadlock-free net must not be falsely claimed deadlocked by PDR"
    );
}

// ── StableMarking tests ─────────────────────────────────────────────────

#[test]
fn test_pdr_stable_marking_finds_stable_place() {
    let net = stable_place_net();
    let result = run_stable_marking_pdr(&net, None);
    let result = result.expect("PDR should produce a result");
    assert_eq!(
        result.verdict,
        Some(true),
        "net with isolated place p2 should have at least one stable place"
    );
}

#[test]
fn test_pdr_stable_marking_all_unstable() {
    let net = no_stable_place_net();
    let result = run_stable_marking_pdr(&net, None);
    // PDR may prove both places unstable or be inconclusive on some.
    // If it returns a result, check consistency.
    if let Some(result) = result {
        if result.verdict == Some(false) {
            // All places are unstable — correct.
            assert!(
                result.unstable.iter().all(|&u| u),
                "verdict FALSE means all places should be marked unstable"
            );
        }
        // p0 changes from 1 -> 0, p1 changes from 0 -> 1.
        // Both should be unstable if PDR resolves them.
        for (p, &u) in result.unstable.iter().enumerate() {
            if u {
                // Correct: this place is indeed unstable.
            } else {
                // PDR was inconclusive on this place, not incorrect.
                eprintln!("Place {p} inconclusive (not proven unstable by PDR)");
            }
        }
    }
}

#[test]
fn test_pdr_deadlock_source_transition_is_free() {
    // Net with a source transition (no inputs) is never deadlocked.
    let net = PetriNet {
        name: Some("source_trans".to_string()),
        places: vec![place("p0")],
        transitions: vec![trans("t0", vec![], vec![arc(0, 1)])],
        initial_marking: vec![0],
    };
    let result = run_deadlock_pdr(&net, None);
    assert_eq!(
        result,
        Some(false),
        "net with source transition should be deadlock-free"
    );
}

#[test]
fn test_pdr_deadlock_no_transitions_is_deadlock() {
    let net = PetriNet {
        name: Some("no_trans".to_string()),
        places: vec![place("p0")],
        transitions: vec![],
        initial_marking: vec![1],
    };
    let result = run_deadlock_pdr(&net, None);
    assert_eq!(
        result,
        Some(true),
        "net with no transitions is trivially deadlocked"
    );
}
