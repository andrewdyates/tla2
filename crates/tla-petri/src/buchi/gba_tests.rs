// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{build_gba, GbaStateId, LtlNnf};

fn waiting_state(gba: &super::Gba) -> GbaStateId {
    (0..gba.num_states)
        .find(|state| !gba.acceptance[0].contains(state))
        .expect("expected a waiting state")
}

fn done_state(gba: &super::Gba) -> GbaStateId {
    *gba.acceptance[0]
        .iter()
        .next()
        .expect("expected an accepting state")
}

#[test]
fn test_gba_atom_only() {
    let gba = build_gba(&LtlNnf::Atom(0));

    assert_eq!(gba.num_states, 1);
    assert!(gba.acceptance.is_empty());
    assert_eq!(gba.initial_transitions.len(), 1);
    assert_eq!(gba.initial_transitions[0].pos_atoms, vec![0]);
    assert_eq!(gba.initial_transitions[0].successor, 0);
    assert_eq!(gba.transitions[0].len(), 1);
    assert_eq!(gba.transitions[0][0].successor, 0);
}

#[test]
fn test_gba_until_simple() {
    let formula = LtlNnf::Until(Box::new(LtlNnf::Atom(0)), Box::new(LtlNnf::Atom(1)));
    let gba = build_gba(&formula);
    let waiting = waiting_state(&gba);
    let done = done_state(&gba);

    assert_eq!(gba.num_states, 2);
    assert_eq!(gba.acceptance.len(), 1);
    assert_eq!(gba.acceptance[0].len(), 1);
    assert_ne!(waiting, done);
    assert!(gba
        .initial_transitions
        .iter()
        .any(|transition| transition.pos_atoms == vec![1] && transition.successor == done));
    assert!(gba
        .initial_transitions
        .iter()
        .any(|transition| transition.pos_atoms == vec![0] && transition.successor == waiting));
    assert_eq!(gba.transitions[waiting as usize].len(), 2);
}

#[test]
fn test_gba_release_simple() {
    let formula = LtlNnf::Release(Box::new(LtlNnf::Atom(0)), Box::new(LtlNnf::Atom(1)));
    let gba = build_gba(&formula);

    assert_eq!(gba.num_states, 2);
    assert!(gba.acceptance.is_empty());
    assert_eq!(gba.initial_transitions.len(), 2);
    assert!(gba
        .initial_transitions
        .iter()
        .any(|transition| transition.pos_atoms == vec![1, 0]));
    assert!(gba
        .initial_transitions
        .iter()
        .any(|transition| transition.pos_atoms == vec![1]));
}

#[test]
fn test_gba_globally() {
    let formula = LtlNnf::Release(Box::new(LtlNnf::False), Box::new(LtlNnf::Atom(0)));
    let gba = build_gba(&formula);

    assert_eq!(gba.num_states, 1);
    assert!(gba.acceptance.is_empty());
    assert_eq!(gba.initial_transitions.len(), 1);
    assert_eq!(gba.initial_transitions[0].pos_atoms, vec![0]);
    assert_eq!(gba.initial_transitions[0].successor, 0);
    assert_eq!(gba.transitions[0].len(), 1);
    assert_eq!(gba.transitions[0][0].pos_atoms, vec![0]);
    assert_eq!(gba.transitions[0][0].successor, 0);
}

#[test]
fn test_gba_finally() {
    let formula = LtlNnf::Until(Box::new(LtlNnf::True), Box::new(LtlNnf::Atom(0)));
    let gba = build_gba(&formula);
    let waiting = waiting_state(&gba);
    let done = done_state(&gba);

    assert_eq!(gba.num_states, 2);
    assert_eq!(gba.acceptance.len(), 1);
    assert!(gba
        .initial_transitions
        .iter()
        .any(|transition| transition.pos_atoms == vec![0] && transition.successor == done));
    assert!(gba
        .initial_transitions
        .iter()
        .any(|transition| transition.pos_atoms.is_empty() && transition.successor == waiting));
}

#[test]
fn test_gba_acceptance_condition_marks_done_state_only() {
    let formula = LtlNnf::Until(Box::new(LtlNnf::Atom(0)), Box::new(LtlNnf::Atom(1)));
    let gba = build_gba(&formula);
    let waiting = waiting_state(&gba);
    let done = done_state(&gba);

    assert!(gba.acceptance[0].contains(&done));
    assert!(!gba.acceptance[0].contains(&waiting));
}
