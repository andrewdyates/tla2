// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::buchi::LtlNnf;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionIdx, TransitionInfo};
use crate::reduction::ReducedNet;
use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};

use super::{formula_contains_next, ltl_visible_reduced_transitions};

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

/// Net with two independent subnets:
/// Subnet A: p0 -> t0 -> p1 -> t1 -> p0  (cycle, places 0-1, transitions 0-1)
/// Subnet B: p2 -> t2 -> p3              (chain, places 2-3, transition 2)
fn two_subnet_net() -> PetriNet {
    PetriNet {
        name: Some("two-subnets".to_string()),
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
            trans("t2", vec![arc(2, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![1, 0, 1, 0],
    }
}

#[test]
fn test_formula_contains_next_positive() {
    let formula = LtlNnf::Next(Box::new(LtlNnf::Atom(0)));
    assert!(formula_contains_next(&formula));
}

#[test]
fn test_formula_contains_next_nested() {
    let formula = LtlNnf::Until(
        Box::new(LtlNnf::True),
        Box::new(LtlNnf::Next(Box::new(LtlNnf::Atom(0)))),
    );
    assert!(formula_contains_next(&formula));
}

#[test]
fn test_formula_contains_next_negative() {
    let formula = LtlNnf::Release(Box::new(LtlNnf::False), Box::new(LtlNnf::Atom(0)));
    assert!(!formula_contains_next(&formula));
}

#[test]
fn test_visible_cardinality_only_touches_referenced_places() {
    let net = two_subnet_net();
    let reduced = ReducedNet::identity(&net);

    // Atom referencing only p0 (in subnet A).
    let atoms = vec![ResolvedPredicate::IntLe(
        ResolvedIntExpr::Constant(1),
        ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
    )];

    let visible = ltl_visible_reduced_transitions(&atoms, &reduced);
    let visible_set: std::collections::HashSet<_> = visible.iter().copied().collect();

    // t0 and t1 touch p0 → visible. t2 does not touch p0 → invisible.
    assert!(visible_set.contains(&TransitionIdx(0)), "t0 touches p0");
    assert!(visible_set.contains(&TransitionIdx(1)), "t1 touches p0");
    assert!(
        !visible_set.contains(&TransitionIdx(2)),
        "t2 does not touch p0"
    );
}

#[test]
fn test_visible_fireability_includes_shared_place_transitions() {
    let net = two_subnet_net();
    let reduced = ReducedNet::identity(&net);

    // IsFireable atom referencing t0 (inputs: p0, outputs: p1).
    let atoms = vec![ResolvedPredicate::IsFireable(vec![TransitionIdx(0)])];

    let visible = ltl_visible_reduced_transitions(&atoms, &reduced);
    let visible_set: std::collections::HashSet<_> = visible.iter().copied().collect();

    // t0 is the referenced transition → visible.
    // t1 shares p0 (input of t0) and p1 (output of t0) → visible.
    // t2 shares no places with t0 → invisible.
    assert!(visible_set.contains(&TransitionIdx(0)), "t0 is referenced");
    assert!(
        visible_set.contains(&TransitionIdx(1)),
        "t1 shares places with t0"
    );
    assert!(!visible_set.contains(&TransitionIdx(2)), "t2 independent");
}

#[test]
fn test_visible_all_when_formula_touches_all_places() {
    let net = two_subnet_net();
    let reduced = ReducedNet::identity(&net);

    // Atom referencing p0 and p2 (both subnets).
    let atoms = vec![ResolvedPredicate::IntLe(
        ResolvedIntExpr::Constant(1),
        ResolvedIntExpr::TokensCount(vec![PlaceIdx(0), PlaceIdx(2)]),
    )];

    let visible = ltl_visible_reduced_transitions(&atoms, &reduced);
    // All 3 transitions touch one of {p0, p2}.
    assert_eq!(visible.len(), 3);
}

#[test]
fn test_visible_empty_atoms_returns_no_visible() {
    let net = two_subnet_net();
    let reduced = ReducedNet::identity(&net);

    // True atom references no places or transitions.
    let atoms = vec![ResolvedPredicate::True];

    let visible = ltl_visible_reduced_transitions(&atoms, &reduced);
    assert!(visible.is_empty());
}
