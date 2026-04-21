// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for LP state-equation reachability pre-seeding.

use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
use crate::property_xml::PathQuantifier;
use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};

use super::super::reachability::PropertyTracker;
use super::run_lp_seeding;

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

/// Token-conserving net: p0(3) → t0 → p1. Sum p0+p1 = 3 always.
fn conserving_net() -> PetriNet {
    PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![3, 0],
    }
}

fn tracker(id: &str, quantifier: PathQuantifier, predicate: ResolvedPredicate) -> PropertyTracker {
    PropertyTracker {
        id: id.to_string(),
        quantifier,
        predicate,
        verdict: None,
        resolved_by: None,
        flushed: false,
    }
}

#[test]
fn test_ef_infeasible_target_seeds_false() {
    let net = conserving_net();
    // EF(p0 >= 5): impossible since p0 + p1 = 3 and p1 >= 0 => p0 <= 3.
    let mut trackers = vec![tracker(
        "prop-00",
        PathQuantifier::EF,
        ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(5),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
        ),
    )];

    run_lp_seeding(&net, &mut trackers);
    assert_eq!(
        trackers[0].verdict,
        Some(false),
        "EF of infeasible target should be FALSE"
    );
}

#[test]
fn test_ef_feasible_target_stays_unresolved() {
    let net = conserving_net();
    // EF(p1 >= 2): reachable by firing t0 twice.
    let mut trackers = vec![tracker(
        "prop-00",
        PathQuantifier::EF,
        ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(2),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
        ),
    )];

    run_lp_seeding(&net, &mut trackers);
    assert_eq!(
        trackers[0].verdict, None,
        "LP-feasible EF should stay unresolved"
    );
}

#[test]
fn test_ag_conjunction_seeds_true() {
    let net = conserving_net();
    // AG(p0 <= 3 AND p1 <= 3): always true since p0 + p1 = 3.
    // Violating atoms: p0 >= 4 and p1 >= 4 — both LP-infeasible.
    let mut trackers = vec![tracker(
        "prop-00",
        PathQuantifier::AG,
        ResolvedPredicate::And(vec![
            ResolvedPredicate::IntLe(
                ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
                ResolvedIntExpr::Constant(3),
            ),
            ResolvedPredicate::IntLe(
                ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
                ResolvedIntExpr::Constant(3),
            ),
        ]),
    )];

    run_lp_seeding(&net, &mut trackers);
    assert_eq!(
        trackers[0].verdict,
        Some(true),
        "AG of invariant conjunction should be TRUE"
    );
}

#[test]
fn test_ag_violable_stays_unresolved() {
    let net = conserving_net();
    // AG(p0 <= 1): false since initial marking has p0 = 3.
    // But LP can't prove this false — it's the BFS/witness side.
    // The violating atom p0 >= 2 is LP-feasible, so AG stays unresolved.
    let mut trackers = vec![tracker(
        "prop-00",
        PathQuantifier::AG,
        ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
            ResolvedIntExpr::Constant(1),
        ),
    )];

    run_lp_seeding(&net, &mut trackers);
    assert_eq!(
        trackers[0].verdict, None,
        "AG with LP-feasible violation should stay unresolved"
    );
}

#[test]
fn test_non_amenable_formula_stays_unresolved() {
    let net = conserving_net();
    // EF(IsFireable(t0)): not LP-amenable, should be skipped.
    let mut trackers = vec![tracker(
        "prop-00",
        PathQuantifier::EF,
        ResolvedPredicate::IsFireable(vec![crate::petri_net::TransitionIdx(0)]),
    )];

    run_lp_seeding(&net, &mut trackers);
    assert_eq!(
        trackers[0].verdict, None,
        "Non-amenable formula should stay unresolved"
    );
}

#[test]
fn test_already_resolved_trackers_skipped() {
    let net = conserving_net();
    let mut trackers = vec![tracker(
        "prop-00",
        PathQuantifier::EF,
        ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(5),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
        ),
    )];
    // Pre-seed a verdict (as if BMC already resolved it).
    trackers[0].verdict = Some(true);

    run_lp_seeding(&net, &mut trackers);
    assert_eq!(
        trackers[0].verdict,
        Some(true),
        "Pre-seeded verdict should not change"
    );
}

#[test]
fn test_mixed_trackers_partial_seeding() {
    let net = conserving_net();
    let mut trackers = vec![
        // EF(p0 >= 5): infeasible → FALSE
        tracker(
            "prop-00",
            PathQuantifier::EF,
            ResolvedPredicate::IntLe(
                ResolvedIntExpr::Constant(5),
                ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
            ),
        ),
        // EF(p1 >= 2): feasible → stays None
        tracker(
            "prop-01",
            PathQuantifier::EF,
            ResolvedPredicate::IntLe(
                ResolvedIntExpr::Constant(2),
                ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
            ),
        ),
        // EF(Or(...)): non-amenable → stays None
        tracker(
            "prop-02",
            PathQuantifier::EF,
            ResolvedPredicate::Or(vec![ResolvedPredicate::True]),
        ),
    ];

    run_lp_seeding(&net, &mut trackers);
    assert_eq!(trackers[0].verdict, Some(false));
    assert_eq!(trackers[1].verdict, None);
    assert_eq!(trackers[2].verdict, None);
}

#[test]
fn test_ag_with_token_rhs_seeds_true() {
    let net = conserving_net();
    // AG(p0 <= p0 + p1): always true because p1 >= 0 in every reachable marking.
    let mut trackers = vec![tracker(
        "prop-00",
        PathQuantifier::AG,
        ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0), PlaceIdx(1)]),
        ),
    )];

    run_lp_seeding(&net, &mut trackers);
    assert_eq!(
        trackers[0].verdict,
        Some(true),
        "Token-vs-token AG invariant should be proven by strict LP violation"
    );
}

#[test]
fn test_ag_with_token_rhs_feasible_violation_stays_unresolved() {
    let net = conserving_net();
    // AG(p0 <= p1) is false at the initial marking, so LP must not seed TRUE.
    let mut trackers = vec![tracker(
        "prop-00",
        PathQuantifier::AG,
        ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
        ),
    )];

    run_lp_seeding(&net, &mut trackers);
    assert_eq!(
        trackers[0].verdict, None,
        "LP-feasible token-vs-token violation must stay unresolved"
    );
}
