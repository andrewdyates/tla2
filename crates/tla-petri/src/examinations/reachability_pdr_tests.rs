// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for PDR reachability pre-seeding.

use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
use crate::property_xml::PathQuantifier;
use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};

use super::super::reachability::PropertyTracker;
use super::super::reachability::ReachabilityResolutionSource;
use super::run_pdr_seeding;

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

fn three_token_net() -> PetriNet {
    PetriNet {
        name: Some("three_token".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![3, 0],
    }
}

fn simple_net() -> PetriNet {
    PetriNet {
        name: Some("simple".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
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
fn test_pdr_seeds_ag_true_for_inductive_invariant() {
    let net = three_token_net();
    let mut trackers = vec![tracker(
        "prop-00",
        PathQuantifier::AG,
        ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0), PlaceIdx(1)]),
            ResolvedIntExpr::Constant(3),
        ),
    )];

    run_pdr_seeding(&net, &mut trackers, None);
    assert_eq!(trackers[0].verdict, Some(true));
    assert_eq!(
        trackers[0].resolved_by.map(|resolution| resolution.source),
        Some(ReachabilityResolutionSource::Pdr)
    );
}

#[test]
fn test_pdr_seeds_ag_false_for_reachable_counterexample() {
    let net = simple_net();
    let mut trackers = vec![tracker(
        "prop-00",
        PathQuantifier::AG,
        ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
            ResolvedIntExpr::Constant(0),
        ),
    )];

    run_pdr_seeding(&net, &mut trackers, None);
    assert_eq!(trackers[0].verdict, Some(false));
    assert_eq!(
        trackers[0].resolved_by.map(|resolution| resolution.source),
        Some(ReachabilityResolutionSource::Pdr)
    );
}

#[test]
fn test_pdr_seeds_ef_true_when_target_is_reachable() {
    let net = simple_net();
    let mut trackers = vec![tracker(
        "prop-00",
        PathQuantifier::EF,
        ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(1),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
        ),
    )];

    run_pdr_seeding(&net, &mut trackers, None);
    assert_eq!(trackers[0].verdict, Some(true));
    assert_eq!(
        trackers[0].resolved_by.map(|resolution| resolution.source),
        Some(ReachabilityResolutionSource::Pdr)
    );
}

#[test]
fn test_pdr_seeds_ef_false_when_target_is_unreachable() {
    let net = simple_net();
    let mut trackers = vec![tracker(
        "prop-00",
        PathQuantifier::EF,
        ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(2),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
        ),
    )];

    run_pdr_seeding(&net, &mut trackers, None);
    assert_eq!(trackers[0].verdict, Some(false));
    assert_eq!(
        trackers[0].resolved_by.map(|resolution| resolution.source),
        Some(ReachabilityResolutionSource::Pdr)
    );
}

#[test]
fn test_pdr_leaves_preseeded_verdict_unchanged() {
    let net = simple_net();
    let mut trackers = vec![tracker(
        "prop-00",
        PathQuantifier::EF,
        ResolvedPredicate::True,
    )];
    trackers[0].verdict = Some(true);

    run_pdr_seeding(&net, &mut trackers, None);
    assert_eq!(trackers[0].verdict, Some(true));
    assert_eq!(trackers[0].resolved_by, None);
}

#[test]
fn test_pdr_deadline_expiry_leaves_tracker_unresolved() {
    let net = simple_net();
    let mut trackers = vec![tracker(
        "prop-00",
        PathQuantifier::AG,
        ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
            ResolvedIntExpr::Constant(1),
        ),
    )];

    run_pdr_seeding(&net, &mut trackers, Some(std::time::Instant::now()));
    assert_eq!(trackers[0].verdict, None);
    assert_eq!(trackers[0].resolved_by, None);
}
