// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{product_has_accepting_cycle, product_has_accepting_cycle_with_limit, tarjan_product};
use crate::buchi::gba::build_gba;
use crate::buchi::{LtlContext, LtlNnf};
use crate::explorer::{explore_full, ExplorationConfig, ReachabilityGraph};
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};
use crate::scc::tarjan_scc;

fn alternating_net() -> PetriNet {
    PetriNet {
        name: Some("alternating".to_string()),
        places: vec![
            PlaceInfo {
                id: "p0".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "p1".to_string(),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "t0".to_string(),
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
                id: "t1".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![1, 0],
    }
}

fn deadlock_net(initial_marking: Vec<u64>) -> PetriNet {
    PetriNet {
        name: Some("deadlock".to_string()),
        places: initial_marking
            .iter()
            .enumerate()
            .map(|(index, _)| PlaceInfo {
                id: format!("p{index}"),
                name: None,
            })
            .collect(),
        transitions: Vec::new(),
        initial_marking,
    }
}

fn tokens_at_least(place: PlaceIdx, value: u64) -> ResolvedPredicate {
    ResolvedPredicate::IntLe(
        ResolvedIntExpr::Constant(value),
        ResolvedIntExpr::TokensCount(vec![place]),
    )
}

fn normalize_sccs(mut sccs: Vec<Vec<u32>>) -> Vec<Vec<u32>> {
    for scc in &mut sccs {
        scc.sort_unstable();
    }
    sccs.sort_unstable();
    sccs
}

#[test]
fn test_product_trivial_true() {
    let net = alternating_net();
    let full = explore_full(&net, &ExplorationConfig::default());
    let ctx = LtlContext::new(Vec::new(), &full, &net);
    let gba = build_gba(&LtlNnf::True);

    assert_eq!(product_has_accepting_cycle(&gba, &ctx), Some(true));
}

#[test]
fn test_product_trivial_false() {
    let net = deadlock_net(vec![0]);
    let full = explore_full(&net, &ExplorationConfig::default());
    let ctx = LtlContext::new(vec![tokens_at_least(PlaceIdx(0), 1)], &full, &net);
    let gba = build_gba(&LtlNnf::Until(
        Box::new(LtlNnf::True),
        Box::new(LtlNnf::Atom(0)),
    ));

    assert_eq!(product_has_accepting_cycle(&gba, &ctx), Some(false));
}

#[test]
fn test_product_deadlock_self_loop() {
    let net = deadlock_net(vec![1]);
    let full = explore_full(&net, &ExplorationConfig::default());
    let ctx = LtlContext::new(Vec::new(), &full, &net);
    let gba = build_gba(&LtlNnf::True);

    assert_eq!(product_has_accepting_cycle(&gba, &ctx), Some(true));
}

#[test]
fn test_product_acceptance_all_sets() {
    let formula = LtlNnf::And(vec![
        LtlNnf::Until(Box::new(LtlNnf::True), Box::new(LtlNnf::Atom(0))),
        LtlNnf::Until(Box::new(LtlNnf::True), Box::new(LtlNnf::Atom(1))),
    ]);
    let gba = build_gba(&formula);

    let failing_net = deadlock_net(vec![1, 0]);
    let failing_full = explore_full(&failing_net, &ExplorationConfig::default());
    let failing_ctx = LtlContext::new(
        vec![
            tokens_at_least(PlaceIdx(0), 1),
            tokens_at_least(PlaceIdx(1), 1),
        ],
        &failing_full,
        &failing_net,
    );
    assert_eq!(product_has_accepting_cycle(&gba, &failing_ctx), Some(false));

    let passing_net = alternating_net();
    let passing_full = explore_full(&passing_net, &ExplorationConfig::default());
    let passing_ctx = LtlContext::new(
        vec![
            tokens_at_least(PlaceIdx(0), 1),
            tokens_at_least(PlaceIdx(1), 1),
        ],
        &passing_full,
        &passing_net,
    );
    assert_eq!(product_has_accepting_cycle(&gba, &passing_ctx), Some(true));
}

#[test]
fn test_product_duplicate_tarjan_matches_reachability_tarjan() {
    let adj = vec![vec![1], vec![2], vec![0], vec![4], vec![3], vec![]];
    let product_sccs = normalize_sccs(tarjan_product(&adj));
    let graph = ReachabilityGraph {
        adj: adj
            .iter()
            .map(|successors| successors.iter().copied().map(|succ| (succ, 0)).collect())
            .collect(),
        num_states: adj.len() as u32,
        completed: true,
    };
    let graph_sccs = normalize_sccs(tarjan_scc(&graph));

    assert_eq!(product_sccs, graph_sccs);
}

#[test]
fn test_product_size_limit_returns_none_when_limit_exceeded() {
    let net = alternating_net();
    let full = explore_full(&net, &ExplorationConfig::default());
    let ctx = LtlContext::new(Vec::new(), &full, &net);
    let gba = build_gba(&LtlNnf::True);

    assert_eq!(product_has_accepting_cycle_with_limit(&gba, &ctx, 0), None);
}
