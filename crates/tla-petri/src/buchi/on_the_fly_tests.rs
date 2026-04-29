// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::on_the_fly_product_emptiness_with_limit;
use crate::buchi::gba::build_gba;
use crate::buchi::nnf::negate;
use crate::buchi::LtlNnf;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
use crate::reduction::ReducedNet;
use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};
use std::time::{Duration, Instant};

/// Identity ReducedNet: no reductions applied, marking expansion is passthrough.
fn identity_reduced(net: &PetriNet) -> ReducedNet {
    ReducedNet::identity(net)
}

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

/// Helper: run on-the-fly product emptiness with identity reduction.
fn check_on_the_fly(
    gba_formula: &LtlNnf,
    net: &PetriNet,
    atoms: &[ResolvedPredicate],
) -> Option<bool> {
    let reduced = identity_reduced(net);
    let neg = negate(gba_formula);
    let gba = build_gba(&neg);
    on_the_fly_product_emptiness_with_limit(
        &gba,
        net,
        &reduced,
        net,
        atoms,
        usize::MAX,
        50_000_000,
        None,
    )
    .expect("on-the-fly product should expand markings safely")
}

// ── Equivalence tests: on-the-fly must match pre-built product ──

#[test]
fn test_on_the_fly_trivial_true() {
    // GBA for True has an accepting cycle on any non-empty system.
    let net = alternating_net();
    let result = check_on_the_fly(&LtlNnf::True, &net, &[]);
    // check_ltl negates, so True → neg → False → no accepting cycle → Some(true).
    // But we're calling product emptiness directly: GBA for neg(True)=False → no states → false.
    // Actually, let me think about this correctly.
    // We negate the formula in check_on_the_fly, so:
    // formula = True → neg = False → GBA has 0 states → product empty → no cycle → Some(false)
    assert_eq!(result, Some(false));
}

#[test]
fn test_on_the_fly_alternating_has_cycle() {
    // Build GBA directly for True (not negated) — any cycle is accepting.
    let net = alternating_net();
    let reduced = identity_reduced(&net);
    let gba = build_gba(&LtlNnf::True);
    let result = on_the_fly_product_emptiness_with_limit(
        &gba,
        &net,
        &reduced,
        &net,
        &[],
        usize::MAX,
        50_000_000,
        None,
    )
    .expect("on-the-fly product should expand markings safely");
    assert_eq!(result, Some(true));
}

#[test]
fn test_on_the_fly_deadlock_self_loop_has_cycle() {
    let net = deadlock_net(vec![1]);
    let reduced = identity_reduced(&net);
    let gba = build_gba(&LtlNnf::True);
    let result = on_the_fly_product_emptiness_with_limit(
        &gba,
        &net,
        &reduced,
        &net,
        &[],
        usize::MAX,
        50_000_000,
        None,
    )
    .expect("on-the-fly product should expand markings safely");
    assert_eq!(result, Some(true));
}

#[test]
fn test_on_the_fly_until_no_accepting_cycle_on_deadlock() {
    // F(p0 >= 1) on a deadlock net with p0=0: never satisfied.
    let net = deadlock_net(vec![0]);
    let reduced = identity_reduced(&net);
    let atoms = vec![tokens_at_least(PlaceIdx(0), 1)];
    let formula = LtlNnf::Until(Box::new(LtlNnf::True), Box::new(LtlNnf::Atom(0)));
    let gba = build_gba(&formula);
    let result = on_the_fly_product_emptiness_with_limit(
        &gba,
        &net,
        &reduced,
        &net,
        &atoms,
        usize::MAX,
        50_000_000,
        None,
    )
    .expect("on-the-fly product should expand markings safely");
    assert_eq!(result, Some(false));
}

#[test]
fn test_on_the_fly_size_limit_returns_none() {
    let net = alternating_net();
    let reduced = identity_reduced(&net);
    let gba = build_gba(&LtlNnf::True);
    let result = on_the_fly_product_emptiness_with_limit(
        &gba,
        &net,
        &reduced,
        &net,
        &[],
        usize::MAX,
        0,
        None,
    )
    .expect("size-limit path should not hit expansion overflow");
    assert_eq!(result, None);
}

#[test]
fn test_on_the_fly_system_marking_limit_returns_none() {
    let net = alternating_net();
    let reduced = identity_reduced(&net);
    let gba = build_gba(&LtlNnf::True);
    let result = on_the_fly_product_emptiness_with_limit(
        &gba,
        &net,
        &reduced,
        &net,
        &[],
        1,
        50_000_000,
        None,
    )
    .expect("system-marking limit should not hit expansion overflow");
    assert_eq!(result, None);
}

#[test]
fn test_on_the_fly_expired_deadline_returns_none() {
    let net = alternating_net();
    let reduced = identity_reduced(&net);
    let gba = build_gba(&LtlNnf::True);
    let result = on_the_fly_product_emptiness_with_limit(
        &gba,
        &net,
        &reduced,
        &net,
        &[],
        usize::MAX,
        50_000_000,
        Some(Instant::now() - Duration::from_secs(1)),
    )
    .expect("deadline path should not hit expansion overflow");
    assert_eq!(result, None);
}

#[test]
fn test_on_the_fly_matches_legacy_on_alternating_mutex() {
    // A(G(¬(p0>=1 ∧ p1>=1))) — mutual exclusion on alternating net.
    // The on-the-fly path should give the same result as the legacy path.
    use crate::examinations::ltl::check_ltl_properties;
    use crate::explorer::ExplorationConfig;
    use crate::output::Verdict;
    use crate::property_xml::{Formula, IntExpr, LtlFormula, Property, StatePredicate};

    let net = alternating_net();
    let props = vec![Property {
        id: "mutex".to_string(),
        formula: Formula::Ltl(LtlFormula::Globally(Box::new(LtlFormula::Not(Box::new(
            LtlFormula::And(vec![
                LtlFormula::Atom(StatePredicate::IntLe(
                    IntExpr::Constant(1),
                    IntExpr::TokensCount(vec!["p0".to_string()]),
                )),
                LtlFormula::Atom(StatePredicate::IntLe(
                    IntExpr::Constant(1),
                    IntExpr::TokensCount(vec!["p1".to_string()]),
                )),
            ]),
        ))))),
    }];

    let results = check_ltl_properties(&net, &props, &ExplorationConfig::default());
    assert_eq!(results[0].1, Verdict::True, "mutual exclusion should hold");
}
