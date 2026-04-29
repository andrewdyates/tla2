// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for PDR/IC3 encoding of Petri nets as CHC problems.

use super::*;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};

// ── Test helpers ────────────────────────────────────────────────────

fn arc(place: u32, weight: u64) -> Arc {
    Arc {
        place: PlaceIdx(place),
        weight,
    }
}

fn place(id: &str) -> PlaceInfo {
    PlaceInfo {
        id: id.to_string(),
        name: None,
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

/// Simple producer-consumer net:
///   p0 (ready) --[t0]--> p1 (busy) --[t1]--> p0 (ready)
///   Initial marking: p0=1, p1=0
fn simple_two_place_net() -> PetriNet {
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

/// Mutex net with 3 places:
///   p0 (idle_a), p1 (idle_b), p2 (mutex token)
///   t0: p0 + p2 -> p0' (a enters critical section, consumes mutex)
///   t1: p0' -> p0 + p2 (a leaves, restores mutex)
///   Wait, simpler: just a token-bounded net.
///
///   p0=3 tokens, t0 consumes 1 from p0 and produces 1 to p1.
///   Safety: p0 + p1 = 3 always (conservation).
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

/// Net where tokens can only increase at p1 (no conservation):
///   p0=1, t0: p0 -> p0 + p1 (produces at p1 without consuming from it)
fn growing_net() -> PetriNet {
    PetriNet {
        name: Some("growing".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(0, 1), arc(1, 1)])],
        initial_marking: vec![1, 0],
    }
}

// ── Encoding tests ──────────────────────────────────────────────────

#[test]
fn encode_simple_net_produces_valid_chc() {
    let net = simple_two_place_net();
    let safety = ResolvedPredicate::True; // trivial safety
    let config = PdrConfig::default();

    let problem = encode_petri_net_pdr(&net, &safety, &config);

    // Should have exactly 1 predicate
    assert_eq!(problem.predicates().len(), 1);
    assert_eq!(problem.predicates()[0].name, "Inv");
    assert_eq!(problem.predicates()[0].arity(), 2); // 2 places

    // Clauses: 1 init + 2 transitions + 1 stuttering + 1 query = 5
    assert_eq!(problem.clauses().len(), 5);

    // Should have exactly 1 query (head = false)
    assert_eq!(problem.queries().count(), 1);

    // Should have exactly 1 fact (init clause)
    assert_eq!(problem.facts().count(), 1);

    // Should validate
    assert!(problem.validate().is_ok());
}

#[test]
fn encode_without_stuttering() {
    let net = simple_two_place_net();
    let safety = ResolvedPredicate::True;
    let config = PdrConfig {
        add_stuttering: false,
        ..PdrConfig::default()
    };

    let problem = encode_petri_net_pdr(&net, &safety, &config);

    // 1 init + 2 transitions + 0 stuttering + 1 query = 4
    assert_eq!(problem.clauses().len(), 4);
    assert!(problem.validate().is_ok());
}

#[test]
fn encode_without_p_invariants() {
    let net = simple_two_place_net();
    let safety = ResolvedPredicate::True;
    let config = PdrConfig {
        use_p_invariants: false,
        ..PdrConfig::default()
    };

    let problem = encode_petri_net_pdr(&net, &safety, &config);
    assert!(problem.validate().is_ok());
}

#[test]
fn encode_predicate_int_le() {
    let net = simple_two_place_net();
    // Safety: tokens_count(p0) <= 1
    let safety = ResolvedPredicate::IntLe(
        ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
        ResolvedIntExpr::Constant(1),
    );
    let config = PdrConfig::default();

    let problem = encode_petri_net_pdr(&net, &safety, &config);
    assert!(problem.validate().is_ok());
    assert_eq!(problem.queries().count(), 1);
}

#[test]
fn encode_predicate_is_fireable() {
    let net = simple_two_place_net();
    // Safety: t0 is always fireable (this is FALSE for our net)
    let safety = ResolvedPredicate::IsFireable(vec![crate::petri_net::TransitionIdx(0)]);
    let config = PdrConfig::default();

    let problem = encode_petri_net_pdr(&net, &safety, &config);
    assert!(problem.validate().is_ok());
}

#[test]
fn encode_complex_predicate() {
    let net = simple_two_place_net();
    // Safety: (p0 >= 0) AND (p1 >= 0)
    let safety = ResolvedPredicate::And(vec![
        ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(0),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
        ),
        ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(0),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
        ),
    ]);
    let config = PdrConfig::default();

    let problem = encode_petri_net_pdr(&net, &safety, &config);
    assert!(problem.validate().is_ok());
}

#[test]
fn encode_empty_net() {
    // Net with 1 place, 0 transitions
    let net = PetriNet {
        name: None,
        places: vec![place("p0")],
        transitions: vec![],
        initial_marking: vec![5],
    };
    let safety = ResolvedPredicate::True;
    let config = PdrConfig::default();

    let problem = encode_petri_net_pdr(&net, &safety, &config);

    // 1 init + 0 transitions + 1 stuttering + 1 query = 3
    assert_eq!(problem.clauses().len(), 3);
    assert!(problem.validate().is_ok());
}

#[test]
fn encode_multi_weight_transition() {
    // Net with weighted arcs: t0 consumes 2 from p0, produces 3 to p1
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 2)], vec![arc(1, 3)])],
        initial_marking: vec![4, 0],
    };
    let safety = ResolvedPredicate::True;
    let config = PdrConfig::default();

    let problem = encode_petri_net_pdr(&net, &safety, &config);
    assert!(problem.validate().is_ok());
}

#[test]
fn encode_self_loop_transition() {
    // Net where t0 reads from p0 and writes back to p0 (self-loop, zero delta)
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(0, 1), arc(1, 1)])],
        initial_marking: vec![1, 0],
    };
    let safety = ResolvedPredicate::True;
    let config = PdrConfig::default();

    let problem = encode_petri_net_pdr(&net, &safety, &config);
    assert!(problem.validate().is_ok());
}

// ── Solver integration tests ────────────────────────────────────────
// These tests actually run z4-chc and require more time. They verify
// correctness of the full encode+solve pipeline.

#[test]
fn solve_trivially_safe() {
    let net = simple_two_place_net();
    // Safety: TRUE (trivially safe)
    let safety = ResolvedPredicate::True;
    let config = PdrConfig {
        time_budget: Duration::from_secs(10),
        ..PdrConfig::default()
    };

    let result = solve_petri_net_pdr(&net, &safety, &config);
    assert_eq!(result, PdrCheckResult::Safe);
}

#[test]
fn solve_conservation_safe() {
    let net = three_token_net();
    // Safety: p0 + p1 <= 3 (should be safe due to token conservation)
    let safety = ResolvedPredicate::IntLe(
        ResolvedIntExpr::TokensCount(vec![PlaceIdx(0), PlaceIdx(1)]),
        ResolvedIntExpr::Constant(3),
    );
    let config = PdrConfig {
        time_budget: Duration::from_secs(10),
        ..PdrConfig::default()
    };

    let result = solve_petri_net_pdr(&net, &safety, &config);
    assert_eq!(result, PdrCheckResult::Safe);
}

#[test]
fn solve_conservation_also_ge_safe() {
    let net = three_token_net();
    // Safety: p0 + p1 >= 3 (also safe: total tokens = 3 always)
    let safety = ResolvedPredicate::IntLe(
        ResolvedIntExpr::Constant(3),
        ResolvedIntExpr::TokensCount(vec![PlaceIdx(0), PlaceIdx(1)]),
    );
    let config = PdrConfig {
        time_budget: Duration::from_secs(10),
        ..PdrConfig::default()
    };

    let result = solve_petri_net_pdr(&net, &safety, &config);
    assert_eq!(result, PdrCheckResult::Safe);
}

#[test]
fn solve_bounded_unsafe() {
    let net = three_token_net();
    // Safety: p1 <= 2 (UNSAFE: p1 can reach 3 by firing t0 three times)
    let safety = ResolvedPredicate::IntLe(
        ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
        ResolvedIntExpr::Constant(2),
    );
    let config = PdrConfig {
        time_budget: Duration::from_secs(10),
        ..PdrConfig::default()
    };

    let result = solve_petri_net_pdr(&net, &safety, &config);
    assert_eq!(result, PdrCheckResult::Unsafe);
}

#[test]
fn solve_growing_net_safe_bound() {
    let net = growing_net();
    // Safety: p0 >= 1 (should be safe: t0 always restores p0's token)
    let safety = ResolvedPredicate::IntLe(
        ResolvedIntExpr::Constant(1),
        ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
    );
    let config = PdrConfig {
        time_budget: Duration::from_secs(10),
        ..PdrConfig::default()
    };

    let result = solve_petri_net_pdr(&net, &safety, &config);
    assert_eq!(result, PdrCheckResult::Safe);
}

#[test]
fn solve_trivially_unsafe() {
    let net = simple_two_place_net();
    // Safety: FALSE (trivially unsafe)
    let safety = ResolvedPredicate::False;
    let config = PdrConfig {
        time_budget: Duration::from_secs(10),
        ..PdrConfig::default()
    };

    let result = solve_petri_net_pdr(&net, &safety, &config);
    assert_eq!(result, PdrCheckResult::Unsafe);
}

#[test]
fn solve_negation_property() {
    let net = simple_two_place_net();
    // Safety: NOT(p0 >= 2) = p0 <= 1 (safe: p0 is always 0 or 1)
    let safety = ResolvedPredicate::Not(Box::new(ResolvedPredicate::IntLe(
        ResolvedIntExpr::Constant(2),
        ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
    )));
    let config = PdrConfig {
        time_budget: Duration::from_secs(10),
        ..PdrConfig::default()
    };

    let result = solve_petri_net_pdr(&net, &safety, &config);
    assert_eq!(result, PdrCheckResult::Safe);
}
