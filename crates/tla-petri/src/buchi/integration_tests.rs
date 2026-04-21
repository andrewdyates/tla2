// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::examinations::ltl::check_ltl_properties;
use crate::explorer::ExplorationConfig;
use crate::output::Verdict;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
use crate::property_xml::{Formula, IntExpr, LtlFormula, Property, StatePredicate};

fn cyclic_safe_net() -> PetriNet {
    PetriNet {
        name: Some("cycle-safe".to_string()),
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

fn linear_deadlock_net() -> PetriNet {
    PetriNet {
        name: Some("linear-deadlock".to_string()),
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
        transitions: vec![TransitionInfo {
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
        }],
        initial_marking: vec![1, 0],
    }
}

fn tokens_at_least(place: &str, value: u64) -> LtlFormula {
    LtlFormula::Atom(StatePredicate::IntLe(
        IntExpr::Constant(value),
        IntExpr::TokensCount(vec![place.to_string()]),
    ))
}

fn property(id: &str, formula: LtlFormula) -> Property {
    Property {
        id: id.to_string(),
        formula: Formula::Ltl(formula),
    }
}

#[test]
fn test_ltl_mutex_global_exclusion() {
    let net = cyclic_safe_net();
    let props = vec![property(
        "mutex",
        LtlFormula::Globally(Box::new(LtlFormula::Not(Box::new(LtlFormula::And(vec![
            tokens_at_least("p0", 1),
            tokens_at_least("p1", 1),
        ]))))),
    )];

    let results = check_ltl_properties(&net, &props, &ExplorationConfig::default());

    assert_eq!(results[0].1, Verdict::True);
}

#[test]
fn test_ltl_always_eventually_token_returns_false_after_drain() {
    let net = linear_deadlock_net();
    let props = vec![property(
        "gf-p0",
        LtlFormula::Globally(Box::new(LtlFormula::Finally(Box::new(tokens_at_least(
            "p0", 1,
        ))))),
    )];

    let results = check_ltl_properties(&net, &props, &ExplorationConfig::default());

    assert_eq!(results[0].1, Verdict::False);
}

#[test]
fn test_ltl_formerly_guarded_ids_now_execute_normally() {
    // After the guard-timing fix (#1246), the 5 formerly-guarded property
    // IDs now execute normally instead of returning CannotCompute.
    let net = cyclic_safe_net();
    let formerly_guarded_ids = [
        "AirplaneLD-PT-0010-LTLCardinality-04",
        "AirplaneLD-PT-0010-LTLCardinality-09",
        "CSRepetitions-PT-02-LTLCardinality-03",
        "Anderson-PT-04-LTLFireability-02",
        "CSRepetitions-PT-02-LTLFireability-03",
    ];
    let props: Vec<_> = formerly_guarded_ids
        .iter()
        .map(|id| property(id, LtlFormula::Globally(Box::new(tokens_at_least("p0", 1)))))
        .collect();

    let results = check_ltl_properties(&net, &props, &ExplorationConfig::default());

    for (id, verdict) in &results {
        assert_ne!(
            *verdict,
            Verdict::CannotCompute,
            "{id} should execute normally after guard-timing fix"
        );
    }
}

// ── GBA acceptance regression tests for G(X(F(...))) pattern ────────

#[test]
fn test_ltl_globally_next_finally_on_cycle() {
    // A(G(X(F(p0 >= 1)))) on cyclic net: [1,0] <-> [0,1]
    // From any state, in the next state, eventually p0>=1 holds:
    //   From [1,0]: next is [0,1], then [1,0] has p0=1. TRUE.
    //   From [0,1]: next is [1,0] which has p0=1. TRUE.
    // Ground truth: TRUE
    let net = cyclic_safe_net();
    let props = vec![property(
        "g-x-f",
        LtlFormula::Globally(Box::new(LtlFormula::Next(Box::new(LtlFormula::Finally(
            Box::new(tokens_at_least("p0", 1)),
        ))))),
    )];

    let results = check_ltl_properties(&net, &props, &ExplorationConfig::default());

    assert_eq!(
        results[0].1,
        Verdict::True,
        "A(G(X(F(p0>=1)))) should be TRUE on cyclic net where p0 recurs"
    );
}

#[test]
fn test_ltl_globally_next_finally_next_finally_on_cycle() {
    // A(G(X(F(X(F(p0 >= 1)))))) on cyclic net
    // This nests two F operators inside G(X(...)), creating multiple
    // acceptance sets that must all be covered in the product.
    // Ground truth: TRUE (same reasoning — p0=1 recurs on the cycle)
    let net = cyclic_safe_net();
    let props = vec![property(
        "g-x-f-x-f",
        LtlFormula::Globally(Box::new(LtlFormula::Next(Box::new(LtlFormula::Finally(
            Box::new(LtlFormula::Next(Box::new(LtlFormula::Finally(Box::new(
                tokens_at_least("p0", 1),
            ))))),
        ))))),
    )];

    let results = check_ltl_properties(&net, &props, &ExplorationConfig::default());

    assert_eq!(
        results[0].1,
        Verdict::True,
        "A(G(X(F(X(F(p0>=1)))))) should be TRUE on cyclic net where p0 recurs"
    );
}

#[test]
fn test_ltl_not_next_finally_globally_pattern() {
    // A(¬X(F(G(X(F(X(F(p0 >= 1)))))))) on cyclic net
    // This is the exact pattern of AirplaneLD LTLCardinality-04.
    // X(F(G(...))) means "in the next step, eventually reach a point
    // where G(...) holds forever." On a cycle where p0 recurs, the G
    // inner formula holds from every point. So the F is satisfied, and
    // the X just delays by one step.
    // So X(F(G(...))) is TRUE on this net.
    // Therefore ¬X(F(G(...))) is FALSE.
    // Therefore A(¬X(F(G(...)))) is FALSE.
    let net = cyclic_safe_net();
    let props = vec![property(
        "not-x-f-g-x-f-x-f",
        LtlFormula::Not(Box::new(LtlFormula::Next(Box::new(LtlFormula::Finally(
            Box::new(LtlFormula::Globally(Box::new(LtlFormula::Next(Box::new(
                LtlFormula::Finally(Box::new(LtlFormula::Next(Box::new(LtlFormula::Finally(
                    Box::new(tokens_at_least("p0", 1)),
                ))))),
            ))))),
        ))))),
    )];

    let results = check_ltl_properties(&net, &props, &ExplorationConfig::default());

    assert_eq!(
        results[0].1,
        Verdict::False,
        "A(¬X(F(G(X(F(X(F(p0>=1)))))))) should be FALSE on cyclic net"
    );
}

#[test]
fn test_ltl_not_next_finally_globally_simpler() {
    // A(¬X(F(G(X(F(p0 >= 1)))))) on cyclic net
    // Simpler version with only one F inside G(X(...))
    // X(F(G(X(F(p0>=1))))) should be TRUE → ¬(...) is FALSE → A(¬(...)) is FALSE
    let net = cyclic_safe_net();
    let props = vec![property(
        "not-x-f-g-x-f",
        LtlFormula::Not(Box::new(LtlFormula::Next(Box::new(LtlFormula::Finally(
            Box::new(LtlFormula::Globally(Box::new(LtlFormula::Next(Box::new(
                LtlFormula::Finally(Box::new(tokens_at_least("p0", 1))),
            ))))),
        ))))),
    )];

    let results = check_ltl_properties(&net, &props, &ExplorationConfig::default());

    assert_eq!(
        results[0].1,
        Verdict::False,
        "A(¬X(F(G(X(F(p0>=1)))))) should be FALSE on cyclic net"
    );
}

#[test]
fn test_ltl_finally_globally_next_finally() {
    // A(F(G(X(F(p0 >= 1))))) on cyclic net
    // F(G(X(F(p0>=1)))): eventually, from some point, globally X(F(p0>=1)).
    // On the cycle, G(X(F(p0>=1))) holds from the start. So F is trivially satisfied.
    // Ground truth: TRUE
    let net = cyclic_safe_net();
    let props = vec![property(
        "f-g-x-f",
        LtlFormula::Finally(Box::new(LtlFormula::Globally(Box::new(LtlFormula::Next(
            Box::new(LtlFormula::Finally(Box::new(tokens_at_least("p0", 1)))),
        ))))),
    )];

    let results = check_ltl_properties(&net, &props, &ExplorationConfig::default());

    assert_eq!(
        results[0].1,
        Verdict::True,
        "A(F(G(X(F(p0>=1))))) should be TRUE on cyclic net"
    );
}

#[test]
fn test_ltl_finally_next_globally_on_deadlock_net() {
    // A(F(X(G(tokens(p0) >= 1)))) on linear deadlock net: [1,0] → [0,1] (dead)
    //
    // This mirrors the CircadianClock-PT-000001-LTLFireability-10 pattern:
    //   A(F(¬X(F(¬(is-fireable(t_a) ∨ is-fireable(t_b)))))) = A(F(X(G(a ∨ b))))
    //
    // Path: [1,0] → [0,1] → [0,1] → ...
    // At deadlock [0,1]: p0 = 0, so G(p0 >= 1) is false.
    // At [0,1]: X(G(p0>=1)) = G(p0>=1) at [0,1] = false.
    // At [1,0]: X(G(p0>=1)) = G(p0>=1) at [0,1] = false.
    // No position satisfies X(G(p0>=1)), so F(X(G(p0>=1))) is false.
    // Ground truth: FALSE
    let net = linear_deadlock_net();
    let props = vec![property(
        "f-x-g-deadlock",
        LtlFormula::Finally(Box::new(LtlFormula::Next(Box::new(LtlFormula::Globally(
            Box::new(tokens_at_least("p0", 1)),
        ))))),
    )];

    let results = check_ltl_properties(&net, &props, &ExplorationConfig::default());

    assert_eq!(
        results[0].1,
        Verdict::False,
        "A(F(X(G(p0>=1)))) should be FALSE on deadlock net — \
         deadlock self-loop with p0=0 means G(p0>=1) never holds"
    );
}

#[test]
fn test_ltl_finally_negation_next_finally_negation_on_deadlock_net() {
    // A(F(¬X(F(¬(tokens(p0) >= 1))))) on linear deadlock net
    //
    // This is the EXACT syntactic pattern of CircadianClock-PT-000001-LTLFireability-10,
    // using tokens-count instead of is-fireable.
    //
    // Simplification: ¬(tokens(p0) >= 1) = tokens(p0) < 1 = tokens(p0) == 0
    //   F(¬(tokens(p0) >= 1)) = F(p0 == 0) = eventually p0 is empty
    //   X(F(p0 == 0)) = in next state, eventually p0 is empty
    //   ¬X(F(p0 == 0)) = X(G(p0 >= 1)) — in next state, p0 is always >= 1
    //   F(X(G(p0 >= 1))) = eventually reach a state where next state always has p0 >= 1
    //
    // Same as test above but constructed with negation nesting.
    // Ground truth: FALSE
    let net = linear_deadlock_net();

    // Build: F(¬(X(F(¬(p0 >= 1)))))
    let inner_atom = tokens_at_least("p0", 1);
    let not_atom = LtlFormula::Not(Box::new(inner_atom));
    let f_not_atom = LtlFormula::Finally(Box::new(not_atom));
    let x_f_not = LtlFormula::Next(Box::new(f_not_atom));
    let not_x_f_not = LtlFormula::Not(Box::new(x_f_not));
    let f_not_x_f_not = LtlFormula::Finally(Box::new(not_x_f_not));

    let props = vec![property("circadian-pattern", f_not_x_f_not)];

    let results = check_ltl_properties(&net, &props, &ExplorationConfig::default());

    assert_eq!(
        results[0].1,
        Verdict::False,
        "A(F(¬X(F(¬(p0>=1))))) should be FALSE on deadlock net — \
         same pattern as CircadianClock-PT-000001-LTLFireability-10"
    );
}

#[test]
fn test_gba_acceptance_coverage_for_globally_next_finally() {
    // Diagnostic: examine the GBA for the negated formula of
    // ¬X(F(G(X(F(p))))) to understand why acceptance fails.
    //
    // The formula φ = ¬X(F(G(X(F(p)))))
    // In NNF: Next(Release(False, Until(True, Next(Release(False, Next(Release(False, NegAtom(0))))))))
    //
    // ¬φ = X(F(G(X(F(p)))))
    // In NNF: Next(Until(True, Release(False, Next(Until(True, Atom(0))))))
    //
    // The GBA is built from ¬φ. It should have an accepting cycle when
    // Atom(0) holds infinitely often.
    use super::gba::build_gba;
    use super::nnf::{negate, to_nnf};

    let formula = LtlFormula::Not(Box::new(LtlFormula::Next(Box::new(LtlFormula::Finally(
        Box::new(LtlFormula::Globally(Box::new(LtlFormula::Next(Box::new(
            LtlFormula::Finally(Box::new(tokens_at_least("p0", 1))),
        ))))),
    )))));

    let mut atoms = Vec::new();
    let nnf = to_nnf(&formula, &mut atoms);
    // nnf = φ in NNF
    // check_ltl_formula negates: neg = ¬φ
    let neg = negate(&nnf);
    let gba = build_gba(&neg);

    eprintln!("GBA states: {}", gba.num_states);
    eprintln!("GBA acceptance sets: {}", gba.acceptance.len());
    for (i, acc_set) in gba.acceptance.iter().enumerate() {
        eprintln!("  acceptance[{i}]: states {:?}", acc_set);
    }
    eprintln!("GBA initial transitions: {}", gba.initial_transitions.len());
    for (i, t) in gba.initial_transitions.iter().enumerate() {
        eprintln!(
            "  init[{i}]: pos={:?} neg={:?} → state {}",
            t.pos_atoms, t.neg_atoms, t.successor
        );
    }
    for sid in 0..gba.num_states {
        eprintln!(
            "GBA state {sid}: {} transitions",
            gba.transitions[sid as usize].len()
        );
        for (i, t) in gba.transitions[sid as usize].iter().enumerate() {
            eprintln!(
                "  [{i}]: pos={:?} neg={:?} → state {}",
                t.pos_atoms, t.neg_atoms, t.successor
            );
        }
    }

    // The GBA should have at least one acceptance set where some state
    // reachable from the initial states is accepting AND part of a cycle.
    // If no state in the "G regime" is accepting for any Until set that
    // the G operator re-introduces, that's the bug.
    let total_accepting_states: usize = gba.acceptance.iter().map(|s| s.len()).sum();
    assert!(
        total_accepting_states > 0,
        "GBA should have at least some accepting states"
    );

    // Check: is there any state that is accepting for ALL acceptance sets?
    let all_accepting: Vec<u32> = (0..gba.num_states)
        .filter(|&s| gba.acceptance.iter().all(|set| set.contains(&s)))
        .collect();
    eprintln!("States accepting for ALL sets: {:?}", all_accepting);

    // Check: are all acceptance sets represented in the reachable states
    // (excluding the initial-only state)?
    for (i, acc_set) in gba.acceptance.iter().enumerate() {
        let non_initial: Vec<_> = acc_set
            .iter()
            .filter(|&&s| {
                // Check if this state is reachable from another state (not just initial)
                (0..gba.num_states).any(|from| {
                    gba.transitions[from as usize]
                        .iter()
                        .any(|t| t.successor == s)
                })
            })
            .collect();
        eprintln!(
            "acceptance[{i}]: {} total, {} reachable from non-initial",
            acc_set.len(),
            non_initial.len()
        );
    }
}
