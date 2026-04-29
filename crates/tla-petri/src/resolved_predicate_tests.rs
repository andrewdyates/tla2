// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for resolved predicate resolution and evaluation.
//!
//! Covers the silent-false-on-missing-name behavior that can produce wrong
//! answers when PNML place/transition IDs don't match property XML names.

use std::collections::HashMap;

use super::{
    count_unresolved_with_aliases, eval_int_expr, eval_predicate, predicate_reduction_safe,
    remap_int_expr, remap_predicate, resolve_int_expr, resolve_int_expr_with_aliases,
    resolve_place_bound, resolve_predicate, resolve_predicate_with_aliases, ResolvedIntExpr,
    ResolvedPredicate,
};
use crate::model::PropertyAliases;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionIdx, TransitionInfo};
use crate::property_xml::{IntExpr, StatePredicate};
use crate::reduction::{reduce, reduce_iterative};

fn simple_net() -> PetriNet {
    PetriNet {
        name: Some("test".into()),
        places: vec![
            PlaceInfo {
                id: "P0".into(),
                name: None,
            },
            PlaceInfo {
                id: "P1".into(),
                name: None,
            },
        ],
        transitions: vec![TransitionInfo {
            id: "T0".into(),
            name: None,
            inputs: vec![Arc {
                place: PlaceIdx(0),
                weight: 2,
            }],
            outputs: vec![Arc {
                place: PlaceIdx(1),
                weight: 1,
            }],
        }],
        initial_marking: vec![3, 0],
    }
}

fn duplicate_transition_net() -> PetriNet {
    PetriNet {
        name: Some("duplicate-transitions".into()),
        places: vec![
            PlaceInfo {
                id: "P0".into(),
                name: None,
            },
            PlaceInfo {
                id: "P1".into(),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "T0".into(),
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
                id: "T1".into(),
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
                id: "T_back".into(),
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

fn unfolded_alias_net() -> PetriNet {
    PetriNet {
        name: Some("alias-unfolded".into()),
        places: vec![
            PlaceInfo {
                id: "Fork_0".into(),
                name: None,
            },
            PlaceInfo {
                id: "Fork_1".into(),
                name: None,
            },
            PlaceInfo {
                id: "Done".into(),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "Take_0".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "Take_1".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![1, 1, 0],
    }
}

fn constant_place_net() -> PetriNet {
    PetriNet {
        name: Some("constant-place".into()),
        places: vec![
            PlaceInfo {
                id: "P_live".into(),
                name: None,
            },
            PlaceInfo {
                id: "P_sink".into(),
                name: None,
            },
            PlaceInfo {
                id: "P_const".into(),
                name: None,
            },
        ],
        transitions: vec![TransitionInfo {
            id: "T_live".into(),
            name: None,
            inputs: vec![
                Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                },
                Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                },
            ],
            outputs: vec![
                Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                },
                Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                },
            ],
        }],
        initial_marking: vec![1, 0, 3],
    }
}

fn agglomeration_net() -> PetriNet {
    PetriNet {
        name: Some("agglomeration".into()),
        places: vec![
            PlaceInfo {
                id: "p0".into(),
                name: None,
            },
            PlaceInfo {
                id: "p_mid".into(),
                name: None,
            },
            PlaceInfo {
                id: "p2".into(),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "t0".into(),
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
                id: "t1".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![1, 0, 0],
    }
}

fn place_map(net: &PetriNet) -> HashMap<&str, PlaceIdx> {
    net.places
        .iter()
        .enumerate()
        .map(|(i, p)| (p.id.as_str(), PlaceIdx(i as u32)))
        .collect()
}

fn trans_map(net: &PetriNet) -> HashMap<&str, TransitionIdx> {
    net.transitions
        .iter()
        .enumerate()
        .map(|(i, t)| (t.id.as_str(), TransitionIdx(i as u32)))
        .collect()
}

fn alias_tables() -> PropertyAliases {
    let mut aliases = PropertyAliases::identity(&unfolded_alias_net());
    aliases
        .place_aliases
        .insert(String::from("Fork"), vec![PlaceIdx(0), PlaceIdx(1)]);
    aliases.transition_aliases.insert(
        String::from("Take"),
        vec![TransitionIdx(0), TransitionIdx(1)],
    );
    aliases
}

#[test]
fn test_resolve_is_fireable_no_match_returns_false() {
    // When none of the named transitions exist in the net, IsFireable
    // resolves to False (line 67-68). This silently turns the predicate
    // into a constant — a potential source of wrong answers if the PNML
    // transition IDs differ from the property XML names.
    let net = simple_net();
    let pm = place_map(&net);
    let tm = trans_map(&net);

    let pred = StatePredicate::IsFireable(vec!["nonexistent_t1".into(), "nonexistent_t2".into()]);
    let resolved = resolve_predicate(&pred, &pm, &tm);
    assert!(
        matches!(resolved, ResolvedPredicate::False),
        "unresolvable transitions should produce False"
    );

    // Verify it evaluates to false
    let marking = &[3, 0];
    assert!(!eval_predicate(&resolved, marking, &net));
}

#[test]
fn test_resolve_is_fireable_partial_match() {
    // When some transitions match and some don't, only the matching ones
    // are kept. The predicate should still work for the resolved subset.
    let net = simple_net();
    let pm = place_map(&net);
    let tm = trans_map(&net);

    let pred = StatePredicate::IsFireable(vec!["T0".into(), "nonexistent".into()]);
    let resolved = resolve_predicate(&pred, &pm, &tm);

    // T0 exists, so we should get IsFireable([T0]), not False
    assert!(matches!(resolved, ResolvedPredicate::IsFireable(_)));

    // T0 requires P0 >= 2. With marking [3, 0], T0 is enabled.
    let marking = &[3, 0];
    assert!(eval_predicate(&resolved, marking, &net));

    // With marking [1, 0], T0 is not enabled (needs weight 2).
    let marking = &[1, 0];
    assert!(!eval_predicate(&resolved, marking, &net));
}

#[test]
fn test_resolve_tokens_count_missing_place() {
    // filter_map silently drops unknown place names:
    // TokensCount(["nonexistent"]) becomes TokensCount([]) which sums to 0.
    // This is a potential source of wrong answers when PNML place IDs differ
    // from property XML names.
    let net = simple_net();
    let pm = place_map(&net);

    let expr = IntExpr::TokensCount(vec!["nonexistent".into()]);
    let resolved = resolve_int_expr(&expr, &pm);

    // Should resolve to TokensCount with empty indices
    let ResolvedIntExpr::TokensCount(indices) = &resolved else {
        panic!("expected TokensCount");
    };
    assert!(
        indices.is_empty(),
        "unknown places should be silently dropped"
    );

    // Evaluates to 0 regardless of marking
    let marking = &[100, 200];
    assert_eq!(eval_int_expr(&resolved, marking), 0);
}

#[test]
fn test_resolve_tokens_count_partial_match() {
    // When some places match and some don't, only matched places are summed.
    let net = simple_net();
    let pm = place_map(&net);

    let expr = IntExpr::TokensCount(vec!["P0".into(), "nonexistent".into(), "P1".into()]);
    let resolved = resolve_int_expr(&expr, &pm);

    let ResolvedIntExpr::TokensCount(indices) = &resolved else {
        panic!("expected TokensCount");
    };
    assert_eq!(indices.len(), 2, "only P0 and P1 should resolve");

    // Marking [3, 5]: should sum to 3 + 5 = 8 (skipping nonexistent)
    let marking = &[3, 5];
    assert_eq!(eval_int_expr(&resolved, marking), 8);
}

#[test]
fn test_resolve_place_bound_alias_expands_all_unfolded_places_in_formula_order() {
    let aliases = alias_tables();
    let resolved = resolve_place_bound(
        &[
            String::from("Fork"),
            String::from("Done"),
            String::from("Fork"),
        ],
        &aliases,
    );
    assert_eq!(
        resolved,
        vec![
            PlaceIdx(0),
            PlaceIdx(1),
            PlaceIdx(2),
            PlaceIdx(0),
            PlaceIdx(1)
        ]
    );
}

#[test]
fn test_resolve_tokens_count_alias_expands_and_preserves_multiplicity() {
    let aliases = alias_tables();
    let net = unfolded_alias_net();
    let resolved = resolve_int_expr_with_aliases(
        &IntExpr::TokensCount(vec![String::from("Fork"), String::from("Fork")]),
        &aliases,
    );

    let ResolvedIntExpr::TokensCount(indices) = &resolved else {
        panic!("expected tokens-count");
    };
    assert_eq!(
        indices,
        &vec![PlaceIdx(0), PlaceIdx(1), PlaceIdx(0), PlaceIdx(1)]
    );
    assert_eq!(eval_int_expr(&resolved, &net.initial_marking), 4);
}

#[test]
fn test_resolve_is_fireable_alias_checks_all_unfolded_transitions() {
    let aliases = alias_tables();
    let net = unfolded_alias_net();
    let resolved = resolve_predicate_with_aliases(
        &StatePredicate::IsFireable(vec![String::from("Take")]),
        &aliases,
    );

    let ResolvedPredicate::IsFireable(indices) = &resolved else {
        panic!("expected alias-expanded fireability");
    };
    assert_eq!(indices, &vec![TransitionIdx(0), TransitionIdx(1)]);
    assert!(eval_predicate(&resolved, &net.initial_marking, &net));
    assert!(!eval_predicate(&resolved, &[0, 0, 0], &net));
}

#[test]
fn test_count_unresolved_with_aliases_treats_missing_alias_name_as_unresolved() {
    let aliases = alias_tables();
    let pred = StatePredicate::IntLe(
        IntExpr::TokensCount(vec![String::from("Fork"), String::from("Missing")]),
        IntExpr::Constant(3),
    );
    let (total, unresolved) = count_unresolved_with_aliases(&pred, &aliases);
    assert_eq!(total, 2);
    assert_eq!(unresolved, 1);
}

#[test]
fn test_eval_int_le_boundary() {
    // IntLe uses <= (not <). Verify boundary: equal values → true.
    let net = simple_net();
    let marking = &[5, 3];

    // 5 <= 5 (Constant(5) <= TokensCount([P0])) → true
    let pred = ResolvedPredicate::IntLe(
        ResolvedIntExpr::Constant(5),
        ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
    );
    assert!(
        eval_predicate(&pred, marking, &net),
        "5 <= 5 should be true"
    );

    // 6 <= 5 → false
    let pred = ResolvedPredicate::IntLe(
        ResolvedIntExpr::Constant(6),
        ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
    );
    assert!(
        !eval_predicate(&pred, marking, &net),
        "6 <= 5 should be false"
    );

    // 4 <= 5 → true
    let pred = ResolvedPredicate::IntLe(
        ResolvedIntExpr::Constant(4),
        ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
    );
    assert!(
        eval_predicate(&pred, marking, &net),
        "4 <= 5 should be true"
    );
}

#[test]
fn test_eval_int_le_zero_boundary() {
    // 0 <= 0 should be true (both sides zero)
    let net = simple_net();
    let marking = &[0, 0];
    let pred = ResolvedPredicate::IntLe(
        ResolvedIntExpr::Constant(0),
        ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
    );
    assert!(
        eval_predicate(&pred, marking, &net),
        "0 <= 0 should be true"
    );
}

#[test]
fn test_eval_is_fireable_checks_all_inputs() {
    // T0 requires P0 >= 2 (input arc weight 2). Verify that the weight
    // threshold is respected, not just "token > 0".
    let net = simple_net();

    // Marking [2, 0]: exactly at threshold → enabled
    let pred = ResolvedPredicate::IsFireable(vec![TransitionIdx(0)]);
    assert!(eval_predicate(&pred, &[2, 0], &net), "P0=2 meets weight=2");

    // Marking [1, 0]: below threshold → not enabled
    assert!(!eval_predicate(&pred, &[1, 0], &net), "P0=1 < weight=2");

    // Marking [0, 0]: zero tokens → not enabled
    assert!(!eval_predicate(&pred, &[0, 0], &net), "P0=0 < weight=2");
}

#[test]
fn test_resolve_roundtrip() {
    // Full resolve + eval pipeline: resolve a known predicate from string
    // names, evaluate against a known marking, verify result matches
    // hand computation.
    let net = simple_net();
    let pm = place_map(&net);
    let tm = trans_map(&net);

    // Predicate: (tokens(P0) + tokens(P1) <= 3) AND isFireable(T0)
    // At marking [2, 1]: sum=3, 3<=3 true; T0 needs P0>=2, P0=2 true.
    // Result: true AND true = true.
    let pred = StatePredicate::And(vec![
        StatePredicate::IntLe(
            IntExpr::TokensCount(vec!["P0".into(), "P1".into()]),
            IntExpr::Constant(3),
        ),
        StatePredicate::IsFireable(vec!["T0".into()]),
    ]);
    let resolved = resolve_predicate(&pred, &pm, &tm);

    assert!(eval_predicate(&resolved, &[2, 1], &net));

    // At marking [1, 1]: sum=2, 2<=3 true; T0 needs P0>=2, P0=1 false.
    // Result: true AND false = false.
    assert!(!eval_predicate(&resolved, &[1, 1], &net));

    // At marking [3, 1]: sum=4, 4<=3 false; short-circuit AND → false.
    assert!(!eval_predicate(&resolved, &[3, 1], &net));
}

#[test]
fn test_resolve_constants() {
    let net = simple_net();
    let pm = place_map(&net);
    let tm = trans_map(&net);

    let true_pred = resolve_predicate(&StatePredicate::True, &pm, &tm);
    let false_pred = resolve_predicate(&StatePredicate::False, &pm, &tm);

    assert!(eval_predicate(&true_pred, &[0, 0], &net));
    assert!(!eval_predicate(&false_pred, &[0, 0], &net));
}

#[test]
fn test_remap_int_expr_rewrites_place_indices() {
    let expr = ResolvedIntExpr::TokensCount(vec![PlaceIdx(1), PlaceIdx(0), PlaceIdx(1)]);
    let place_map = vec![Some(PlaceIdx(4)), Some(PlaceIdx(2))];

    let remapped = remap_int_expr(&expr, &place_map).expect("all places should remap");
    match remapped {
        ResolvedIntExpr::TokensCount(indices) => {
            assert_eq!(indices, vec![PlaceIdx(2), PlaceIdx(4), PlaceIdx(2)]);
        }
        ResolvedIntExpr::Constant(_) => panic!("expected remapped tokens-count expression"),
    }
}

#[test]
fn test_remap_predicate_fails_when_slice_drops_dependency() {
    let pred = ResolvedPredicate::And(vec![
        ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
            ResolvedIntExpr::Constant(1),
        ),
        ResolvedPredicate::IsFireable(vec![TransitionIdx(0)]),
    ]);

    let missing_place = remap_predicate(&pred, &[None], &[Some(TransitionIdx(2))]);
    assert!(
        missing_place.is_none(),
        "dropped places must abort remapping"
    );

    let missing_transition = remap_predicate(&pred, &[Some(PlaceIdx(3))], &[None]);
    assert!(
        missing_transition.is_none(),
        "dropped transitions must abort remapping"
    );
}

#[test]
fn test_remap_predicate_aliases_removed_duplicate_transition_id() {
    let reduced = reduce(&duplicate_transition_net());
    let duplicate = ResolvedPredicate::IsFireable(vec![TransitionIdx(1)]);
    let canonical = ResolvedPredicate::IsFireable(vec![TransitionIdx(0)]);

    let remapped_duplicate =
        remap_predicate(&duplicate, &reduced.place_map, &reduced.transition_map)
            .expect("duplicate transition should alias to the canonical survivor");
    let remapped_canonical =
        remap_predicate(&canonical, &reduced.place_map, &reduced.transition_map)
            .expect("canonical transition should still remap");

    let ResolvedPredicate::IsFireable(duplicate_indices) = &remapped_duplicate else {
        panic!("expected remapped duplicate fireability predicate");
    };
    let ResolvedPredicate::IsFireable(canonical_indices) = &remapped_canonical else {
        panic!("expected remapped canonical fireability predicate");
    };
    assert_eq!(duplicate_indices, canonical_indices);
    assert_eq!(duplicate_indices, &vec![TransitionIdx(0)]);
    assert!(eval_predicate(
        &remapped_duplicate,
        &reduced.net.initial_marking,
        &reduced.net
    ));
    assert_eq!(
        eval_predicate(
            &remapped_duplicate,
            &reduced.net.initial_marking,
            &reduced.net
        ),
        eval_predicate(
            &remapped_canonical,
            &reduced.net.initial_marking,
            &reduced.net
        )
    );
}

#[test]
fn test_resolve_not() {
    let net = simple_net();
    let pm = place_map(&net);
    let tm = trans_map(&net);

    let pred = StatePredicate::Not(Box::new(StatePredicate::True));
    let resolved = resolve_predicate(&pred, &pm, &tm);
    assert!(!eval_predicate(&resolved, &[0, 0], &net));

    let pred = StatePredicate::Not(Box::new(StatePredicate::False));
    let resolved = resolve_predicate(&pred, &pm, &tm);
    assert!(eval_predicate(&resolved, &[0, 0], &net));
}

#[test]
fn test_predicate_reduction_safe_allows_removed_constant_place_when_adjacent_transition_survives() {
    let net = constant_place_net();
    let reduced = reduce(&net);
    assert!(
        reduced.place_map[2].is_none(),
        "constant place should be removed by reduction"
    );
    assert!(
        reduced.transition_map[0].is_some(),
        "the live transition touching the constant place should survive"
    );

    let pred = ResolvedPredicate::IntLe(
        ResolvedIntExpr::TokensCount(vec![PlaceIdx(2)]),
        ResolvedIntExpr::Constant(3),
    );
    assert!(
        predicate_reduction_safe(&pred, &net, &reduced.transition_map),
        "removing a constant place is safe when every adjacent transition survives",
    );
}

#[test]
fn test_predicate_reduction_safe_rejects_tokens_count_when_touching_transition_is_removed() {
    let net = agglomeration_net();
    let reduced = reduce_iterative(&net).expect("agglomeration reduction should succeed");
    assert!(reduced.place_map[1].is_none(), "p_mid should be removed");
    assert!(
        reduced.transition_map[0].is_none(),
        "t0 should be removed by agglomeration",
    );

    let pred = ResolvedPredicate::IntLe(
        ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
        ResolvedIntExpr::Constant(0),
    );
    assert!(
        !predicate_reduction_safe(&pred, &net, &reduced.transition_map),
        "TokensCount should be unsafe when a touching transition was eliminated",
    );
}

#[test]
fn test_resolve_or() {
    let net = simple_net();
    let pm = place_map(&net);
    let tm = trans_map(&net);

    // (P0 >= 5) OR (P1 >= 1). At [3, 0]: false OR false = false.
    let pred = StatePredicate::Or(vec![
        StatePredicate::IntLe(
            IntExpr::Constant(5),
            IntExpr::TokensCount(vec!["P0".into()]),
        ),
        StatePredicate::IntLe(
            IntExpr::Constant(1),
            IntExpr::TokensCount(vec!["P1".into()]),
        ),
    ]);
    let resolved = resolve_predicate(&pred, &pm, &tm);
    assert!(!eval_predicate(&resolved, &[3, 0], &net));

    // At [3, 1]: false OR true = true.
    assert!(eval_predicate(&resolved, &[3, 1], &net));
}
