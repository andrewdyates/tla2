// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Property-driven reduction × examination tests.
//!
//! Each test verifies that a specific property-based examination (UpperBounds,
//! Reachability, CTL, LTL) produces the correct answer on a net where
//! structural reductions remove structure referenced by the property.
//!
//! Coverage matrix (cells with tests in this module):
//!
//! | Reduction      | UpperBounds | Reachability | CTL | LTL |
//! |----------------|-------------|-------------|-----|-----|
//! | Constant place | T           | T (EF+AG)   | T   | T   |
//! | Dead trans     | T           | T           | T   | T   |
//! | Isolated place | T           | T           | T   | T   |
//!
//! Budget-edge boundary coverage lives in `property_budget_dispatch.rs`.

use crate::examinations::ctl::check_ctl_properties;
use crate::examinations::ltl::check_ltl_properties;
use crate::examinations::reachability::check_reachability_properties;
use crate::examinations::upper_bounds::check_upper_bounds_properties;
use crate::output::Verdict;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
use crate::property_xml::{
    CtlFormula, Formula, IntExpr, LtlFormula, PathQuantifier, Property, ReachabilityFormula,
    StatePredicate,
};

use super::fixtures::default_config;

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

/// Net with a constant place P_const (always 3 tokens).
///
/// ```text
/// P_live(1) + P_const(3) --T_live--> P_sink(0) + P_const(3)
/// ```
///
/// T_live consumes 1 from P_live and 1 from P_const, produces 1 to P_sink and
/// 1 to P_const. P_const has net effect 0 for every transition — it is constant.
/// T_live fires once (P_live drains), then deadlock.
///
/// Reduction removes P_const as a constant place. Property tests must still
/// see P_const = 3 in expanded markings.
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

/// Net with a structurally dead transition T_dead.
///
/// ```text
/// P_live(1) --T_live--> P_sink(0)
/// P_dead_src(0) --T_dead--> P_sink(0)
/// ```
///
/// P_dead_src has 0 tokens and no producer, so T_dead can never fire.
/// Reduction removes T_dead (and P_dead_src as cascade-isolated).
/// Fireability properties referencing T_dead must evaluate to FALSE.
fn dead_transition_net() -> PetriNet {
    PetriNet {
        name: Some("dead-transition-property".into()),
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
                id: "P_dead_src".into(),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "T_live".into(),
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
                id: "T_dead".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![1, 0, 0],
    }
}

/// Net with an isolated place P_iso (5 tokens, no connected transitions).
///
/// ```text
/// P_live(1) --T_live--> P_sink(0)
/// P_iso(5)  [isolated — no transitions]
/// ```
///
/// P_iso has no input or output arcs. Reduction removes it as isolated.
/// Property tests referencing P_iso must still see its constant value of 5
/// in expanded markings.
fn isolated_place_net() -> PetriNet {
    PetriNet {
        name: Some("isolated-place-property".into()),
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
                id: "P_iso".into(),
                name: None,
            },
        ],
        transitions: vec![TransitionInfo {
            id: "T_live".into(),
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
        initial_marking: vec![1, 0, 5],
    }
}

// ---------------------------------------------------------------------------
// Property helpers
// ---------------------------------------------------------------------------

fn make_upper_bounds_prop(id: &str, places: &[&str]) -> Property {
    Property {
        id: id.to_string(),
        formula: Formula::PlaceBound(places.iter().map(|p| (*p).to_string()).collect()),
    }
}

fn make_ef_prop(id: &str, pred: StatePredicate) -> Property {
    Property {
        id: id.to_string(),
        formula: Formula::Reachability(ReachabilityFormula {
            quantifier: PathQuantifier::EF,
            predicate: pred,
        }),
    }
}

fn make_ctl_prop(id: &str, ctl: CtlFormula) -> Property {
    Property {
        id: id.to_string(),
        formula: Formula::Ctl(ctl),
    }
}

fn make_ltl_prop(id: &str, ltl: LtlFormula) -> Property {
    Property {
        id: id.to_string(),
        formula: Formula::Ltl(ltl),
    }
}

// ---------------------------------------------------------------------------
// UpperBounds × constant place
// ---------------------------------------------------------------------------

/// Reduction removes P_const as constant. ExpandingObserver must restore its
/// value so the UpperBounds query sees the correct bound of 3.
#[test]
fn test_upper_bounds_constant_place_included_in_bound() {
    let props = vec![make_upper_bounds_prop("ub-const", &["P_const"])];
    let results = check_upper_bounds_properties(&constant_place_net(), &props, &default_config());
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].1, Some(3));
}

// ---------------------------------------------------------------------------
// Reachability × constant place
// ---------------------------------------------------------------------------

/// EF(P_const >= 3): the constant place always holds 3 tokens, so this is
/// trivially TRUE in the initial marking. Reduction removes P_const; the
/// observer must expand it back to 3 for predicate evaluation.
#[test]
fn test_reachability_cardinality_constant_place_predicate() {
    // EF(tokens(P_const) >= 3) i.e. EF(3 <= tokens(P_const))
    let pred = StatePredicate::IntLe(
        IntExpr::Constant(3),
        IntExpr::TokensCount(vec!["P_const".to_string()]),
    );
    let props = vec![make_ef_prop("reach-const", pred)];
    let results = check_reachability_properties(&constant_place_net(), &props, &default_config());
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].1, Verdict::True);
}

// ---------------------------------------------------------------------------
// Reachability × dead transition
// ---------------------------------------------------------------------------

/// EF(is-fireable(T_dead)): T_dead is structurally dead and gets removed by
/// reduction. The resolved predicate for a removed transition must evaluate
/// to FALSE across all reachable states.
#[test]
fn test_reachability_fireability_dead_transition_is_never_fireable() {
    let pred = StatePredicate::IsFireable(vec!["T_dead".to_string()]);
    let props = vec![make_ef_prop("reach-dead", pred)];
    let results = check_reachability_properties(&dead_transition_net(), &props, &default_config());
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].1, Verdict::False);
}

// ---------------------------------------------------------------------------
// UpperBounds × dead transition
// ---------------------------------------------------------------------------

/// Dead transition T_dead is removed by reduction. UpperBounds query on
/// P_live (which is not affected by the dead transition) must still report
/// the correct bound of 1 (P_live starts at 1, fires once to 0).
#[test]
fn test_upper_bounds_dead_transition_does_not_affect_bound() {
    let props = vec![make_upper_bounds_prop("ub-live", &["P_live"])];
    let results = check_upper_bounds_properties(&dead_transition_net(), &props, &default_config());
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].1, Some(1));
}

// ---------------------------------------------------------------------------
// Reachability AG × constant place
// ---------------------------------------------------------------------------

/// AG(P_const <= 3): universal path quantifier version. The constant place
/// always holds exactly 3 tokens. After reduction removes P_const, the
/// observer must expand it back to 3 for every explored marking.
#[test]
fn test_reachability_ag_constant_place_predicate() {
    let pred = StatePredicate::IntLe(
        IntExpr::TokensCount(vec!["P_const".to_string()]),
        IntExpr::Constant(3),
    );
    let props = vec![Property {
        id: "reach-ag-const".to_string(),
        formula: Formula::Reachability(ReachabilityFormula {
            quantifier: PathQuantifier::AG,
            predicate: pred,
        }),
    }];
    let results = check_reachability_properties(&constant_place_net(), &props, &default_config());
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].1, Verdict::True);
}

// ---------------------------------------------------------------------------
// CTL × constant place
// ---------------------------------------------------------------------------

/// AG(P_const <= 3): since P_const is always exactly 3, this is TRUE on all
/// reachable states. Post-exploration batch expansion must restore P_const
/// values in the full reachability graph for correct CTL evaluation.
#[test]
fn test_ctl_cardinality_constant_place_in_formula() {
    // AG(tokens(P_const) <= 3) i.e. AG(IntLe(TokensCount([P_const]), Constant(3)))
    let atom = StatePredicate::IntLe(
        IntExpr::TokensCount(vec!["P_const".to_string()]),
        IntExpr::Constant(3),
    );
    let ctl = CtlFormula::AG(Box::new(CtlFormula::Atom(atom)));
    let props = vec![make_ctl_prop("ctl-const", ctl)];
    let results = check_ctl_properties(&constant_place_net(), &props, &default_config());
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].1, Verdict::True);
}

// ---------------------------------------------------------------------------
// LTL × constant place
// ---------------------------------------------------------------------------

/// G(P_const <= 3): same predicate as CTL but through the Büchi product
/// construction. The LTL checker batch-expands all stored markings and must
/// restore P_const = 3 for correct temporal evaluation.
#[test]
fn test_ltl_cardinality_constant_place_in_formula() {
    let atom = StatePredicate::IntLe(
        IntExpr::TokensCount(vec!["P_const".to_string()]),
        IntExpr::Constant(3),
    );
    let ltl = LtlFormula::Globally(Box::new(LtlFormula::Atom(atom)));
    let props = vec![make_ltl_prop("ltl-const", ltl)];
    let results = check_ltl_properties(&constant_place_net(), &props, &default_config());
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].1, Verdict::True);
}

// ---------------------------------------------------------------------------
// CTL × dead transition
// ---------------------------------------------------------------------------

/// AG(NOT is-fireable(T_dead)): the dead transition can never fire, so the
/// negated fireability holds across all reachable states. After reduction
/// removes T_dead, the CTL checker must correctly resolve the IsFireable
/// predicate for the removed transition as FALSE.
#[test]
fn test_ctl_fireability_dead_transition_always_not_fireable() {
    let atom = StatePredicate::Not(Box::new(StatePredicate::IsFireable(vec![
        "T_dead".to_string()
    ])));
    let ctl = CtlFormula::AG(Box::new(CtlFormula::Atom(atom)));
    let props = vec![make_ctl_prop("ctl-dead", ctl)];
    let results = check_ctl_properties(&dead_transition_net(), &props, &default_config());
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].1, Verdict::True);
}

// ---------------------------------------------------------------------------
// LTL × dead transition
// ---------------------------------------------------------------------------

/// G(NOT is-fireable(T_dead)): LTL version of the dead-transition fireability
/// check. The Büchi product must correctly resolve the predicate for a
/// transition that was removed during reduction.
#[test]
fn test_ltl_fireability_dead_transition_always_not_fireable() {
    let atom = StatePredicate::Not(Box::new(StatePredicate::IsFireable(vec![
        "T_dead".to_string()
    ])));
    let ltl = LtlFormula::Globally(Box::new(LtlFormula::Atom(atom)));
    let props = vec![make_ltl_prop("ltl-dead", ltl)];
    let results = check_ltl_properties(&dead_transition_net(), &props, &default_config());
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].1, Verdict::True);
}

// ---------------------------------------------------------------------------
// UpperBounds × isolated place
// ---------------------------------------------------------------------------

/// P_iso has 5 tokens and no transitions. Reduction removes it as isolated.
/// ExpandingObserver must restore P_iso=5 so the UpperBounds query reports
/// the correct bound.
#[test]
fn test_upper_bounds_isolated_place_included_in_bound() {
    let props = vec![make_upper_bounds_prop("ub-iso", &["P_iso"])];
    let results = check_upper_bounds_properties(&isolated_place_net(), &props, &default_config());
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].1, Some(5));
}

// ---------------------------------------------------------------------------
// Reachability × isolated place
// ---------------------------------------------------------------------------

/// EF(P_iso >= 5): the isolated place always holds 5 tokens. After reduction
/// removes P_iso, the observer must expand it back to 5 for predicate
/// evaluation.
#[test]
fn test_reachability_cardinality_isolated_place_predicate() {
    let pred = StatePredicate::IntLe(
        IntExpr::Constant(5),
        IntExpr::TokensCount(vec!["P_iso".to_string()]),
    );
    let props = vec![make_ef_prop("reach-iso", pred)];
    let results = check_reachability_properties(&isolated_place_net(), &props, &default_config());
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].1, Verdict::True);
}

// ---------------------------------------------------------------------------
// CTL × isolated place
// ---------------------------------------------------------------------------

/// AG(P_iso <= 5): the isolated place never changes from 5. Post-exploration
/// batch expansion must restore P_iso=5 in every expanded marking.
#[test]
fn test_ctl_cardinality_isolated_place_in_formula() {
    let atom = StatePredicate::IntLe(
        IntExpr::TokensCount(vec!["P_iso".to_string()]),
        IntExpr::Constant(5),
    );
    let ctl = CtlFormula::AG(Box::new(CtlFormula::Atom(atom)));
    let props = vec![make_ctl_prop("ctl-iso", ctl)];
    let results = check_ctl_properties(&isolated_place_net(), &props, &default_config());
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].1, Verdict::True);
}

// ---------------------------------------------------------------------------
// LTL × isolated place
// ---------------------------------------------------------------------------

/// G(P_iso <= 5): LTL version of the isolated-place cardinality check.
/// The Büchi product must correctly expand markings to include the removed
/// isolated place.
#[test]
fn test_ltl_cardinality_isolated_place_in_formula() {
    let atom = StatePredicate::IntLe(
        IntExpr::TokensCount(vec!["P_iso".to_string()]),
        IntExpr::Constant(5),
    );
    let ltl = LtlFormula::Globally(Box::new(LtlFormula::Atom(atom)));
    let props = vec![make_ltl_prop("ltl-iso", ltl)];
    let results = check_ltl_properties(&isolated_place_net(), &props, &default_config());
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].1, Verdict::True);
}
