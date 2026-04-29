// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for alias-aware CTL/LTL support walkers.

use crate::examinations::query_support::{
    ctl_support_with_aliases, ltl_property_support_with_aliases,
};
use crate::model::PropertyAliases;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionIdx, TransitionInfo};
use crate::property_xml::{CtlFormula, Formula, IntExpr, LtlFormula, Property, StatePredicate};
use crate::reduction::ReducedNet;

fn unfolded_alias_net() -> PetriNet {
    PetriNet {
        name: Some(String::from("alias-unfolded")),
        places: vec![
            PlaceInfo {
                id: String::from("Fork_0"),
                name: None,
            },
            PlaceInfo {
                id: String::from("Fork_1"),
                name: None,
            },
            PlaceInfo {
                id: String::from("Done"),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: String::from("Take_0"),
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
                id: String::from("Take_1"),
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

fn alias_tables(net: &PetriNet) -> PropertyAliases {
    let mut aliases = PropertyAliases::identity(net);
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
fn test_ctl_support_with_aliases_keeps_all_unfolded_dependencies() {
    let net = unfolded_alias_net();
    let reduced = ReducedNet::identity(&net);
    let aliases = alias_tables(&net);
    let properties = vec![Property {
        id: String::from("alias-ctl"),
        formula: Formula::Ctl(CtlFormula::AG(Box::new(CtlFormula::Atom(
            StatePredicate::And(vec![
                StatePredicate::IntLe(
                    IntExpr::Constant(2),
                    IntExpr::TokensCount(vec![String::from("Fork")]),
                ),
                StatePredicate::IsFireable(vec![String::from("Take")]),
            ]),
        )))),
    }];

    let support =
        ctl_support_with_aliases(&reduced, &properties, &aliases).expect("support should resolve");
    assert_eq!(support.places, vec![true, true, false]);
    assert_eq!(support.transitions, vec![true, true]);
}

#[test]
fn test_ltl_support_with_aliases_keeps_all_unfolded_dependencies() {
    let net = unfolded_alias_net();
    let reduced = ReducedNet::identity(&net);
    let aliases = alias_tables(&net);
    let property = Property {
        id: String::from("alias-ltl"),
        formula: Formula::Ltl(LtlFormula::Globally(Box::new(LtlFormula::Atom(
            StatePredicate::And(vec![
                StatePredicate::IntLe(
                    IntExpr::Constant(2),
                    IntExpr::TokensCount(vec![String::from("Fork")]),
                ),
                StatePredicate::IsFireable(vec![String::from("Take")]),
            ]),
        )))),
    };

    let support = ltl_property_support_with_aliases(&reduced, &property, &aliases)
        .expect("support should resolve");
    assert_eq!(support.places, vec![true, true, false]);
    assert_eq!(support.transitions, vec![true, true]);
}
