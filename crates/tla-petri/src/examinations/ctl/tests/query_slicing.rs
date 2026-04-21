// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::check_ctl_properties;
use super::support::{
    build_ctl_slice, check_ctl_properties_unsliced, component_a_ctl_props,
    disconnected_two_component_net, make_ctl_prop,
};

use crate::explorer::ExplorationConfig;
use crate::output::Verdict;
use crate::property_xml::{CtlFormula, IntExpr, StatePredicate};

#[test]
fn test_ctl_query_slicing_single_component() {
    // EF(tokens(a1) >= 1): only references component A.
    // Query slicing should explore only component A (2 states) not the full
    // 4-state product. The answer is TRUE (a0=1 fires ta to reach a1=1).
    let net = disconnected_two_component_net();
    let props = vec![make_ctl_prop(
        "slice-a",
        CtlFormula::EF(Box::new(CtlFormula::Atom(StatePredicate::IntLe(
            IntExpr::Constant(1),
            IntExpr::TokensCount(vec![String::from("a1")]),
        )))),
    )];
    let config = ExplorationConfig::default();
    let results = check_ctl_properties(&net, &props, &config);
    assert_eq!(results[0].1, Verdict::True);
}

#[test]
fn test_ctl_query_slicing_both_components() {
    // AG(tokens(a0) + tokens(a1) + tokens(b0) + tokens(b1) <= 2):
    // references both components. No slicing possible. TRUE because each
    // component is conserving (1 token each, total always 2).
    let net = disconnected_two_component_net();
    let props = vec![make_ctl_prop(
        "no-slice",
        CtlFormula::AG(Box::new(CtlFormula::Atom(StatePredicate::IntLe(
            IntExpr::TokensCount(vec![
                String::from("a0"),
                String::from("a1"),
                String::from("b0"),
                String::from("b1"),
            ]),
            IntExpr::Constant(2),
        )))),
    )];
    let config = ExplorationConfig::default();
    let results = check_ctl_properties(&net, &props, &config);
    assert_eq!(results[0].1, Verdict::True);
}

#[test]
fn test_ctl_query_slicing_fireability() {
    let net = disconnected_two_component_net();
    let props = vec![make_ctl_prop(
        "slice-fire",
        CtlFormula::EF(Box::new(CtlFormula::Atom(StatePredicate::IsFireable(
            vec![String::from("ta")],
        )))),
    )];
    let (reduced, slice) =
        build_ctl_slice(&net, &props).expect("fireability-only CTL support should slice");
    assert!(slice.net.num_places() < reduced.net.num_places());
    assert!(slice.net.num_transitions() < reduced.net.num_transitions());

    let config = ExplorationConfig::new(2);
    let results = check_ctl_properties(&net, &props, &config);
    assert_eq!(results[0].1, Verdict::True);
}

#[test]
fn test_ctl_query_slicing_shrinks_disconnected_component() {
    let net = disconnected_two_component_net();
    let props = component_a_ctl_props();
    let (reduced, slice) =
        build_ctl_slice(&net, &props).expect("component-local CTL properties should slice");

    assert!(slice.net.num_places() < reduced.net.num_places());
    assert!(slice.net.num_transitions() < reduced.net.num_transitions());
}

#[test]
fn test_ctl_query_slicing_matches_unsliced_results() {
    let net = disconnected_two_component_net();
    let props = component_a_ctl_props();
    let config = ExplorationConfig::default();

    let sliced = check_ctl_properties(&net, &props, &config);
    let unsliced = check_ctl_properties_unsliced(&net, &props, &config);

    assert_eq!(sliced, unsliced);
}
