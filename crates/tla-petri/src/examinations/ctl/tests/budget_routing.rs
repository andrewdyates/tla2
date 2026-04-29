// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::local_checker::LocalCtlChecker;
use super::super::resolve::resolve_ctl_with_aliases;
use std::path::PathBuf;

use super::super::{
    check_ctl_properties, classify_shallow_ctl, classify_shallow_ctl_suffix,
    ctl_batch_contains_next_step, ctl_formula_contains_next_step,
};
use super::support::{
    atom_pred, check_ctl_properties_unsliced, component_a_ctl_props, ctl_budget_ag_fireable,
    ctl_budget_cycle_net, ctl_local_fallback_formula, ctl_local_fallback_net,
    disconnected_two_component_net, make_ctl_prop, simple_net, suffix_cycle_net, suffix_exit_net,
};

use crate::explorer::{explore_full, ExplorationConfig};
use crate::model::PropertyAliases;
use crate::output::Verdict;
use crate::parser::parse_pnml_dir;
use crate::property_xml::{parse_properties, CtlFormula, Formula, IntExpr, StatePredicate};

fn mcc_benchmark_dir(model: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("benchmarks")
        .join("mcc")
        .join("2024")
        .join("INPUTS")
        .join(model)
}

#[test]
fn test_ctl_budget_boundary_sufficient_resolves() {
    let props = vec![make_ctl_prop("ctl-budget-ok", ctl_budget_ag_fireable())];
    let results = check_ctl_properties(&ctl_budget_cycle_net(), &props, &ExplorationConfig::new(2));
    assert_eq!(
        results,
        vec![(String::from("ctl-budget-ok"), Verdict::True)]
    );
}

#[test]
fn test_ctl_budget_boundary_tight_resolved_by_shallow_routing() {
    // AG(is-fireable(t0 ∨ t1)) on a 2-state cycle is always TRUE.
    // Previously this returned CannotCompute because the exploration budget
    // was too small. With shallow routing, k-induction proves it directly.
    let props = vec![make_ctl_prop("ctl-budget-tight", ctl_budget_ag_fireable())];
    let results = check_ctl_properties(&ctl_budget_cycle_net(), &props, &ExplorationConfig::new(1));
    assert_eq!(
        results,
        vec![(String::from("ctl-budget-tight"), Verdict::True)]
    );
}

#[test]
fn test_ctl_formula_contains_next_step_unit() {
    // EX and AX are immediate-successor operators -> true.
    assert!(ctl_formula_contains_next_step(&CtlFormula::EX(Box::new(
        CtlFormula::Atom(StatePredicate::IntLe(
            IntExpr::Constant(0),
            IntExpr::Constant(1),
        )),
    ))));
    assert!(ctl_formula_contains_next_step(&CtlFormula::AX(Box::new(
        CtlFormula::Atom(StatePredicate::IntLe(
            IntExpr::Constant(0),
            IntExpr::Constant(1),
        )),
    ))));

    // EF, AF, EG, AG, EU, AU without EX/AX -> false.
    let atom = CtlFormula::Atom(StatePredicate::IntLe(
        IntExpr::Constant(0),
        IntExpr::Constant(1),
    ));
    assert!(!ctl_formula_contains_next_step(&CtlFormula::EF(Box::new(
        atom.clone()
    ))));
    assert!(!ctl_formula_contains_next_step(&CtlFormula::AG(Box::new(
        atom.clone()
    ))));
    assert!(!ctl_formula_contains_next_step(&CtlFormula::EU(
        Box::new(atom.clone()),
        Box::new(atom.clone()),
    )));

    // Nested EX inside AG -> true.
    assert!(ctl_formula_contains_next_step(&CtlFormula::AG(Box::new(
        CtlFormula::EX(Box::new(atom.clone())),
    ))));
}

#[test]
fn test_ctl_batch_gate_detects_ex_in_mixed_batch() {
    let safe_prop = make_ctl_prop(
        "safe",
        CtlFormula::AG(Box::new(CtlFormula::Atom(StatePredicate::IntLe(
            IntExpr::Constant(0),
            IntExpr::Constant(1),
        )))),
    );
    let ex_prop = make_ctl_prop(
        "has-ex",
        CtlFormula::EX(Box::new(CtlFormula::Atom(StatePredicate::IntLe(
            IntExpr::Constant(0),
            IntExpr::Constant(1),
        )))),
    );

    // Pure stutter-insensitive batch -> eligible for deep slice.
    assert!(!ctl_batch_contains_next_step(&[safe_prop.clone()]));

    // Mixed batch with EX -> not eligible.
    assert!(ctl_batch_contains_next_step(&[safe_prop, ex_prop]));
}

#[test]
fn test_ctl_deep_slice_verdict_parity_on_disconnected_net() {
    // Use the disconnected net with EF-only formulas (stutter-insensitive).
    // Production code uses the deep relevance cone; unsliced path doesn't.
    // Verdicts must match regardless.
    let net = disconnected_two_component_net();
    let props = component_a_ctl_props();
    let config = ExplorationConfig::default();

    let sliced = check_ctl_properties(&net, &props, &config);
    let unsliced = check_ctl_properties_unsliced(&net, &props, &config);
    assert_eq!(sliced, unsliced);
}

#[test]
fn test_ctl_fallback_with_ex_verdict_parity() {
    // EX(tokens(a1) >= 1) in the disconnected net. Contains EX, so the
    // batch stays on the conservative induced-subnet closure. Verdict
    // must still match the unsliced path.
    let net = disconnected_two_component_net();
    let props = vec![make_ctl_prop(
        "fallback-ex",
        CtlFormula::EX(Box::new(CtlFormula::Atom(StatePredicate::IntLe(
            IntExpr::Constant(1),
            IntExpr::TokensCount(vec![String::from("a1")]),
        )))),
    )];

    assert!(ctl_batch_contains_next_step(&props));

    let config = ExplorationConfig::default();
    let sliced = check_ctl_properties(&net, &props, &config);
    let unsliced = check_ctl_properties_unsliced(&net, &props, &config);
    assert_eq!(sliced, unsliced);
}

#[test]
fn test_ctl_local_fallback_recovers_deep_formula_when_full_graph_truncates() {
    let net = ctl_local_fallback_net();
    let props = vec![make_ctl_prop("local-deep", ctl_local_fallback_formula())];
    let config = ExplorationConfig::new(3);

    let results = check_ctl_properties(&net, &props, &config);
    assert_eq!(results, vec![(String::from("local-deep"), Verdict::True)]);
}

#[test]
fn test_local_checker_directly_proves_budget_limited_deep_formula() {
    let net = ctl_local_fallback_net();
    let aliases = PropertyAliases::identity(&net);
    let resolved = resolve_ctl_with_aliases(&ctl_local_fallback_formula(), &aliases);
    let mut checker = LocalCtlChecker::new(&net, &ExplorationConfig::new(3));

    assert_eq!(checker.eval_root(&resolved), Ok(true));
}

#[test]
fn test_ctl_local_fallback_recovers_real_mcc_formula_under_tight_budget() {
    const MODEL: &str = "AirplaneLD-PT-0010";
    const PROPERTY_ID: &str = "AirplaneLD-PT-0010-CTLFireability-2024-09";

    let model_dir = mcc_benchmark_dir(MODEL);
    if !model_dir.join("model.pnml").exists() {
        eprintln!("SKIP: {MODEL} benchmark not downloaded");
        return;
    }

    let net = parse_pnml_dir(&model_dir).expect("AirplaneLD-PT-0010 should parse");
    let properties =
        parse_properties(&model_dir, "CTLFireability").expect("CTLFireability XML should parse");
    let property = properties
        .into_iter()
        .find(|property| property.id == PROPERTY_ID)
        .expect("target AirplaneLD CTL property should exist");

    let ctl = match &property.formula {
        Formula::Ctl(ctl) => ctl,
        other => panic!("expected CTL formula, got {other:?}"),
    };
    assert!(
        ctl_formula_contains_next_step(ctl),
        "{PROPERTY_ID} should stay on the deep CTL lane, not a shallow shortcut"
    );
    assert!(
        classify_shallow_ctl(ctl).is_none() && classify_shallow_ctl_suffix(ctl).is_none(),
        "{PROPERTY_ID} should not be classified as a shallow reachability/suffix formula"
    );

    let config = ExplorationConfig::new(128);
    let full = explore_full(&net, &config);
    assert!(
        !full.graph.completed,
        "{PROPERTY_ID}: full-graph exploration should exceed the tight state budget"
    );

    let results = check_ctl_properties(&net, std::slice::from_ref(&property), &config);
    assert_eq!(
        results,
        vec![(String::from(PROPERTY_ID), Verdict::False)],
        "{PROPERTY_ID}: local CTL fallback should recover the exact MCC verdict under a tight budget"
    );
}

/// Cross-validate that LocalCtlChecker agrees with the full-graph CtlChecker
/// on every CTL operator (EX, AX, EF, AF, EG, AG, EU, AU) across three
/// structurally different small nets.
#[test]
fn test_local_checker_agrees_with_full_graph_on_all_operators() {
    use super::super::checker::CtlChecker;
    use super::super::resolve::resolve_ctl;
    use crate::explorer::explore_full;
    use crate::petri_net::PlaceIdx;
    use std::collections::HashMap;

    let nets = [
        ("simple", simple_net()),
        ("suffix-cycle", suffix_cycle_net()),
        ("suffix-exit", suffix_exit_net()),
    ];

    for (net_name, net) in &nets {
        let place_map: HashMap<&str, PlaceIdx> = net
            .places
            .iter()
            .enumerate()
            .map(|(i, p)| (p.id.as_str(), PlaceIdx(i as u32)))
            .collect();
        let trans_map: HashMap<&str, crate::petri_net::TransitionIdx> = net
            .transitions
            .iter()
            .enumerate()
            .map(|(i, t)| (t.id.as_str(), crate::petri_net::TransitionIdx(i as u32)))
            .collect();
        let aliases = PropertyAliases::identity(net);

        let p0 = net.places[0].id.as_str();
        let atom = CtlFormula::Atom(atom_pred(p0, 1));
        let atom_false = CtlFormula::Atom(atom_pred(p0, 999));

        let formulas: Vec<(&str, CtlFormula)> = vec![
            ("EX-true", CtlFormula::EX(Box::new(atom.clone()))),
            ("AX-true", CtlFormula::AX(Box::new(atom.clone()))),
            ("EF-true", CtlFormula::EF(Box::new(atom.clone()))),
            ("AF-true", CtlFormula::AF(Box::new(atom.clone()))),
            ("EG-true", CtlFormula::EG(Box::new(atom.clone()))),
            ("AG-true", CtlFormula::AG(Box::new(atom.clone()))),
            ("EX-false", CtlFormula::EX(Box::new(atom_false.clone()))),
            ("EF-false", CtlFormula::EF(Box::new(atom_false.clone()))),
            ("AG-false", CtlFormula::AG(Box::new(atom_false.clone()))),
            (
                "EU",
                CtlFormula::EU(Box::new(atom.clone()), Box::new(atom_false.clone())),
            ),
            (
                "AU",
                CtlFormula::AU(Box::new(atom.clone()), Box::new(atom_false.clone())),
            ),
            (
                "nested-EF-AG",
                CtlFormula::EF(Box::new(CtlFormula::AG(Box::new(atom.clone())))),
            ),
        ];

        // Full-graph checker
        let config = ExplorationConfig::default();
        let full = explore_full(net, &config);
        assert!(
            full.graph.completed,
            "{net_name}: full graph must complete for cross-validation"
        );
        let full_checker = CtlChecker::new(&full, net);

        for (label, formula) in &formulas {
            let resolved_full = resolve_ctl(formula, &place_map, &trans_map);
            let full_result = full_checker.eval(&resolved_full)[0];

            let resolved_local = resolve_ctl_with_aliases(formula, &aliases);
            let mut local_checker = LocalCtlChecker::new(net, &config);
            let local_result = local_checker
                .eval_root(&resolved_local)
                .unwrap_or_else(|e| panic!("{net_name}/{label}: local checker error: {e}"));

            assert_eq!(
                full_result, local_result,
                "{net_name}/{label}: full-graph={full_result}, local={local_result}"
            );
        }
    }
}
