// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use super::*;
use crate::buchi::{check_ltl_on_the_fly, resolve_atom_with_aliases};
use crate::model::PropertyAliases;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
use crate::property_xml::{
    parse_properties, Formula, IntExpr, LtlFormula, Property, StatePredicate,
};
use crate::reduction::ReducedNet;

fn cyclic_net() -> PetriNet {
    // p0 -> t0 -> p1 -> t1 -> p0, initial marking [1, 0]
    // States: [1,0] <-> [0,1] — cycle
    PetriNet {
        name: Some("cyclic".to_string()),
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

fn make_ltl_prop(id: &str, ltl: LtlFormula) -> Property {
    Property {
        id: id.to_string(),
        formula: Formula::Ltl(ltl),
    }
}

fn benchmark_model_dir(model: &str) -> PathBuf {
    Path::new("benchmarks/mcc/2024/INPUTS").join(model)
}

fn load_real_ltl_property(
    model: &str,
    examination: &str,
    property_id: &str,
) -> Option<(PetriNet, Property)> {
    let model_dir = benchmark_model_dir(model);
    if !model_dir.join("model.pnml").exists() {
        return None;
    }

    let net = crate::parser::parse_pnml_dir(&model_dir).expect("real benchmark PNML should parse");
    let property = parse_properties(&model_dir, examination)
        .expect("real benchmark property XML should parse")
        .into_iter()
        .find(|prop| prop.id == property_id)
        .expect("property id should exist in benchmark XML");
    Some((net, property))
}

fn lookup_registry_verdict(path: &Path, model: &str, formula_index: usize) -> Option<Verdict> {
    if !path.exists() {
        return None;
    }

    let needle = format!("{model}/{formula_index},");
    let contents = std::fs::read_to_string(path).expect("registry CSV should read");
    let line = contents.lines().find(|line| line.starts_with(&needle))?;
    let raw = line
        .split_once(',')
        .expect("registry line should contain a comma")
        .1;
    Some(match raw {
        "true" => Verdict::True,
        "false" => Verdict::False,
        other => panic!("unexpected registry verdict {other}"),
    })
}

fn check_ltl_property_unguarded(
    net: &PetriNet,
    property: &Property,
    config: &ExplorationConfig,
) -> Verdict {
    let Formula::Ltl(ltl) = &property.formula else {
        return Verdict::CannotCompute;
    };

    let aliases = PropertyAliases::identity(net);
    let mut atom_preds = Vec::new();
    let nnf = to_nnf(ltl, &mut atom_preds);
    let resolved_atoms: Vec<_> = atom_preds
        .iter()
        .map(|pred| resolve_atom_with_aliases(pred, &aliases))
        .collect();

    // Use identity reduction (no-op) since this helper tests on the raw net.
    let reduced = ReducedNet::identity(net);
    match check_ltl_on_the_fly(
        &nnf,
        net,
        &reduced,
        net,
        &resolved_atoms,
        None,
        config.max_states(),
        config.deadline(),
    ) {
        Ok(Some(true)) => Verdict::True,
        Ok(Some(false)) => Verdict::False,
        Ok(None) => Verdict::CannotCompute,
        Err(error) => {
            panic!("on-the-fly LTL expansion should not overflow in test helper: {error}")
        }
    }
}

#[test]
fn test_ltl_globally_atom() {
    // A(G(tokens(p0) + tokens(p1) <= 1)) — conserving net, always true
    let net = cyclic_net();
    let props = vec![make_ltl_prop(
        "g-00",
        LtlFormula::Globally(Box::new(LtlFormula::Atom(StatePredicate::IntLe(
            IntExpr::TokensCount(vec!["p0".to_string(), "p1".to_string()]),
            IntExpr::Constant(1),
        )))),
    )];
    let config = ExplorationConfig::default();
    let results = check_ltl_properties(&net, &props, &config);
    assert_eq!(results[0].1, Verdict::True);
}

#[test]
fn test_ltl_unguarded_tight_budget_returns_cannot_compute() {
    let net = cyclic_net();
    let property = make_ltl_prop(
        "tight-budget-ltl-unguarded",
        LtlFormula::Globally(Box::new(LtlFormula::Atom(StatePredicate::True))),
    );
    let verdict = check_ltl_property_unguarded(&net, &property, &ExplorationConfig::new(1));
    assert_eq!(verdict, Verdict::CannotCompute);
}

#[test]
fn test_ltl_unguarded_expired_deadline_returns_cannot_compute() {
    let net = cyclic_net();
    let property = make_ltl_prop(
        "expired-deadline-ltl-unguarded",
        LtlFormula::Globally(Box::new(LtlFormula::Finally(Box::new(LtlFormula::Atom(
            StatePredicate::IntLe(
                IntExpr::Constant(1),
                IntExpr::TokensCount(vec!["p0".to_string()]),
            ),
        ))))),
    );
    let config =
        ExplorationConfig::default().with_deadline(Some(Instant::now() - Duration::from_secs(1)));
    let verdict = check_ltl_property_unguarded(&net, &property, &config);
    assert_eq!(verdict, Verdict::CannotCompute);
}

#[test]
fn test_fair_share_budget_divides_remaining_time() {
    assert_eq!(
        fair_share_budget(Duration::from_secs(9), 3),
        Duration::from_secs(3)
    );
    // Duration / u32 preserves sub-millisecond remainder: 7ms / 4 = 1.75ms
    assert_eq!(
        fair_share_budget(Duration::from_millis(7), 4),
        Duration::from_micros(1750)
    );
}

#[test]
fn test_ltl_previously_guarded_ids_now_execute_normally() {
    // After the guard-timing fix (#1246), the 5 previously-guarded property
    // IDs now execute normally instead of returning CannotCompute.
    let net = cyclic_net();
    let config = ExplorationConfig::default();
    let formerly_guarded_ids = [
        "AirplaneLD-PT-0010-LTLCardinality-04",
        "AirplaneLD-PT-0010-LTLCardinality-09",
        "CSRepetitions-PT-02-LTLCardinality-03",
        "Anderson-PT-04-LTLFireability-02",
        "CSRepetitions-PT-02-LTLFireability-03",
    ];
    let props: Vec<_> = formerly_guarded_ids
        .iter()
        .map(|id| {
            make_ltl_prop(
                id,
                LtlFormula::Globally(Box::new(LtlFormula::Atom(StatePredicate::IntLe(
                    IntExpr::TokensCount(vec!["p0".to_string(), "p1".to_string()]),
                    IntExpr::Constant(1),
                )))),
            )
        })
        .collect();

    let results = check_ltl_properties(&net, &props, &config);
    for (id, verdict) in &results {
        assert_ne!(
            *verdict,
            Verdict::CannotCompute,
            "{id} should execute normally after guard-timing fix"
        );
    }
}

#[test]
fn test_ltl_adjacent_property_id_still_executes() {
    let net = cyclic_net();
    let props = vec![make_ltl_prop(
        "AirplaneLD-PT-0010-LTLCardinality-05",
        LtlFormula::Globally(Box::new(LtlFormula::Atom(StatePredicate::IntLe(
            IntExpr::TokensCount(vec!["p0".to_string(), "p1".to_string()]),
            IntExpr::Constant(1),
        )))),
    )];
    let config = ExplorationConfig::default();
    let results = check_ltl_properties(&net, &props, &config);
    assert_eq!(results[0].1, Verdict::True);
}

#[test]
fn test_ltl_finally_atom() {
    // A(F(tokens(p1) >= 1)) — cyclic net always reaches p1=1
    let net = cyclic_net();
    let props = vec![make_ltl_prop(
        "f-00",
        LtlFormula::Finally(Box::new(LtlFormula::Atom(StatePredicate::IntLe(
            IntExpr::Constant(1),
            IntExpr::TokensCount(vec!["p1".to_string()]),
        )))),
    )];
    let config = ExplorationConfig::default();
    let results = check_ltl_properties(&net, &props, &config);
    assert_eq!(results[0].1, Verdict::True);
}

#[test]
fn test_ltl_globally_finally() {
    // A(G(F(tokens(p0) >= 1))) — on the cycle, p0=1 recurs infinitely
    let net = cyclic_net();
    let props = vec![make_ltl_prop(
        "gf-00",
        LtlFormula::Globally(Box::new(LtlFormula::Finally(Box::new(LtlFormula::Atom(
            StatePredicate::IntLe(
                IntExpr::Constant(1),
                IntExpr::TokensCount(vec!["p0".to_string()]),
            ),
        ))))),
    )];
    let config = ExplorationConfig::default();
    let results = check_ltl_properties(&net, &props, &config);
    assert_eq!(results[0].1, Verdict::True);
}

#[test]
fn test_ltl_globally_false() {
    // A(G(tokens(p0) >= 1)) — false because state [0,1] has p0=0
    let net = cyclic_net();
    let props = vec![make_ltl_prop(
        "g-01",
        LtlFormula::Globally(Box::new(LtlFormula::Atom(StatePredicate::IntLe(
            IntExpr::Constant(1),
            IntExpr::TokensCount(vec!["p0".to_string()]),
        )))),
    )];
    let config = ExplorationConfig::default();
    let results = check_ltl_properties(&net, &props, &config);
    assert_eq!(results[0].1, Verdict::False);
}

// ── Regression tests for the 5 formerly-wrong LTL properties ──────
//
// These properties previously returned wrong answers due to successor-state
// guard timing in the Buchi product construction (see #1246). After the fix,
// the production path now correctly uses current-state guards and all 5
// match ground truth.

#[test]
fn test_regression_airplane_ltl_cardinality_04_matches_ground_truth() {
    let Some((net, property)) = load_real_ltl_property(
        "AirplaneLD-PT-0010",
        "LTLCardinality",
        "AirplaneLD-PT-0010-LTLCardinality-04",
    ) else {
        return;
    };

    let expected = lookup_registry_verdict(
        Path::new("registry/mcc-labels/l-t-l-cardinality-2024.csv"),
        "AirplaneLD-PT-0010",
        4,
    )
    .expect("ground truth should contain AirplaneLD-PT-0010/4");
    let verdict = check_ltl_property_unguarded(&net, &property, &ExplorationConfig::default());

    assert_eq!(expected, Verdict::False);
    assert_eq!(
        verdict, expected,
        "formerly wrong — fixed by #1246 guard-timing fix"
    );
}

#[test]
fn test_regression_airplane_ltl_cardinality_05_matches_ground_truth() {
    let Some((net, property)) = load_real_ltl_property(
        "AirplaneLD-PT-0010",
        "LTLCardinality",
        "AirplaneLD-PT-0010-LTLCardinality-05",
    ) else {
        return;
    };

    let expected = lookup_registry_verdict(
        Path::new("registry/mcc-labels/l-t-l-cardinality-2024.csv"),
        "AirplaneLD-PT-0010",
        5,
    )
    .expect("ground truth should contain AirplaneLD-PT-0010/5");
    let verdict = check_ltl_property_unguarded(&net, &property, &ExplorationConfig::default());

    assert_eq!(expected, Verdict::True);
    assert_eq!(verdict, expected);
}

#[test]
fn test_regression_airplane_ltl_cardinality_09_matches_ground_truth() {
    let Some((net, property)) = load_real_ltl_property(
        "AirplaneLD-PT-0010",
        "LTLCardinality",
        "AirplaneLD-PT-0010-LTLCardinality-09",
    ) else {
        return;
    };

    let expected = lookup_registry_verdict(
        Path::new("registry/mcc-labels/l-t-l-cardinality-2024.csv"),
        "AirplaneLD-PT-0010",
        9,
    )
    .expect("ground truth should contain AirplaneLD-PT-0010/9");
    let verdict = check_ltl_property_unguarded(&net, &property, &ExplorationConfig::default());

    assert_eq!(expected, Verdict::False);
    assert_eq!(
        verdict, expected,
        "formerly wrong — fixed by #1246 guard-timing fix"
    );
}

#[test]
fn test_regression_csrepetitions_ltl_cardinality_03_matches_ground_truth() {
    let Some((net, property)) = load_real_ltl_property(
        "CSRepetitions-PT-02",
        "LTLCardinality",
        "CSRepetitions-PT-02-LTLCardinality-03",
    ) else {
        return;
    };

    let expected = lookup_registry_verdict(
        Path::new("registry/mcc-labels/l-t-l-cardinality-2024.csv"),
        "CSRepetitions-PT-02",
        3,
    )
    .expect("ground truth should contain CSRepetitions-PT-02/3");
    let verdict = check_ltl_property_unguarded(&net, &property, &ExplorationConfig::default());

    assert_eq!(expected, Verdict::False);
    assert_eq!(
        verdict, expected,
        "formerly wrong — fixed by #1246 guard-timing fix"
    );
}

#[test]
fn test_regression_anderson_ltl_fireability_02_matches_ground_truth() {
    let Some((net, property)) = load_real_ltl_property(
        "Anderson-PT-04",
        "LTLFireability",
        "Anderson-PT-04-LTLFireability-02",
    ) else {
        return;
    };

    let expected = lookup_registry_verdict(
        Path::new("registry/mcc-labels/l-t-l-fireability-2024.csv"),
        "Anderson-PT-04",
        2,
    )
    .expect("ground truth should contain Anderson-PT-04/2");
    let verdict = check_ltl_property_unguarded(&net, &property, &ExplorationConfig::default());

    assert_eq!(expected, Verdict::False);
    assert_eq!(
        verdict, expected,
        "formerly wrong — fixed by #1246 guard-timing fix"
    );
}

#[test]
fn test_regression_csrepetitions_ltl_fireability_03_matches_ground_truth() {
    let Some((net, property)) = load_real_ltl_property(
        "CSRepetitions-PT-02",
        "LTLFireability",
        "CSRepetitions-PT-02-LTLFireability-03",
    ) else {
        return;
    };

    let expected = lookup_registry_verdict(
        Path::new("registry/mcc-labels/l-t-l-fireability-2024.csv"),
        "CSRepetitions-PT-02",
        3,
    )
    .expect("ground truth should contain CSRepetitions-PT-02/3");
    let verdict = check_ltl_property_unguarded(&net, &property, &ExplorationConfig::default());

    assert_eq!(expected, Verdict::False);
    assert_eq!(
        verdict, expected,
        "formerly wrong — fixed by #1246 guard-timing fix"
    );
}

// ── Shallow LTL classification tests ──────────────────────────────

fn some_pred() -> StatePredicate {
    StatePredicate::IntLe(
        IntExpr::TokensCount(vec!["p0".to_string()]),
        IntExpr::Constant(1),
    )
}

#[test]
fn test_classify_g_atom_is_invariant() {
    let f = LtlFormula::Globally(Box::new(LtlFormula::Atom(some_pred())));
    assert!(matches!(
        classify_shallow_ltl(&f),
        Some(ShallowLtl::Invariant(_))
    ));
}

#[test]
fn test_classify_f_atom_is_eventually() {
    let f = LtlFormula::Finally(Box::new(LtlFormula::Atom(some_pred())));
    assert!(matches!(
        classify_shallow_ltl(&f),
        Some(ShallowLtl::Eventually(_))
    ));
}

#[test]
fn test_classify_not_f_atom_is_invariant() {
    // Not(F(atom)) = G(Not(atom)) = AG(Not(atom))
    let f = LtlFormula::Not(Box::new(LtlFormula::Finally(Box::new(LtlFormula::Atom(
        some_pred(),
    )))));
    assert!(matches!(
        classify_shallow_ltl(&f),
        Some(ShallowLtl::Invariant(_))
    ));
}

#[test]
fn test_classify_not_g_atom_is_eventually() {
    // Not(G(atom)) = F(Not(atom)) = AF(Not(atom))
    let f = LtlFormula::Not(Box::new(LtlFormula::Globally(Box::new(LtlFormula::Atom(
        some_pred(),
    )))));
    assert!(matches!(
        classify_shallow_ltl(&f),
        Some(ShallowLtl::Eventually(_))
    ));
}

#[test]
fn test_classify_g_g_atom_is_invariant() {
    // G(G(atom)) = AG(atom) — idempotent
    let f = LtlFormula::Globally(Box::new(LtlFormula::Globally(Box::new(LtlFormula::Atom(
        some_pred(),
    )))));
    assert!(matches!(
        classify_shallow_ltl(&f),
        Some(ShallowLtl::Invariant(_))
    ));
}

#[test]
fn test_classify_f_f_atom_is_eventually() {
    // F(F(atom)) = AF(atom) — idempotent
    let f = LtlFormula::Finally(Box::new(LtlFormula::Finally(Box::new(LtlFormula::Atom(
        some_pred(),
    )))));
    assert!(matches!(
        classify_shallow_ltl(&f),
        Some(ShallowLtl::Eventually(_))
    ));
}

#[test]
fn test_classify_f_g_is_deep() {
    // F(G(atom)) — persistence, not shallow
    let f = LtlFormula::Finally(Box::new(LtlFormula::Globally(Box::new(LtlFormula::Atom(
        some_pred(),
    )))));
    assert!(classify_shallow_ltl(&f).is_none());
}

#[test]
fn test_classify_g_f_is_deep() {
    // G(F(atom)) — recurrence, not shallow
    let f = LtlFormula::Globally(Box::new(LtlFormula::Finally(Box::new(LtlFormula::Atom(
        some_pred(),
    )))));
    assert!(classify_shallow_ltl(&f).is_none());
}

#[test]
fn test_classify_until_is_deep() {
    let f = LtlFormula::Until(
        Box::new(LtlFormula::Atom(some_pred())),
        Box::new(LtlFormula::Atom(some_pred())),
    );
    assert!(classify_shallow_ltl(&f).is_none());
}

#[test]
fn test_classify_next_is_deep() {
    let f = LtlFormula::Next(Box::new(LtlFormula::Atom(some_pred())));
    assert!(classify_shallow_ltl(&f).is_none());
}

#[test]
fn test_classify_g_and_atoms_is_invariant() {
    // G(atom1 AND atom2) — conjunction of state preds
    let f = LtlFormula::Globally(Box::new(LtlFormula::And(vec![
        LtlFormula::Atom(some_pred()),
        LtlFormula::Atom(StatePredicate::True),
    ])));
    assert!(matches!(
        classify_shallow_ltl(&f),
        Some(ShallowLtl::Invariant(_))
    ));
}

#[test]
fn test_classify_g_nested_temporal_is_deep() {
    // G(atom AND F(atom)) — mixed: conjunction has temporal child
    let f = LtlFormula::Globally(Box::new(LtlFormula::And(vec![
        LtlFormula::Atom(some_pred()),
        LtlFormula::Finally(Box::new(LtlFormula::Atom(some_pred()))),
    ])));
    assert!(classify_shallow_ltl(&f).is_none());
}

// ── Routing parity: G(atom) via reachability matches Buchi ──

#[test]
fn test_shallow_g_invariant_matches_buchi_on_cyclic_net() {
    // G(tokens(p0) + tokens(p1) <= 1) is TRUE on the cyclic net.
    // Verify that the shallow routing (reachability) gives same answer.
    let net = cyclic_net();
    let config = ExplorationConfig::default();
    let props = vec![make_ltl_prop(
        "g-shallow",
        LtlFormula::Globally(Box::new(LtlFormula::Atom(StatePredicate::IntLe(
            IntExpr::TokensCount(vec!["p0".to_string(), "p1".to_string()]),
            IntExpr::Constant(1),
        )))),
    )];
    let results = check_ltl_properties(&net, &props, &config);
    assert_eq!(results[0].1, Verdict::True);
}

#[test]
fn test_shallow_g_false_invariant_matches_buchi() {
    // G(tokens(p0) >= 1) is FALSE — state [0,1] violates it.
    let net = cyclic_net();
    let config = ExplorationConfig::default();
    let props = vec![make_ltl_prop(
        "g-false-shallow",
        LtlFormula::Globally(Box::new(LtlFormula::Atom(StatePredicate::IntLe(
            IntExpr::Constant(1),
            IntExpr::TokensCount(vec!["p0".to_string()]),
        )))),
    )];
    let results = check_ltl_properties(&net, &props, &config);
    assert_eq!(results[0].1, Verdict::False);
}

#[test]
fn test_shallow_f_prefilter_true_via_ag() {
    // F(tokens(p0) + tokens(p1) <= 1) where the predicate is an invariant.
    // AG(pred) holds, so F(pred) = AF(pred) should be TRUE.
    let net = cyclic_net();
    let config = ExplorationConfig::default();
    let props = vec![make_ltl_prop(
        "f-prefilter-true",
        LtlFormula::Finally(Box::new(LtlFormula::Atom(StatePredicate::IntLe(
            IntExpr::TokensCount(vec!["p0".to_string(), "p1".to_string()]),
            IntExpr::Constant(1),
        )))),
    )];
    let results = check_ltl_properties(&net, &props, &config);
    assert_eq!(results[0].1, Verdict::True);
}

#[test]
fn test_mixed_shallow_and_deep_properties() {
    // Mix of G(atom) (shallow), G(F(atom)) (deep), and F(atom) (pre-filter).
    // All should produce correct results when processed together.
    let net = cyclic_net();
    let config = ExplorationConfig::default();
    let props = vec![
        // G(atom) — shallow invariant, TRUE
        make_ltl_prop(
            "mix-g",
            LtlFormula::Globally(Box::new(LtlFormula::Atom(StatePredicate::IntLe(
                IntExpr::TokensCount(vec!["p0".to_string(), "p1".to_string()]),
                IntExpr::Constant(1),
            )))),
        ),
        // G(F(atom)) — deep recurrence, TRUE on cycle
        make_ltl_prop(
            "mix-gf",
            LtlFormula::Globally(Box::new(LtlFormula::Finally(Box::new(LtlFormula::Atom(
                StatePredicate::IntLe(
                    IntExpr::Constant(1),
                    IntExpr::TokensCount(vec!["p0".to_string()]),
                ),
            ))))),
        ),
        // F(atom) — pre-filterable, TRUE (atom is invariant on this net)
        make_ltl_prop(
            "mix-f",
            LtlFormula::Finally(Box::new(LtlFormula::Atom(StatePredicate::IntLe(
                IntExpr::TokensCount(vec!["p0".to_string(), "p1".to_string()]),
                IntExpr::Constant(1),
            )))),
        ),
    ];
    let results = check_ltl_properties(&net, &props, &config);
    assert_eq!(results[0].0, "mix-g");
    assert_eq!(results[0].1, Verdict::True);
    assert_eq!(results[1].0, "mix-gf");
    assert_eq!(results[1].1, Verdict::True);
    assert_eq!(results[2].0, "mix-f");
    assert_eq!(results[2].1, Verdict::True);
}

#[test]
fn test_shallow_ltl_flush_returns_only_unflushed_results() {
    let net = cyclic_net();
    let config = ExplorationConfig::default();
    let props = vec![
        make_ltl_prop(
            "mix-g",
            LtlFormula::Globally(Box::new(LtlFormula::Atom(StatePredicate::IntLe(
                IntExpr::TokensCount(vec!["p0".to_string(), "p1".to_string()]),
                IntExpr::Constant(1),
            )))),
        ),
        make_ltl_prop(
            "mix-gf",
            LtlFormula::Globally(Box::new(LtlFormula::Finally(Box::new(LtlFormula::Atom(
                StatePredicate::IntLe(
                    IntExpr::Constant(1),
                    IntExpr::TokensCount(vec!["p0".to_string()]),
                ),
            ))))),
        ),
        make_ltl_prop(
            "mix-f",
            LtlFormula::Finally(Box::new(LtlFormula::Atom(StatePredicate::IntLe(
                IntExpr::TokensCount(vec!["p0".to_string(), "p1".to_string()]),
                IntExpr::Constant(1),
            )))),
        ),
    ];

    let results =
        check_ltl_properties_with_flush(&net, &props, &PropertyAliases::identity(&net), &config);

    assert_eq!(results, vec![(String::from("mix-gf"), Verdict::True)]);
}

#[test]
fn test_shallow_f_prefilter_false_via_ef() {
    // F(tokens(p0) >= 2) is FALSE — total tokens = 1, so tokens(p0) >= 2 is
    // unreachable. The EF shortcut should detect EF(pred)=FALSE and conclude
    // AF(pred)=FALSE without invoking the Buchi product.
    let net = cyclic_net();
    let config = ExplorationConfig::default();
    let props = vec![make_ltl_prop(
        "f-prefilter-false",
        LtlFormula::Finally(Box::new(LtlFormula::Atom(StatePredicate::IntLe(
            IntExpr::Constant(2),
            IntExpr::TokensCount(vec!["p0".to_string()]),
        )))),
    )];
    let results = check_ltl_properties(&net, &props, &config);
    assert_eq!(results[0].1, Verdict::False);
}

#[test]
fn test_shallow_f_falls_through_to_buchi_when_shortcuts_inconclusive() {
    // F(tokens(p0) <= 0) on the cyclic net:
    // - AG(p0<=0) = FALSE (initial [1,0] violates it) → no quick TRUE
    // - EF(p0<=0) = TRUE (state [0,1] satisfies it) → no quick FALSE
    // → Falls through to Buchi. Answer is TRUE because the net cycles and
    //   every path eventually reaches [0,1] where p0=0.
    let net = cyclic_net();
    let config = ExplorationConfig::default();
    let props = vec![make_ltl_prop(
        "f-buchi-fallthrough",
        LtlFormula::Finally(Box::new(LtlFormula::Atom(StatePredicate::IntLe(
            IntExpr::TokensCount(vec!["p0".to_string()]),
            IntExpr::Constant(0),
        )))),
    )];
    let results = check_ltl_properties(&net, &props, &config);
    assert_eq!(results[0].1, Verdict::True);
}
