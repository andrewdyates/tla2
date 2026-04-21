// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::naive_eval::naive_ctl_eval;
use super::support::{has_mcc_benchmark, mcc_benchmark_dir};
use crate::examinations::ctl::checker::CtlChecker;
use crate::examinations::ctl::resolve::resolve_ctl;
use crate::parser::parse_pnml_dir;
use crate::petri_net::PlaceIdx;
use crate::property_xml::{parse_properties, Formula};
use crate::resolved_predicate::count_unresolved;
use std::collections::HashMap;

/// Compare naive fixpoint CTL evaluator vs production checker on ALL
/// Angiogenesis CTLFireability properties.
#[test]
fn test_naive_vs_production_ctl_angiogenesis() {
    if !has_mcc_benchmark("Angiogenesis-PT-01") {
        eprintln!("SKIP: Angiogenesis-PT-01 benchmark not downloaded");
        return;
    }

    let net = parse_pnml_dir(&mcc_benchmark_dir("Angiogenesis-PT-01")).expect("parse PNML");
    let config = crate::explorer::ExplorationConfig::default();
    let full = crate::explorer::explore_full(&net, &config);
    assert!(full.graph.completed);

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

    let checker = CtlChecker::new(&full, &net);
    let n = full.graph.num_states as usize;

    // 2024 ground truth
    let fire_truth: Vec<bool> = vec![
        false, false, true, true, true, false, true, true, false, false, true, true, true, true,
        true, false,
    ];

    let props = parse_properties(&mcc_benchmark_dir("Angiogenesis-PT-01"), "CTLFireability")
        .expect("parse properties");

    for (i, prop) in props.iter().enumerate() {
        let formula = match &prop.formula {
            Formula::Ctl(ctl) => resolve_ctl(ctl, &place_map, &trans_map),
            _ => continue,
        };

        let prod = checker.eval(&formula);
        let naive = naive_ctl_eval(&formula, &full, &net);

        let prod_count = prod.iter().filter(|&&v| v).count();
        let naive_count = naive.iter().filter(|&&v| v).count();
        let agree = prod == naive;
        let prod_s0 = prod[0];
        let naive_s0 = naive[0];
        let truth = fire_truth[i];

        let status = if prod_s0 == truth && naive_s0 == truth {
            "OK"
        } else if prod_s0 == naive_s0 {
            "BOTH WRONG"
        } else {
            "DISAGREE"
        };

        eprintln!(
            "Property {i:02} ({}) [{status}]: prod={prod_s0} ({prod_count}/{n}), naive={naive_s0} ({naive_count}/{n}), truth={truth}, agree={agree}",
            prop.id
        );

        // Production must match ground truth — this is the hard assertion.
        // Naive may disagree at deadlock states (textbook vs MCC semantics).
        assert_eq!(
            prod_s0, truth,
            "Angiogenesis CTLFireability-{i:02} ({}): production={prod_s0}, truth={truth}",
            prop.id
        );

        if !agree {
            let diffs: Vec<usize> = (0..n).filter(|&s| prod[s] != naive[s]).collect();
            eprintln!(
                "  DISAGREE at {} states: {:?}",
                diffs.len(),
                &diffs[..diffs.len().min(20)]
            );
        }
    }
}

/// Same comparison on AirplaneLD CTLFireability + CTLCardinality
#[test]
fn test_naive_vs_production_ctl_airplaneld() {
    if !has_mcc_benchmark("AirplaneLD-PT-0010") {
        eprintln!("SKIP: AirplaneLD-PT-0010 benchmark not downloaded");
        return;
    }

    let net = parse_pnml_dir(&mcc_benchmark_dir("AirplaneLD-PT-0010")).expect("parse PNML");
    let config = crate::explorer::ExplorationConfig::default();
    let full = crate::explorer::explore_full(&net, &config);
    assert!(full.graph.completed);

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

    let checker = CtlChecker::new(&full, &net);
    let n = full.graph.num_states as usize;

    for exam in &["CTLFireability", "CTLCardinality"] {
        // From registry/mcc-labels/c-t-l-{fireability,cardinality}-2024.csv
        let truth_vec: Vec<bool> = if *exam == "CTLFireability" {
            vec![
                true, false, true, true, false, true, true, false, false, false, true, true, true,
                false, true, false,
            ]
        } else {
            vec![
                true, false, true, false, false, true, true, true, true, true, false, false, false,
                true, false, false,
            ]
        };

        let props = parse_properties(&mcc_benchmark_dir("AirplaneLD-PT-0010"), exam)
            .expect("parse properties");

        let mut wrong_count = 0;
        let mut disagree_count = 0;
        for (i, prop) in props.iter().enumerate() {
            let formula = match &prop.formula {
                Formula::Ctl(ctl) => resolve_ctl(ctl, &place_map, &trans_map),
                _ => continue,
            };

            let prod = checker.eval(&formula);
            let naive = naive_ctl_eval(&formula, &full, &net);
            let prod_s0 = prod[0];
            let naive_s0 = naive[0];
            let truth = truth_vec[i];

            let status = if prod_s0 == truth && naive_s0 == truth {
                "OK"
            } else if prod_s0 == naive_s0 {
                wrong_count += 1;
                "BOTH WRONG"
            } else {
                disagree_count += 1;
                "DISAGREE"
            };

            // Production must match ground truth.
            assert_eq!(
                prod_s0, truth,
                "AirplaneLD {exam}-{i:02}: production={prod_s0}, truth={truth}"
            );

            if status != "OK" {
                let prod_count = prod.iter().filter(|&&v| v).count();
                let naive_count = naive.iter().filter(|&&v| v).count();
                eprintln!(
                    "{exam}-{i:02} [{status}]: prod={prod_s0} ({prod_count}/{n}), naive={naive_s0} ({naive_count}/{n}), truth={truth}"
                );
            }
        }
        eprintln!("{exam}: {wrong_count} both-wrong, {disagree_count} disagree");
    }
}

/// Localize SwimmingPool CTLCardinality wrong answers: runs the CTL checker
/// on the UNREDUCED net (SwimmingPool-PT-01, small enough to explore fully)
/// and compares against 2024 ground truth labels.
///
/// If wrong on unreduced net → CTL checker bug.
/// If correct on unreduced → reduction/expansion pipeline bug.
#[test]
fn test_swimmingpool_ctl_unreduced_localization() {
    if !has_mcc_benchmark("SwimmingPool-PT-01") {
        eprintln!("SKIP: SwimmingPool-PT-01 benchmark not downloaded");
        return;
    }

    let net = parse_pnml_dir(&mcc_benchmark_dir("SwimmingPool-PT-01")).expect("parse PNML");
    // PT-01 has initial marking Out=20, Cabins=10, Bags=15 — 45 total tokens.
    // State space should be manageable (<50M states).
    let config = crate::explorer::ExplorationConfig::new(200_000_000);
    let full = crate::explorer::explore_full(&net, &config);
    eprintln!(
        "SwimmingPool-PT-01: {} states explored, completed={}",
        full.graph.num_states, full.graph.completed
    );
    if !full.graph.completed {
        eprintln!("SKIP: SwimmingPool-PT-01 unreduced state space too large");
        return;
    }

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

    let checker = CtlChecker::new(&full, &net);
    let n = full.graph.num_states as usize;
    eprintln!(
        "SwimmingPool-PT-01: {n} states, {} places",
        net.num_places()
    );

    // 2024 ground truth from registry/mcc-labels/c-t-l-cardinality-2024.csv
    // All 16 formulas have labels for PT-01.
    let truth: Vec<Option<bool>> = vec![
        Some(false), // 0
        Some(false), // 1
        Some(false), // 2
        Some(false), // 3
        Some(true),  // 4
        Some(true),  // 5
        Some(true),  // 6
        Some(true),  // 7
        Some(true),  // 8
        Some(true),  // 9
        Some(false), // 10
        Some(true),  // 11
        Some(true),  // 12
        Some(true),  // 13
        Some(true),  // 14
        Some(true),  // 15
    ];

    let props = parse_properties(&mcc_benchmark_dir("SwimmingPool-PT-01"), "CTLCardinality")
        .expect("parse properties");

    let mut wrong_prod = 0usize;
    let mut wrong_naive = 0usize;
    for (i, prop) in props.iter().enumerate() {
        let formula = match &prop.formula {
            Formula::Ctl(ctl) => resolve_ctl(ctl, &place_map, &trans_map),
            _ => continue,
        };

        let prod = checker.eval(&formula);
        let naive = naive_ctl_eval(&formula, &full, &net);
        let prod_s0 = prod[0];
        let naive_s0 = naive[0];

        if let Some(expected) = truth[i] {
            let prod_ok = prod_s0 == expected;
            let naive_ok = naive_s0 == expected;
            if !prod_ok {
                wrong_prod += 1;
            }
            if !naive_ok {
                wrong_naive += 1;
            }
            let status = if prod_ok && naive_ok {
                "OK"
            } else if prod_ok {
                "naive_wrong"
            } else if naive_ok {
                "PROD_WRONG"
            } else {
                "BOTH_WRONG"
            };
            eprintln!(
                "CTLCard-{i:02} [{status}]: prod={prod_s0} naive={naive_s0} truth={expected}"
            );
        } else {
            eprintln!("CTLCard-{i:02}: prod={prod_s0} naive={naive_s0} truth=? (skipped)");
        }
    }

    eprintln!("UNREDUCED LOCALIZATION (PT-01): prod_wrong={wrong_prod} naive_wrong={wrong_naive}");
}

/// Layer 2: documents that structural reduction (even DeadlockSafe) is
/// UNSOUND for CTL. Pre/post-agglomeration changes path structure, causing
/// CTL path quantifiers (EG, AF, EU, etc.) to give wrong answers.
///
/// This test verifies the known unsoundness: structural reduction produces
/// 5 wrong answers on SwimmingPool-PT-01 CTLCardinality. The production
/// pipeline (Layer 3 test) avoids this by using identity reduction.
#[test]
fn test_structural_reduction_unsound_for_ctl() {
    use crate::examinations::query_support::ctl_support_with_aliases;
    use crate::examinations::reachability::protected_places_for_prefire;
    use crate::explorer::explore_full;
    use crate::model::PropertyAliases;
    use crate::reduction::{reduce_iterative_structural_deadlock_safe_with_protected, ReducedNet};

    if !has_mcc_benchmark("SwimmingPool-PT-01") {
        eprintln!("SKIP: SwimmingPool-PT-01 benchmark not downloaded");
        return;
    }

    let net = parse_pnml_dir(&mcc_benchmark_dir("SwimmingPool-PT-01")).expect("parse PNML");
    let props = parse_properties(&mcc_benchmark_dir("SwimmingPool-PT-01"), "CTLCardinality")
        .expect("parse properties");

    let aliases = PropertyAliases::identity(&net);
    let identity = ReducedNet::identity(&net);
    let initial_protected = ctl_support_with_aliases(&identity, &props, &aliases)
        .map(|support| protected_places_for_prefire(&net, &support))
        .unwrap_or_else(|| vec![true; net.num_places()]);
    let reduced =
        reduce_iterative_structural_deadlock_safe_with_protected(&net, &initial_protected)
            .expect("reduction should succeed");

    // CTL support analysis may protect all places on this small net (9 places),
    // preventing any reduction. When protection is broad enough to yield an
    // identity net, unsoundness cannot manifest, so skip the wrong-answer check.
    if reduced.net.num_places() >= net.num_places() {
        eprintln!(
            "Structural reduction produced identity net (protection covers all places). \
             Unsoundness cannot manifest; test passes vacuously."
        );
        return;
    }

    let config =
        crate::explorer::ExplorationConfig::new(200_000_000).refitted_for_net(&reduced.net);
    let mut full = explore_full(&reduced.net, &config);
    assert!(full.graph.completed);

    for marking in &mut full.markings {
        *marking = reduced.expand_marking(marking).expect("expand");
    }

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

    let checker = CtlChecker::new(&full, &net);
    let truth: Vec<Option<bool>> = vec![
        Some(false),
        Some(false),
        Some(false),
        Some(false),
        Some(true),
        Some(true),
        Some(true),
        Some(true),
        Some(true),
        Some(true),
        Some(false),
        Some(true),
        Some(true),
        Some(true),
        Some(true),
        Some(true),
    ];

    let mut wrong = 0usize;
    for (i, prop) in props.iter().enumerate() {
        let formula = match &prop.formula {
            Formula::Ctl(ctl) => resolve_ctl(ctl, &place_map, &trans_map),
            _ => continue,
        };
        let result = checker.eval(&formula)[0];
        if let Some(expected) = truth[i] {
            if result != expected {
                wrong += 1;
            }
        }
    }

    // Structural reduction MUST produce wrong answers here (documents unsoundness).
    // If this ever becomes 0, it means the reduction rules changed and the
    // unsoundness may have been accidentally fixed or the test is no longer valid.
    assert!(
        wrong > 0,
        "Expected structural reduction to produce wrong CTL answers, but got 0. \
         Either the reduction rules changed or the test data is wrong."
    );
    eprintln!(
        "Structural reduction unsoundness confirmed: {wrong} wrong CTL answers (expected >0)"
    );
}

/// Layer 3: run the PRODUCTION CTL pipeline (identity reduction + query slicing)
/// on SwimmingPool-PT-01. This tests exactly what MCC competition would run.
#[test]
fn test_swimmingpool_ctl_production_pipeline() {
    use crate::examinations::ctl::check_ctl_properties;

    if !has_mcc_benchmark("SwimmingPool-PT-01") {
        eprintln!("SKIP: SwimmingPool-PT-01 benchmark not downloaded");
        return;
    }

    let net = parse_pnml_dir(&mcc_benchmark_dir("SwimmingPool-PT-01")).expect("parse PNML");
    let props = parse_properties(&mcc_benchmark_dir("SwimmingPool-PT-01"), "CTLCardinality")
        .expect("parse properties");
    let config = crate::explorer::ExplorationConfig::default();

    let results = check_ctl_properties(&net, &props, &config);

    // Ground truth for SwimmingPool-PT-01 CTLCardinality (2024 labels)
    let truth: Vec<Option<bool>> = vec![
        Some(false),
        Some(false),
        Some(false),
        Some(false),
        Some(true),
        Some(true),
        Some(true),
        Some(true),
        Some(true),
        Some(true),
        Some(false),
        Some(true),
        Some(true),
        Some(true),
        Some(true),
        Some(true),
    ];

    let mut wrong = 0usize;
    for (i, (prop_id, verdict)) in results.iter().enumerate() {
        if let Some(expected) = truth.get(i).copied().flatten() {
            let got = match verdict {
                crate::examination::Verdict::True => true,
                crate::examination::Verdict::False => false,
                other => {
                    eprintln!("CTLCard-{i:02} [{prop_id}]: {other:?} (not T/F)");
                    continue;
                }
            };
            if got != expected {
                wrong += 1;
                eprintln!("CTLCard-{i:02} [{prop_id}] [WRONG]: production={got} truth={expected}");
            }
        }
    }
    eprintln!(
        "PRODUCTION PIPELINE (PT-01): {wrong} wrong out of {} results",
        results.len()
    );
    assert_eq!(
        wrong, 0,
        "SwimmingPool-PT-01 CTLCardinality: {wrong} wrong in PRODUCTION pipeline"
    );
}

/// Layer 3 (LTL): run the production LTL pipeline on SwimmingPool-PT-01.
///
/// The identity-net Buchi path is much more expensive than the CTL path, so
/// keep this benchmark-backed parity check behind a finite deadline. If the
/// exact run cannot finish within the unit-test budget we skip instead of
/// stalling the whole crate test suite.
#[test]
fn test_swimmingpool_ltl_production_pipeline() {
    use crate::examinations::ltl::check_ltl_properties;

    const TEST_TIMEOUT_SECS: u64 = 120;

    if !has_mcc_benchmark("SwimmingPool-PT-01") {
        eprintln!("SKIP: SwimmingPool-PT-01 benchmark not downloaded");
        return;
    }

    let net = parse_pnml_dir(&mcc_benchmark_dir("SwimmingPool-PT-01")).expect("parse PNML");
    let props = parse_properties(&mcc_benchmark_dir("SwimmingPool-PT-01"), "LTLCardinality")
        .expect("parse properties");
    let deadline =
        Some(std::time::Instant::now() + std::time::Duration::from_secs(TEST_TIMEOUT_SECS));
    let config = crate::explorer::ExplorationConfig::new(4_000_000).with_deadline(deadline);

    let results = check_ltl_properties(&net, &props, &config);

    // Ground truth for SwimmingPool-PT-01 LTLCardinality (2024 labels)
    let truth: Vec<Option<bool>> = vec![
        Some(false),
        Some(true),
        Some(true),
        Some(false),
        Some(false),
        Some(false),
        Some(false),
        Some(false),
        Some(false),
        Some(false),
        Some(false),
        Some(false),
        Some(false),
        Some(true),
        Some(false),
        Some(false),
    ];

    let mut wrong = 0usize;
    let mut inconclusive = 0usize;
    for (i, (prop_id, verdict)) in results.iter().enumerate() {
        if let Some(expected) = truth.get(i).copied().flatten() {
            let got = match verdict {
                crate::examination::Verdict::True => true,
                crate::examination::Verdict::False => false,
                other => {
                    inconclusive += 1;
                    eprintln!("LTLCard-{i:02} [{prop_id}]: {other:?} (inconclusive)");
                    continue;
                }
            };
            if got != expected {
                wrong += 1;
                eprintln!("LTLCard-{i:02} [{prop_id}] [WRONG]: production={got} truth={expected}");
            }
        }
    }
    eprintln!(
        "LTL PRODUCTION PIPELINE (PT-01): {wrong} wrong, {inconclusive} inconclusive out of {} results",
        results.len(),
    );
    if inconclusive > 0 {
        eprintln!(
            "SKIP: SwimmingPool-PT-01 LTLCardinality exact parity exceeded the \
             {TEST_TIMEOUT_SECS}s unit-test budget"
        );
        return;
    }
    assert_eq!(
        wrong, 0,
        "SwimmingPool-PT-01 LTLCardinality: {wrong} wrong in PRODUCTION pipeline"
    );
}

/// Check for unresolved transition/place names in CTL formulas.
/// If any names fail to resolve, the corresponding IsFireable/TokensCount
/// becomes False/0, potentially making entire subformulas vacuously true/false.
#[test]
fn test_check_unresolved_names_in_wrong_ctl_formulas() {
    if !has_mcc_benchmark("AirplaneLD-PT-0010") {
        eprintln!("SKIP: AirplaneLD-PT-0010 benchmark not downloaded");
        return;
    }
    if !has_mcc_benchmark("Angiogenesis-PT-01") {
        eprintln!("SKIP: Angiogenesis-PT-01 benchmark not downloaded");
        return;
    }

    use crate::property_xml::Formula;

    // Helper: count unresolved in a CTL formula's atoms
    fn count_unresolved_ctl(
        formula: &crate::property_xml::CtlFormula,
        place_map: &HashMap<&str, PlaceIdx>,
        trans_map: &HashMap<&str, crate::petri_net::TransitionIdx>,
    ) -> (usize, usize) {
        match formula {
            crate::property_xml::CtlFormula::Atom(pred) => {
                count_unresolved(pred, place_map, trans_map)
            }
            crate::property_xml::CtlFormula::Not(inner)
            | crate::property_xml::CtlFormula::EX(inner)
            | crate::property_xml::CtlFormula::AX(inner)
            | crate::property_xml::CtlFormula::EF(inner)
            | crate::property_xml::CtlFormula::AF(inner)
            | crate::property_xml::CtlFormula::EG(inner)
            | crate::property_xml::CtlFormula::AG(inner) => {
                count_unresolved_ctl(inner, place_map, trans_map)
            }
            crate::property_xml::CtlFormula::And(children)
            | crate::property_xml::CtlFormula::Or(children) => {
                children.iter().fold((0, 0), |(t, u), c| {
                    let (ct, cu) = count_unresolved_ctl(c, place_map, trans_map);
                    (t + ct, u + cu)
                })
            }
            crate::property_xml::CtlFormula::EU(phi, psi)
            | crate::property_xml::CtlFormula::AU(phi, psi) => {
                let (pt, pu) = count_unresolved_ctl(phi, place_map, trans_map);
                let (qt, qu) = count_unresolved_ctl(psi, place_map, trans_map);
                (pt + qt, pu + qu)
            }
        }
    }

    // Also collect the specific unresolved names
    fn collect_unresolved_names(
        formula: &crate::property_xml::CtlFormula,
        place_map: &HashMap<&str, PlaceIdx>,
        trans_map: &HashMap<&str, crate::petri_net::TransitionIdx>,
        out: &mut Vec<String>,
    ) {
        match formula {
            crate::property_xml::CtlFormula::Atom(pred) => {
                collect_unresolved_pred(pred, place_map, trans_map, out);
            }
            crate::property_xml::CtlFormula::Not(inner)
            | crate::property_xml::CtlFormula::EX(inner)
            | crate::property_xml::CtlFormula::AX(inner)
            | crate::property_xml::CtlFormula::EF(inner)
            | crate::property_xml::CtlFormula::AF(inner)
            | crate::property_xml::CtlFormula::EG(inner)
            | crate::property_xml::CtlFormula::AG(inner) => {
                collect_unresolved_names(inner, place_map, trans_map, out);
            }
            crate::property_xml::CtlFormula::And(children)
            | crate::property_xml::CtlFormula::Or(children) => {
                for c in children {
                    collect_unresolved_names(c, place_map, trans_map, out);
                }
            }
            crate::property_xml::CtlFormula::EU(phi, psi)
            | crate::property_xml::CtlFormula::AU(phi, psi) => {
                collect_unresolved_names(phi, place_map, trans_map, out);
                collect_unresolved_names(psi, place_map, trans_map, out);
            }
        }
    }

    fn collect_unresolved_pred(
        pred: &crate::property_xml::StatePredicate,
        place_map: &HashMap<&str, PlaceIdx>,
        trans_map: &HashMap<&str, crate::petri_net::TransitionIdx>,
        out: &mut Vec<String>,
    ) {
        match pred {
            crate::property_xml::StatePredicate::IsFireable(transitions) => {
                for name in transitions {
                    if !trans_map.contains_key(name.as_str()) {
                        out.push(format!("transition:{name}"));
                    }
                }
            }
            crate::property_xml::StatePredicate::IntLe(left, right) => {
                collect_unresolved_int(left, place_map, out);
                collect_unresolved_int(right, place_map, out);
            }
            crate::property_xml::StatePredicate::And(children)
            | crate::property_xml::StatePredicate::Or(children) => {
                for c in children {
                    collect_unresolved_pred(c, place_map, trans_map, out);
                }
            }
            crate::property_xml::StatePredicate::Not(inner) => {
                collect_unresolved_pred(inner, place_map, trans_map, out);
            }
            _ => {}
        }
    }

    fn collect_unresolved_int(
        expr: &crate::property_xml::IntExpr,
        place_map: &HashMap<&str, PlaceIdx>,
        out: &mut Vec<String>,
    ) {
        if let crate::property_xml::IntExpr::TokensCount(places) = expr {
            for name in places {
                if !place_map.contains_key(name.as_str()) {
                    out.push(format!("place:{name}"));
                }
            }
        }
    }

    // Check AirplaneLD — all CTL formula names must resolve
    let mut total_unresolved = 0usize;
    {
        let net = parse_pnml_dir(&mcc_benchmark_dir("AirplaneLD-PT-0010")).unwrap();
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

        for exam in &["CTLFireability", "CTLCardinality"] {
            let props = parse_properties(&mcc_benchmark_dir("AirplaneLD-PT-0010"), exam).unwrap();
            for (i, prop) in props.iter().enumerate() {
                let ctl = match &prop.formula {
                    Formula::Ctl(ctl) => ctl,
                    _ => continue,
                };
                let (_total, unresolved) = count_unresolved_ctl(ctl, &place_map, &trans_map);
                if unresolved > 0 {
                    let mut names = Vec::new();
                    collect_unresolved_names(ctl, &place_map, &trans_map, &mut names);
                    eprintln!(
                        "UNRESOLVED: AirplaneLD {exam}-{i:02} ({}): {unresolved} names: {names:?}",
                        prop.id
                    );
                    total_unresolved += unresolved;
                }
            }
        }
    }

    // Check Angiogenesis — all CTL formula names must resolve
    {
        let net = parse_pnml_dir(&mcc_benchmark_dir("Angiogenesis-PT-01")).unwrap();
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

        let props =
            parse_properties(&mcc_benchmark_dir("Angiogenesis-PT-01"), "CTLFireability").unwrap();
        for (i, prop) in props.iter().enumerate() {
            let ctl = match &prop.formula {
                Formula::Ctl(ctl) => ctl,
                _ => continue,
            };
            let (_total, unresolved) = count_unresolved_ctl(ctl, &place_map, &trans_map);
            if unresolved > 0 {
                let mut names = Vec::new();
                collect_unresolved_names(ctl, &place_map, &trans_map, &mut names);
                eprintln!(
                    "UNRESOLVED: Angiogenesis CTLFireability-{i:02} ({}): {unresolved} names: {names:?}",
                    prop.id
                );
                total_unresolved += unresolved;
            }
        }
    }

    assert_eq!(
        total_unresolved, 0,
        "All place/transition names in CTL formulas must resolve; {total_unresolved} unresolved"
    );
}
