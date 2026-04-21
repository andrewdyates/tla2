// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;
use std::path::PathBuf;

use crate::examination::{collect_examination_core, Examination, ExaminationValue, Verdict};
use crate::examinations::query_support::{reachability_support, visible_transitions_for_support};
use crate::examinations::reachability::{PropertyTracker, ReachabilityObserver};
use crate::explorer::{explore, ExplorationConfig};
use crate::model::load_model_dir;
use crate::property_xml::{parse_properties, Formula};
use crate::reduction::ReducedNet;
use crate::resolved_predicate::resolve_predicate_with_aliases;
use crate::stubborn::PorStrategy;

fn mcc_input_dir(model: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/mcc/2024/INPUTS")
        .join(model)
}

const OTHER_NEO_ELECTION_ISOLATED_PLACE_MODELS: &[&str] = &[
    "NeoElection-COL-3",
    "NeoElection-COL-4",
    "NeoElection-COL-5",
    "NeoElection-COL-6",
    "NeoElection-COL-7",
    "NeoElection-COL-8",
];

const EXPECTED_NEO_ELECTION_ISOLATED_PLACES: &[&str] = &["P-crashed", "P-dead", "P-electionFailed"];

fn sorted_isolated_place_ids(model_name: &str) -> Vec<String> {
    let colored =
        crate::hlpnml::parse_hlpnml_dir(&mcc_input_dir(model_name)).expect("model should parse");
    let connected_places: HashSet<&str> = colored
        .arcs
        .iter()
        .flat_map(|arc| [arc.source.as_str(), arc.target.as_str()])
        .collect();
    let mut isolated: Vec<String> = colored
        .places
        .iter()
        .filter(|place| !connected_places.contains(place.id.as_str()))
        .map(|place| place.id.clone())
        .collect();
    isolated.sort();
    isolated
}

#[test]
fn test_neo_election_rc03_full_pipeline_returns_false() {
    let model =
        load_model_dir(mcc_input_dir("NeoElection-COL-2")).expect("NeoElection-COL-2 should load");

    let records = collect_examination_core(
        model.net(),
        model.model_name(),
        model.model_dir(),
        model.aliases(),
        Examination::ReachabilityCardinality,
        &ExplorationConfig::new(50_000),
        false,
    )
    .expect("ReachabilityCardinality collection should succeed");

    let rc03 = records
        .into_iter()
        .find(|record| record.formula_id == "NeoElection-COL-2-ReachabilityCardinality-2024-03")
        .expect("RC-03 record should exist");

    assert_eq!(
        rc03.value,
        ExaminationValue::Verdict(Verdict::False),
        "RC-03 should be FALSE in the full reachability pipeline",
    );
}

fn simplified_rf_tracker(
    model_name: &str,
    property_suffix: &str,
) -> (crate::model::PreparedModel, PropertyTracker) {
    let model = load_model_dir(mcc_input_dir(model_name)).expect("model should load");
    let property_id = format!("{model_name}-ReachabilityFireability-2024-{property_suffix}");
    let property = parse_properties(model.model_dir(), "ReachabilityFireability")
        .expect("ReachabilityFireability properties should parse")
        .into_iter()
        .find(|prop| prop.id == property_id)
        .expect("target property should exist");
    let simplified = crate::formula_simplify::simplify_properties_with_aliases(
        model.net(),
        std::slice::from_ref(&property),
        model.aliases(),
    );
    let simplified_property = simplified
        .into_iter()
        .next()
        .expect("single-property simplification should return one property");
    let Formula::Reachability(rf) = &simplified_property.formula else {
        panic!("target property should remain a reachability formula");
    };
    let tracker = PropertyTracker {
        id: simplified_property.id.clone(),
        quantifier: rf.quantifier,
        predicate: resolve_predicate_with_aliases(&rf.predicate, model.aliases()),
        verdict: None,
        resolved_by: None,
        flushed: false,
    };
    (model, tracker)
}

#[test]
fn test_neo_election_rf09_collapsed_bfs_stays_false_with_and_without_por() {
    let (model, tracker) = simplified_rf_tracker("NeoElection-COL-2", "09");

    let base_config = ExplorationConfig::new(1_000_000).with_workers(1);
    let full_marking_config = base_config.clone().with_fingerprint_dedup(false);

    let mut full_observer = ReachabilityObserver::from_trackers(model.net(), vec![tracker.clone()]);
    let full_result = explore(model.net(), &base_config, &mut full_observer);
    let full_verdict = full_observer.results_completed()[0].1;
    eprintln!(
        "RF-09 no-POR BFS: completed={}, states={}, verdict={}",
        full_result.completed, full_result.states_visited, full_verdict,
    );
    assert!(
        full_result.completed,
        "RF-09 no-POR BFS should complete on the collapsed COL net",
    );
    assert!(
        !full_verdict,
        "RF-09 no-POR BFS should remain FALSE on the collapsed COL net",
    );

    let mut full_marking_observer =
        ReachabilityObserver::from_trackers(model.net(), vec![tracker.clone()]);
    let full_marking_result = explore(
        model.net(),
        &full_marking_config,
        &mut full_marking_observer,
    );
    let full_marking_verdict = full_marking_observer.results_completed()[0].1;
    eprintln!(
        "RF-09 no-POR BFS (full markings): completed={}, states={}, verdict={}",
        full_marking_result.completed, full_marking_result.states_visited, full_marking_verdict,
    );
    assert!(
        full_marking_result.completed,
        "RF-09 no-POR BFS with full-marking dedup should complete",
    );
    assert!(
        !full_marking_verdict,
        "RF-09 no-POR BFS with full-marking dedup should remain FALSE",
    );

    let reduced = ReducedNet::identity(model.net());
    let support = reachability_support(&reduced, std::slice::from_ref(&tracker))
        .expect("RF-09 reachability support should resolve");
    let visible = visible_transitions_for_support(model.net(), &support)
        .expect("RF-09 should induce a nontrivial POR visible set");
    let por_config = base_config.with_por(PorStrategy::SafetyPreserving { visible });

    let mut por_observer = ReachabilityObserver::from_trackers(model.net(), vec![tracker]);
    let por_result = explore(model.net(), &por_config, &mut por_observer);
    let por_verdict = por_observer.results_completed()[0].1;
    eprintln!(
        "RF-09 POR BFS: completed={}, states={}, verdict={}",
        por_result.completed, por_result.states_visited, por_verdict,
    );
    assert!(
        por_result.completed,
        "RF-09 POR BFS should complete on the collapsed COL net",
    );
    assert!(
        !por_verdict,
        "RF-09 POR BFS should remain FALSE on the collapsed COL net",
    );
}

/// Guard: strengthened criterion prevents collapsing on NeoElection-COL-2.
///
/// Even though `reduce_colored` is re-enabled (#1418), the strengthened
/// soundness criterion (all arcs of every touching transition must be uniform
/// and guard-free) prevents any places from being collapsed on this model.
#[test]
fn test_strengthened_criterion_no_neo_election_collapse() {
    let mut colored = crate::hlpnml::parse_hlpnml_dir(&mcc_input_dir("NeoElection-COL-2"))
        .expect("NeoElection-COL-2 HLPNML should parse");
    let report = crate::colored_reduce::reduce_colored(&mut colored);
    assert!(
        report.collapsed_places.is_empty(),
        "strengthened criterion should prevent NeoElection-COL-2 collapsing, \
         but {} places were collapsed: {:?}",
        report.collapsed_places.len(),
        report.collapsed_places,
    );
    assert_eq!(report.places_saved(), 0);
}

#[test]
fn test_other_neo_election_variants_skip_isolated_place_collapsing() {
    for model_name in OTHER_NEO_ELECTION_ISOLATED_PLACE_MODELS {
        let isolated = sorted_isolated_place_ids(model_name);
        assert_eq!(
            isolated,
            EXPECTED_NEO_ELECTION_ISOLATED_PLACES
                .iter()
                .map(|name| String::from(*name))
                .collect::<Vec<_>>(),
            "{model_name} should still exercise the isolated-place exclusion path",
        );

        let mut colored = crate::hlpnml::parse_hlpnml_dir(&mcc_input_dir(model_name))
            .expect("NeoElection sibling HLPNML should parse");
        let report = crate::colored_reduce::reduce_colored(&mut colored);
        eprintln!(
            "{model_name}: isolated={isolated:?}, collapsed={:?}",
            report.collapsed_places
        );
        assert!(
            report.collapsed_places.is_empty(),
            "{model_name} should not collapse isolated-place variants {:?}, but collapsed {:?}",
            isolated,
            report.collapsed_places,
        );
    }
}

/// Regression guard: production and uncollapsed pipelines agree on NeoElection RF (#1418).
///
/// With the strengthened criterion, collapsing is a no-op on NeoElection-COL-2
/// (no places pass the criterion). This test catches regressions if the
/// criterion is weakened or if collapsing is re-enabled unsoundly.
#[test]
fn test_production_vs_uncollapsed_firability_agreement() {
    // Load model via production path (collapsing re-enabled #1418).
    let production_model =
        load_model_dir(mcc_input_dir("NeoElection-COL-2")).expect("NeoElection-COL-2 should load");
    let production_results = collect_examination_core(
        production_model.net(),
        production_model.model_name(),
        production_model.model_dir(),
        production_model.aliases(),
        Examination::ReachabilityFireability,
        &ExplorationConfig::new(50_000),
        false,
    )
    .expect("RF collection should succeed on production net");

    // Load uncollapsed model for comparison.
    let dir = mcc_input_dir("NeoElection-COL-2");
    let colored =
        crate::hlpnml::parse_hlpnml_dir(&dir).expect("NeoElection-COL-2 HLPNML should parse");
    // Unfold without any collapsing for ground truth.
    let uncollapsed = crate::unfold::unfold_to_pt(&colored).expect("uncollapsed net should unfold");
    let uncollapsed_results = collect_examination_core(
        &uncollapsed.net,
        "NeoElection-COL-2",
        &dir,
        &uncollapsed.aliases,
        Examination::ReachabilityFireability,
        &ExplorationConfig::new(50_000),
        false,
    )
    .expect("RF collection should succeed on uncollapsed net");

    // Compare: no verdict disagreements should exist.
    // CannotCompute mismatches are acceptable — they mean the pipeline timed out
    // or hit a budget limit, not that collapsing produced a wrong answer. Only
    // flag when BOTH paths produce definitive verdicts (True/False) that differ.
    let mut wrong_answers = Vec::new();
    let mut cannot_compute_mismatches = Vec::new();
    for prod in &production_results {
        if let Some(uncol) = uncollapsed_results
            .iter()
            .find(|r| r.formula_id == prod.formula_id)
        {
            if prod.value != uncol.value {
                let is_cannot_compute = matches!(
                    prod.value,
                    ExaminationValue::Verdict(Verdict::CannotCompute)
                ) || matches!(
                    uncol.value,
                    ExaminationValue::Verdict(Verdict::CannotCompute)
                );
                if is_cannot_compute {
                    cannot_compute_mismatches.push(format!(
                        "{}: production={:?}, uncollapsed={:?}",
                        prod.formula_id, prod.value, uncol.value,
                    ));
                } else {
                    wrong_answers.push(format!(
                        "{}: production={:?}, uncollapsed={:?}",
                        prod.formula_id, prod.value, uncol.value,
                    ));
                }
            }
        }
    }

    for m in &cannot_compute_mismatches {
        eprintln!("Collapsing CannotCompute mismatch (benign): {m}");
    }
    for m in &wrong_answers {
        eprintln!("Collapsing WRONG ANSWER: {m}");
    }
    assert!(
        wrong_answers.is_empty(),
        "Strengthened collapsing should produce zero wrong-answer mismatches. \
         Found {} wrong answers — the collapsing criterion may need further tightening.",
        wrong_answers.len(),
    );
}
