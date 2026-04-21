// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::rc::Rc;
use std::time::Instant;

use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
use crate::property_xml::PathQuantifier;
use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};

use super::super::reachability::PropertyTracker;
use super::frontier::{BloomFilter, ScoredNode, TraceNode};
use super::heuristic::{heuristic_distance, HeuristicWeights};
use super::search::run_heuristic_seeding_params;
use crate::examinations::reachability_witness::{
    validation_targets_from_trackers, WitnessValidationContext,
};

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

fn transition(id: &str, inputs: Vec<Arc>, outputs: Vec<Arc>) -> TransitionInfo {
    TransitionInfo {
        id: id.to_string(),
        name: None,
        inputs,
        outputs,
    }
}

fn ef_tracker(id: &str, pred: ResolvedPredicate) -> PropertyTracker {
    PropertyTracker {
        id: id.to_string(),
        quantifier: PathQuantifier::EF,
        predicate: pred,
        verdict: None,
        resolved_by: None,
        flushed: false,
    }
}

fn ag_tracker(id: &str, pred: ResolvedPredicate) -> PropertyTracker {
    PropertyTracker {
        id: id.to_string(),
        quantifier: PathQuantifier::AG,
        predicate: pred,
        verdict: None,
        resolved_by: None,
        flushed: false,
    }
}

fn tokens_ge(place: u32, threshold: u64) -> ResolvedPredicate {
    ResolvedPredicate::IntLe(
        ResolvedIntExpr::Constant(threshold),
        ResolvedIntExpr::TokensCount(vec![PlaceIdx(place)]),
    )
}

/// Linear net: p0 →[t0]→ p1 →[t1]→ p2, initial: p0=5.
/// Heuristic search should find EF(tokens(p2) >= 5) deterministically
/// by always preferring forward transitions.
fn linear_net() -> PetriNet {
    PetriNet {
        name: Some("linear".to_string()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            transition("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            transition("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![5, 0, 0],
    }
}

#[test]
fn test_heuristic_distance_zero_at_target() {
    let weights = HeuristicWeights {
        place_targets: vec![(2, 5)],
    };
    // Marking already satisfies target (p2 >= 5).
    let marking = vec![0, 0, 5];
    assert_eq!(heuristic_distance(&marking, &weights), 0);
}

#[test]
fn test_heuristic_distance_positive_deficit() {
    let weights = HeuristicWeights {
        place_targets: vec![(2, 5)],
    };
    let marking = vec![5, 0, 2];
    assert_eq!(heuristic_distance(&marking, &weights), 3);
}

#[test]
fn test_heuristic_finds_directed_witness() {
    let net = linear_net();
    // EF(tokens(p2) >= 5) — requires 10 firings: 5× t0 then 5× t1.
    let pred = tokens_ge(2, 5);
    let mut trackers = vec![ef_tracker("prop_linear", pred)];
    let targets = validation_targets_from_trackers(&trackers);
    let validation = WitnessValidationContext::new(&net, &targets);

    run_heuristic_seeding_params(
        &net,
        &mut trackers,
        &validation,
        None,
        1_000_000,
        100_000,
        10_000,
    );

    assert_eq!(
        trackers[0].verdict,
        Some(true),
        "heuristic search should find directed witness"
    );
}

#[test]
fn test_heuristic_ag_counterexample() {
    // Mutex net: p_free(2) <-> p_critical via t_enter/t_exit.
    // AG(NOT(tokens(p_critical) >= 1)) = FALSE (t_enter makes p_critical >= 1).
    let net = PetriNet {
        name: Some("mutex".to_string()),
        places: vec![place("p_free"), place("p_critical")],
        transitions: vec![
            transition("t_enter", vec![arc(0, 1)], vec![arc(1, 1)]),
            transition("t_exit", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![2, 0],
    };
    let pred = ResolvedPredicate::Not(Box::new(tokens_ge(1, 1)));
    let mut trackers = vec![ag_tracker("prop_ag", pred)];
    let targets = validation_targets_from_trackers(&trackers);
    let validation = WitnessValidationContext::new(&net, &targets);

    run_heuristic_seeding_params(
        &net,
        &mut trackers,
        &validation,
        None,
        100_000,
        10_000,
        1_000,
    );

    assert_eq!(
        trackers[0].verdict,
        Some(false),
        "heuristic search should find AG counterexample"
    );
}

#[test]
fn test_heuristic_respects_budget() {
    // One-safe net with unreachable predicate. Should exhaust budget without OOM.
    let net = PetriNet {
        name: Some("one_safe".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            transition("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            transition("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };
    let pred = tokens_ge(1, 100);
    let mut trackers = vec![ef_tracker("prop_budget", pred)];
    let targets = validation_targets_from_trackers(&trackers);
    let validation = WitnessValidationContext::new(&net, &targets);

    // Small budget — should finish quickly.
    run_heuristic_seeding_params(&net, &mut trackers, &validation, None, 100, 1_000, 100);

    // Should remain unresolved (unreachable property).
    assert_eq!(trackers[0].verdict, None);
}

#[test]
fn test_heuristic_respects_deadline() {
    let net = PetriNet {
        name: Some("one_safe".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            transition("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            transition("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };
    let pred = tokens_ge(1, 100);
    let mut trackers = vec![ef_tracker("prop_deadline", pred)];
    let targets = validation_targets_from_trackers(&trackers);
    let validation = WitnessValidationContext::new(&net, &targets);

    let deadline = Some(Instant::now());
    run_heuristic_seeding_params(
        &net,
        &mut trackers,
        &validation,
        deadline,
        1_000_000,
        100_000,
        10_000,
    );

    assert_eq!(trackers[0].verdict, None, "should respect passed deadline");
}

#[test]
fn test_bloom_filter_basic() {
    let mut bloom = BloomFilter::new(1000);
    let m1 = vec![1u64, 2, 3];

    assert!(!bloom.probably_contains(&m1));
    bloom.insert(&m1);
    assert!(bloom.probably_contains(&m1));
}

#[test]
fn test_heuristic_initial_marking_satisfies() {
    // Initial marking already satisfies EF(tokens(p0) >= 5).
    let net = linear_net();
    let pred = tokens_ge(0, 5);
    let mut trackers = vec![ef_tracker("prop_init", pred)];
    let targets = validation_targets_from_trackers(&trackers);
    let validation = WitnessValidationContext::new(&net, &targets);

    run_heuristic_seeding_params(&net, &mut trackers, &validation, None, 100, 1000, 100);

    assert_eq!(
        trackers[0].verdict,
        Some(true),
        "initial marking should satisfy EF immediately"
    );
}

// ── MCC ground truth soundness tests ─────────────────────────────

fn workspace_root() -> std::path::PathBuf {
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
}

fn mcc_model_dir(model: &str) -> std::path::PathBuf {
    workspace_root()
        .join("benchmarks")
        .join("mcc")
        .join("2024")
        .join("INPUTS")
        .join(model)
}

fn has_mcc_benchmark(model: &str) -> bool {
    mcc_model_dir(model).join("model.pnml").exists()
}

fn registry_path(file_name: &str) -> std::path::PathBuf {
    workspace_root()
        .join("registry")
        .join("mcc-labels")
        .join(file_name)
}

/// Load ground truth verdicts from the MCC registry CSV.
/// Returns a Vec<bool> indexed by formula position (0-based).
fn load_ground_truth(csv_file: &str, model: &str) -> Vec<bool> {
    let path = registry_path(csv_file);
    let contents = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("registry CSV {csv_file} should read: {e}"));
    let mut rows: Vec<(usize, bool)> = contents
        .lines()
        .filter_map(|line| {
            let (lhs, rhs) = line.split_once(',')?;
            let (row_model, raw_index) = lhs.rsplit_once('/')?;
            if row_model != model {
                return None;
            }
            let index: usize = raw_index.parse().expect("formula index should parse");
            let verdict = match rhs {
                "true" => true,
                "false" => false,
                other => panic!("unexpected registry verdict {other}"),
            };
            Some((index, verdict))
        })
        .collect();
    rows.sort_by_key(|(index, _)| *index);
    assert!(!rows.is_empty(), "registry should have entries for {model}");
    rows.into_iter().map(|(_, v)| v).collect()
}

/// Build PropertyTrackers from parsed MCC properties for a given model.
fn build_trackers_from_properties(
    net: &PetriNet,
    model: &str,
    examination: &str,
) -> Vec<PropertyTracker> {
    use crate::model::PropertyAliases;
    use crate::property_xml::{parse_properties, Formula, ReachabilityFormula};
    use crate::resolved_predicate::resolve_predicate_with_aliases;

    let model_dir = mcc_model_dir(model);
    let properties = parse_properties(&model_dir, examination)
        .unwrap_or_else(|e| panic!("property XML for {examination} should parse: {e}"));
    let aliases = PropertyAliases::identity(net);

    properties
        .iter()
        .filter_map(|prop| {
            let Formula::Reachability(ReachabilityFormula {
                quantifier,
                predicate,
            }) = &prop.formula
            else {
                return None;
            };
            let resolved = resolve_predicate_with_aliases(predicate, &aliases);
            Some(PropertyTracker {
                id: prop.id.clone(),
                quantifier: *quantifier,
                predicate: resolved,
                verdict: None,
                resolved_by: None,
                flushed: false,
            })
        })
        .collect()
}

/// Extract the formula index from a property ID like "Model-Exam-NN".
fn formula_index(id: &str) -> usize {
    id.rsplit_once('-')
        .expect("formula id should contain an index suffix")
        .1
        .parse::<usize>()
        .expect("formula index should parse")
}

/// Verify heuristic search soundness on an MCC model:
/// - Every verdict produced must match MCC ground truth
/// - EF trackers can only get verdict=Some(true)
/// - AG trackers can only get verdict=Some(false)
fn verify_heuristic_soundness(
    net: &PetriNet,
    trackers: &mut Vec<PropertyTracker>,
    ground_truth: &[bool],
    context: &str,
) {
    // Run heuristic search with generous budget (Angiogenesis has 110 states).
    let targets = validation_targets_from_trackers(trackers);
    let validation = WitnessValidationContext::new(net, &targets);
    run_heuristic_seeding_params(
        net,
        trackers,
        &validation,
        None,
        5_000_000,
        1_000_000,
        100_000,
    );

    let mut seeded = 0;
    for tracker in trackers.iter() {
        if let Some(verdict) = tracker.verdict {
            seeded += 1;
            let idx = formula_index(&tracker.id);
            assert!(
                idx < ground_truth.len(),
                "{context}: {}: formula index {idx} out of bounds (ground truth has {} entries)",
                tracker.id,
                ground_truth.len(),
            );

            // Soundness check 1: verdict matches ground truth.
            assert_eq!(
                verdict, ground_truth[idx],
                "{context}: {} heuristic verdict {verdict} does not match \
                 ground truth {}",
                tracker.id, ground_truth[idx],
            );

            // Soundness check 2: witness-only invariant.
            // EF can only produce true (witness found).
            // AG can only produce false (counterexample found).
            match tracker.quantifier {
                PathQuantifier::EF => assert!(
                    verdict,
                    "{context}: {} EF tracker produced false verdict — \
                     heuristic search is witness-only and must never produce EF=false",
                    tracker.id,
                ),
                PathQuantifier::AG => assert!(
                    !verdict,
                    "{context}: {} AG tracker produced true verdict — \
                     heuristic search is witness-only and must never produce AG=true",
                    tracker.id,
                ),
            }
        }
    }

    eprintln!(
        "{context}: heuristic search seeded {seeded}/{} verdicts, all match ground truth",
        trackers.len()
    );
}

#[test]
fn test_heuristic_soundness_angiogenesis_reachability_cardinality() {
    const MODEL: &str = "Angiogenesis-PT-01";
    if !has_mcc_benchmark(MODEL) {
        eprintln!("SKIP: {MODEL} benchmark not downloaded");
        return;
    }

    let net = crate::parser::parse_pnml_dir(&mcc_model_dir(MODEL)).expect("PNML should parse");
    let mut trackers = build_trackers_from_properties(&net, MODEL, "ReachabilityCardinality");
    let ground_truth = load_ground_truth("reachability-cardinality-2024.csv", MODEL);

    assert_eq!(
        trackers.len(),
        ground_truth.len(),
        "tracker/ground-truth arity mismatch"
    );
    verify_heuristic_soundness(&net, &mut trackers, &ground_truth, "ReachCard");
}

#[test]
fn test_heuristic_soundness_angiogenesis_reachability_fireability() {
    const MODEL: &str = "Angiogenesis-PT-01";
    if !has_mcc_benchmark(MODEL) {
        eprintln!("SKIP: {MODEL} benchmark not downloaded");
        return;
    }

    let net = crate::parser::parse_pnml_dir(&mcc_model_dir(MODEL)).expect("PNML should parse");
    let mut trackers = build_trackers_from_properties(&net, MODEL, "ReachabilityFireability");
    let ground_truth = load_ground_truth("reachability-fireability-2024.csv", MODEL);

    assert_eq!(
        trackers.len(),
        ground_truth.len(),
        "tracker/ground-truth arity mismatch"
    );
    verify_heuristic_soundness(&net, &mut trackers, &ground_truth, "ReachFire");
}

#[test]
fn test_heuristic_soundness_airplaneld_reachability_cardinality() {
    const MODEL: &str = "AirplaneLD-PT-0010";
    if !has_mcc_benchmark(MODEL) {
        eprintln!("SKIP: {MODEL} benchmark not downloaded");
        return;
    }

    let net = crate::parser::parse_pnml_dir(&mcc_model_dir(MODEL)).expect("PNML should parse");
    let mut trackers = build_trackers_from_properties(&net, MODEL, "ReachabilityCardinality");
    let ground_truth = load_ground_truth("reachability-cardinality-2024.csv", MODEL);

    assert_eq!(
        trackers.len(),
        ground_truth.len(),
        "tracker/ground-truth arity mismatch"
    );
    verify_heuristic_soundness(&net, &mut trackers, &ground_truth, "AirplaneLD-ReachCard");
}

#[test]
fn test_heuristic_empty_net() {
    let net = PetriNet {
        name: None,
        places: vec![],
        transitions: vec![],
        initial_marking: vec![],
    };
    let pred = ResolvedPredicate::True;
    let mut trackers = vec![ef_tracker("prop_empty", pred)];
    let targets = validation_targets_from_trackers(&trackers);
    let validation = WitnessValidationContext::new(&net, &targets);

    // Should handle gracefully (0 places → early return).
    run_heuristic_seeding_params(&net, &mut trackers, &validation, None, 100, 100, 100);

    // Empty net has 0 places, so the heuristic exits early without
    // updating the tracker verdict.  Verify it stays unresolved (None).
    assert_eq!(
        trackers[0].verdict, None,
        "EF(TRUE) on empty net with 0 places should leave verdict unresolved (early return)"
    );
}

#[test]
fn test_trivial_weights_skip_search() {
    // AG property with trivial weights — heuristic search should skip.
    let net = PetriNet {
        name: Some("skip".to_string()),
        places: vec![place("p0")],
        transitions: vec![transition("t0", vec![arc(0, 1)], vec![arc(0, 1)])],
        initial_marking: vec![1],
    };
    // AG(true) — no counterexample possible, trivial weights.
    let pred = ResolvedPredicate::True;
    let mut trackers = vec![ag_tracker("prop_trivial", pred)];
    let targets = validation_targets_from_trackers(&trackers);
    let validation = WitnessValidationContext::new(&net, &targets);

    run_heuristic_seeding_params(&net, &mut trackers, &validation, None, 100, 100, 100);

    // AG(true) has no counterexample, so verdict remains None (trivial weights skip).
    assert_eq!(trackers[0].verdict, None);
}

#[test]
fn test_queue_truncation_keeps_lowest_scores() {
    let queue: BinaryHeap<Reverse<ScoredNode>> = [4, 1, 3, 2]
        .into_iter()
        .map(|score| {
            Reverse(ScoredNode {
                score,
                marking: vec![],
                trace: None,
            })
        })
        .collect();

    let keep = 2;
    let sorted = queue.into_sorted_vec();
    let truncated: BinaryHeap<Reverse<ScoredNode>> = sorted.into_iter().rev().take(keep).collect();

    let mut kept_scores: Vec<u64> = truncated
        .into_vec()
        .into_iter()
        .map(|entry| entry.0.score)
        .collect();
    kept_scores.sort_unstable();

    assert_eq!(
        kept_scores,
        vec![1, 2],
        "queue truncation must keep the best-scoring frontier entries"
    );
}

#[test]
fn test_queue_truncation_releases_discarded_trace_chains() {
    let root = Rc::new(TraceNode {
        parent: None,
        via: crate::petri_net::TransitionIdx(0),
    });
    let queue: BinaryHeap<Reverse<ScoredNode>> = [4, 1, 3, 2]
        .into_iter()
        .map(|score| {
            Reverse(ScoredNode {
                score,
                marking: vec![],
                trace: Some(Rc::new(TraceNode {
                    parent: Some(Rc::clone(&root)),
                    via: crate::petri_net::TransitionIdx(score as u32),
                })),
            })
        })
        .collect();

    assert_eq!(
        Rc::strong_count(&root),
        5,
        "all frontier entries should retain the shared trace root before truncation"
    );

    let keep = 2;
    let sorted = queue.into_sorted_vec();
    let truncated: BinaryHeap<Reverse<ScoredNode>> = sorted.into_iter().rev().take(keep).collect();

    assert_eq!(
        Rc::strong_count(&root),
        3,
        "discarded frontier entries should release their trace chains after truncation"
    );

    drop(truncated);
    assert_eq!(
        Rc::strong_count(&root),
        1,
        "dropping the frontier should release the remaining shared trace chains"
    );
}
