// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::time::{Duration, Instant};

use super::fixtures::*;
use super::*;

#[test]
fn test_ef_cardinality_found() {
    // EF(tokens(p1) >= 2)  i.e. EF(2 <= tokens(p1))
    let net = simple_net();
    let props = vec![make_ef_prop(
        "test-00",
        StatePredicate::IntLe(
            IntExpr::Constant(2),
            IntExpr::TokensCount(vec!["p1".to_string()]),
        ),
    )];
    let mut obs = ReachabilityObserver::new(&net, &props);

    // marking [3, 0]: 0 >= 2? no
    assert!(obs.on_new_state(&[3, 0]));
    // marking [2, 1]: 1 >= 2? no
    assert!(obs.on_new_state(&[2, 1]));
    // marking [1, 2]: 2 >= 2? yes — EF satisfied
    assert!(!obs.on_new_state(&[1, 2]));

    let results = obs.results();
    assert_eq!(results[0].1, Some(true));
}

#[test]
fn test_ef_cardinality_not_found() {
    // EF(tokens(p1) >= 10)
    let net = simple_net();
    let props = vec![make_ef_prop(
        "test-00",
        StatePredicate::IntLe(
            IntExpr::Constant(10),
            IntExpr::TokensCount(vec!["p1".to_string()]),
        ),
    )];
    let mut obs = ReachabilityObserver::new(&net, &props);

    obs.on_new_state(&[3, 0]);
    obs.on_new_state(&[2, 1]);
    obs.on_new_state(&[1, 2]);
    obs.on_new_state(&[0, 3]);

    // Never satisfied — results_completed gives FALSE
    assert_eq!(obs.results()[0].1, None);
    assert!(!obs.results_completed()[0].1);
}

#[test]
fn test_ag_cardinality_holds() {
    // AG(tokens(p0) + tokens(p1) <= 3)  i.e. AG(tokens(p0,p1) <= 3)
    let net = simple_net();
    let props = vec![make_ag_prop(
        "test-00",
        StatePredicate::IntLe(
            IntExpr::TokensCount(vec!["p0".to_string(), "p1".to_string()]),
            IntExpr::Constant(3),
        ),
    )];
    let mut obs = ReachabilityObserver::new(&net, &props);

    // All markings sum to 3 in this conserving net
    assert!(obs.on_new_state(&[3, 0]));
    assert!(obs.on_new_state(&[2, 1]));
    assert!(obs.on_new_state(&[1, 2]));
    assert!(obs.on_new_state(&[0, 3]));

    // Never violated — results_completed gives TRUE
    assert!(obs.results_completed()[0].1);
}

#[test]
fn test_ag_cardinality_violated() {
    // AG(tokens(p0) <= 2) — violated by initial marking [3, 0]
    let net = simple_net();
    let props = vec![make_ag_prop(
        "test-00",
        StatePredicate::IntLe(
            IntExpr::TokensCount(vec!["p0".to_string()]),
            IntExpr::Constant(2),
        ),
    )];
    let mut obs = ReachabilityObserver::new(&net, &props);

    // marking [3, 0]: 3 <= 2? no — AG violated
    assert!(!obs.on_new_state(&[3, 0]));

    assert_eq!(obs.results()[0].1, Some(false));
}

#[test]
fn test_fireability_ef() {
    // EF(is-fireable(t0)) — t0 needs p0 >= 1, true at initial
    let net = simple_net();
    let props = vec![make_ef_prop(
        "test-00",
        StatePredicate::IsFireable(vec!["t0".to_string()]),
    )];
    let mut obs = ReachabilityObserver::new(&net, &props);

    // marking [3, 0]: t0 is enabled (p0=3 >= 1)
    assert!(!obs.on_new_state(&[3, 0]));

    assert_eq!(obs.results()[0].1, Some(true));
}

#[test]
fn test_fireability_ag_negated() {
    // AG(NOT is-fireable(t0)) — false since t0 is fireable at [3,0]
    let net = simple_net();
    let props = vec![make_ag_prop(
        "test-00",
        StatePredicate::Not(Box::new(StatePredicate::IsFireable(vec!["t0".to_string()]))),
    )];
    let mut obs = ReachabilityObserver::new(&net, &props);

    // marking [3, 0]: NOT fireable(t0) = false → AG violated
    assert!(!obs.on_new_state(&[3, 0]));

    assert_eq!(obs.results()[0].1, Some(false));
}

#[test]
fn test_reachability_prefire_guard_preserves_initial_fireability_query() {
    let props = vec![make_ef_prop(
        "prefire-fireability",
        StatePredicate::IsFireable(vec!["t0".to_string()]),
    )];

    let results = check_reachability_properties(&prefire_guard_net(), &props, &default_config());
    assert_eq!(
        results,
        vec![("prefire-fireability".to_string(), Verdict::True)]
    );
}

#[test]
fn test_unsliced_helper_matches_prefire_guarded_production_path() {
    let net = prefire_guard_net();
    let props = vec![make_ef_prop(
        "prefire-fireability",
        StatePredicate::IsFireable(vec!["t0".to_string()]),
    )];
    let config = default_config();

    let production = check_reachability_properties(&net, &props, &config);
    let unsliced = check_reachability_properties_unsliced(&net, &props, &config);

    assert_eq!(unsliced, production);
    assert_eq!(
        unsliced,
        vec![("prefire-fireability".to_string(), Verdict::True)]
    );
}

#[test]
fn test_reachability_prefire_overflow_returns_cannot_compute() {
    let props = vec![make_ef_prop(
        "prefire-overflow",
        StatePredicate::IsFireable(vec!["q_goal".to_string()]),
    )];
    let config = default_config().with_deadline(Some(Instant::now() - Duration::from_secs(1)));

    let results = check_reachability_properties(&prefire_overflow_net(), &props, &config);

    assert_eq!(
        results,
        vec![("prefire-overflow".to_string(), Verdict::CannotCompute)]
    );
}

#[test]
fn test_multiple_properties_mixed() {
    let net = simple_net();
    let props = vec![
        // EF(tokens(p1) >= 3) — satisfied at [0, 3]
        make_ef_prop(
            "ef-00",
            StatePredicate::IntLe(
                IntExpr::Constant(3),
                IntExpr::TokensCount(vec!["p1".to_string()]),
            ),
        ),
        // AG(tokens(p0) <= 5) — always true (max is 3)
        make_ag_prop(
            "ag-00",
            StatePredicate::IntLe(
                IntExpr::TokensCount(vec!["p0".to_string()]),
                IntExpr::Constant(5),
            ),
        ),
    ];
    let mut obs = ReachabilityObserver::new(&net, &props);

    obs.on_new_state(&[3, 0]);
    obs.on_new_state(&[2, 1]);
    obs.on_new_state(&[1, 2]);
    obs.on_new_state(&[0, 3]);

    let results = obs.results_completed();
    assert!(results[0].1); // EF found witness at [0,3]
    assert!(results[1].1); // AG never violated
}

// --- Provenance attribution tests ---

use crate::examinations::reachability::types::{
    finalize_exhaustive_completion, resolve_tracker, ReachabilityResolution,
    ReachabilityResolutionSource,
};

fn make_tracker(id: &str, quantifier: PathQuantifier, net: &PetriNet) -> PropertyTracker {
    let aliases = crate::model::PropertyAliases::identity(net);
    let predicate = crate::resolved_predicate::resolve_predicate_with_aliases(
        &StatePredicate::IntLe(
            IntExpr::Constant(1),
            IntExpr::TokensCount(vec!["p0".to_string()]),
        ),
        &aliases,
    );
    PropertyTracker {
        id: id.to_string(),
        quantifier,
        predicate,
        verdict: None,
        resolved_by: None,
        flushed: false,
    }
}

#[test]
fn test_resolve_tracker_first_writer_wins() {
    let net = simple_net();
    let mut tracker = make_tracker("fw-test", PathQuantifier::EF, &net);

    resolve_tracker(
        &mut tracker,
        true,
        ReachabilityResolutionSource::Bmc,
        Some(2),
    );
    assert_eq!(tracker.verdict, Some(true));
    assert_eq!(
        tracker.resolved_by,
        Some(ReachabilityResolution {
            source: ReachabilityResolutionSource::Bmc,
            depth: Some(2),
        })
    );

    // Second write should be ignored (first-writer-wins).
    resolve_tracker(&mut tracker, false, ReachabilityResolutionSource::Lp, None);
    assert_eq!(tracker.verdict, Some(true));
    assert_eq!(
        tracker.resolved_by.unwrap().source,
        ReachabilityResolutionSource::Bmc,
    );
}

#[test]
fn test_bfs_witness_stamps_provenance() {
    let net = simple_net();
    let props = vec![make_ef_prop(
        "prov-ef",
        StatePredicate::IntLe(
            IntExpr::Constant(3),
            IntExpr::TokensCount(vec!["p1".to_string()]),
        ),
    )];
    let mut obs = ReachabilityObserver::new(&net, &props);

    obs.on_new_state(&[3, 0]);
    obs.on_new_state(&[0, 3]); // witness found

    let trackers = obs.into_trackers();
    assert_eq!(trackers[0].verdict, Some(true));
    assert_eq!(
        trackers[0].resolved_by.unwrap().source,
        ReachabilityResolutionSource::BfsWitness,
    );
}

#[test]
fn test_bfs_counterexample_stamps_provenance() {
    let net = simple_net();
    let props = vec![make_ag_prop(
        "prov-ag",
        StatePredicate::IntLe(
            IntExpr::TokensCount(vec!["p0".to_string()]),
            IntExpr::Constant(2),
        ),
    )];
    let mut obs = ReachabilityObserver::new(&net, &props);

    obs.on_new_state(&[3, 0]); // 3 > 2, counterexample found

    let trackers = obs.into_trackers();
    assert_eq!(trackers[0].verdict, Some(false));
    assert_eq!(
        trackers[0].resolved_by.unwrap().source,
        ReachabilityResolutionSource::BfsCounterexample,
    );
}

#[test]
fn test_finalize_exhaustive_completion_stamps_unresolved() {
    let net = simple_net();
    let ef = make_tracker("exhaust-ef", PathQuantifier::EF, &net);
    let mut ag = make_tracker("exhaust-ag", PathQuantifier::AG, &net);

    // Pre-resolve ag with a different source to test first-writer-wins.
    resolve_tracker(&mut ag, true, ReachabilityResolutionSource::Lp, None);

    let mut trackers = vec![ef, ag];
    finalize_exhaustive_completion(&mut trackers);

    // EF was unresolved → stamped ExhaustiveCompletion with FALSE.
    assert_eq!(trackers[0].verdict, Some(false));
    assert_eq!(
        trackers[0].resolved_by.unwrap().source,
        ReachabilityResolutionSource::ExhaustiveCompletion,
    );

    // AG was already resolved by LP → first-writer-wins preserved.
    assert_eq!(trackers[1].verdict, Some(true));
    assert_eq!(
        trackers[1].resolved_by.unwrap().source,
        ReachabilityResolutionSource::Lp,
    );
}

#[test]
fn test_parallel_summary_preserves_provenance() {
    use crate::explorer::{ParallelExplorationObserver, ParallelExplorationSummary};

    let net = simple_net();
    let props = vec![make_ef_prop(
        "par-ef",
        StatePredicate::IntLe(
            IntExpr::Constant(3),
            IntExpr::TokensCount(vec!["p1".to_string()]),
        ),
    )];
    let mut obs = ReachabilityObserver::new(&net, &props);
    let mut summary = obs.new_summary();

    // Summary discovers the witness via on_new_state.
    summary.on_new_state(&[0, 3]);

    // Merge into observer — provenance must survive the merge.
    obs.merge_summary(summary);
    let trackers = obs.into_trackers();
    assert_eq!(trackers[0].verdict, Some(true));
    assert_eq!(
        trackers[0].resolved_by.unwrap().source,
        ReachabilityResolutionSource::BfsWitness,
    );
}
