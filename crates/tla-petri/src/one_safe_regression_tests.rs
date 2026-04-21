// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for OneSafe false-FALSE bug (#1504).
//!
//! ASLink-PT-01a, ASLink-PT-02a, and Railroad-PT-050 are ground-truth 1-safe
//! but the Petri-net checker reported FALSE due to parallel place merging creating
//! spurious >1 token markings in the reduced net.
//!
//! Root cause: `find_parallel_places` merging combined arc weights via
//! `remap_and_combine_arcs`. If places A and B are parallel with weight-w
//! arcs, merging doubles every arc to 2w on the canonical. A transition
//! producing w tokens now produces 2w, pushing the canonical above 1 even
//! when the original net is 1-safe. Fix: skip parallel place merging in
//! OneSafe semantics.

use std::path::PathBuf;
use std::time::{Duration, Instant};

use crate::examination::one_safe_verdict;
use crate::examinations::one_safe::OneSafeObserver;
use crate::explorer::{explore_observer, ExplorationConfig};
use crate::output::Verdict;
use crate::parser::parse_pnml_dir;
use crate::reduction::reduce_iterative_structural_one_safe;

fn mcc_input_dir(model: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/mcc/2024/INPUTS")
        .join(model)
}

fn has_benchmark(model: &str) -> bool {
    mcc_input_dir(model).join("model.pnml").exists()
}

/// Verify that OneSafe reduction does NOT produce false >1 markings.
///
/// After the fix, parallel places are not merged in OneSafe mode,
/// so the reduced net preserves 1-safety of the original.
fn verify_reduced_net_one_safe(model: &str) -> bool {
    let dir = mcc_input_dir(model);
    let net = parse_pnml_dir(&dir).expect("failed to parse PNML");

    let reduced = reduce_iterative_structural_one_safe(&net).expect("reduction should succeed");

    eprintln!(
        "{}: places {} -> {}, transitions {} -> {}, parallel={}, redundant={}",
        model,
        net.num_places(),
        reduced.net.num_places(),
        net.num_transitions(),
        reduced.net.num_transitions(),
        reduced.report.parallel_places.len(),
        reduced.report.redundant_places.len(),
    );

    // Run BFS with a deadline to avoid timeout. We only need to confirm
    // no >1 marking is found within the explored states.
    let deadline = Instant::now() + Duration::from_secs(30);
    let config = ExplorationConfig::new(10_000_000)
        .refitted_for_net(&reduced.net)
        .with_deadline(Some(deadline));
    let mut observer = OneSafeObserver::new();
    let result = explore_observer(&reduced.net, &config, &mut observer);

    eprintln!(
        "{}: reduced BFS safe={}, completed={}",
        model,
        observer.is_safe(),
        result.completed
    );

    // The reduced net must NOT report a counterexample.
    // (It might not complete, but it must not find >1.)
    observer.is_safe()
}

/// Verify the full verdict is not FALSE for a ground-truth 1-safe model.
fn verify_verdict_not_false(model: &str) {
    let dir = mcc_input_dir(model);
    let net = parse_pnml_dir(&dir).expect("failed to parse PNML");

    let deadline = Instant::now() + Duration::from_secs(30);
    let config = ExplorationConfig::new(10_000_000).with_deadline(Some(deadline));
    let verdict = one_safe_verdict(&net, &config, &[]);
    eprintln!("{}: verdict = {:?}", model, verdict);

    assert!(
        !matches!(verdict, Verdict::False),
        "{model}: OneSafe should NOT be FALSE (ground truth is TRUE), got {verdict:?}"
    );
}

#[test]
fn test_aslink_pt_01a_no_false_one_safe() {
    if !has_benchmark("ASLink-PT-01a") {
        eprintln!("SKIP: ASLink-PT-01a benchmark not available");
        return;
    }

    // Verify reduced net doesn't produce spurious >1 markings
    assert!(
        verify_reduced_net_one_safe("ASLink-PT-01a"),
        "ASLink-PT-01a: reduced net should not report >1 token marking"
    );

    // Verify full verdict is not FALSE
    verify_verdict_not_false("ASLink-PT-01a");
}

#[test]
fn test_aslink_pt_02a_no_false_one_safe() {
    if !has_benchmark("ASLink-PT-02a") {
        eprintln!("SKIP: ASLink-PT-02a benchmark not available");
        return;
    }

    assert!(
        verify_reduced_net_one_safe("ASLink-PT-02a"),
        "ASLink-PT-02a: reduced net should not report >1 token marking"
    );

    verify_verdict_not_false("ASLink-PT-02a");
}

#[test]
fn test_railroad_pt_050_no_false_one_safe() {
    if !has_benchmark("Railroad-PT-050") {
        eprintln!("SKIP: Railroad-PT-050 benchmark not available");
        return;
    }

    assert!(
        verify_reduced_net_one_safe("Railroad-PT-050"),
        "Railroad-PT-050: reduced net should not report >1 token marking"
    );

    verify_verdict_not_false("Railroad-PT-050");
}
