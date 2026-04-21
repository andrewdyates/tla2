// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for LP rounding bug (#1501).
//!
//! The LP state equation solver (minilp) returns floating-point optimal values.
//! For integer-weighted Petri nets, the true optimum is integer-valued, but
//! floating-point error can push it slightly below (e.g., 0.999999 instead of
//! 1.0). Using `floor()` truncated this to 0, producing unsound LP bounds
//! that overrode correct P-invariant bounds. Fix: use `ceil()`.

use std::path::PathBuf;

use crate::invariant::compute_p_invariants;
use crate::lp_state_equation::lp_upper_bound;
use crate::model::PropertyAliases;
use crate::parser::parse_pnml_dir;
use crate::property_xml::{parse_properties, Formula};
use crate::resolved_predicate::resolve_place_bound;

fn mcc_input_dir(model: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/mcc/2024/INPUTS")
        .join(model)
}

fn has_benchmark(model: &str) -> bool {
    mcc_input_dir(model).join("model.pnml").exists()
}

/// LP bound for NQueens-PT-30 P_7_21 must be >= P-invariant bound (1).
///
/// Before the fix, LP returned Some(0) due to floor() truncation of ~0.999.
/// P-invariants correctly computed bound=1 (4 covering invariants).
/// The LP overrode the P-invariant via `effective_bound = min(structural, lp)`,
/// causing the property to resolve as 0 instead of 1.
#[test]
fn test_nqueens_lp_bound_not_truncated() {
    if !has_benchmark("NQueens-PT-30") {
        eprintln!("SKIP: NQueens-PT-30 benchmark not available");
        return;
    }

    let dir = mcc_input_dir("NQueens-PT-30");
    let net = parse_pnml_dir(&dir).expect("failed to parse PNML");
    let properties =
        parse_properties(&dir, "UpperBounds").expect("failed to parse UpperBounds properties");

    let prop = &properties[0];
    assert_eq!(prop.id, "NQueens-PT-30-UpperBounds-00");

    let aliases = PropertyAliases::identity(&net);
    let place_indices = resolve_place_bound(
        match &prop.formula {
            Formula::PlaceBound(names) => names,
            _ => panic!("expected PlaceBound"),
        },
        &aliases,
    );

    // P-invariant bound
    let invariants = compute_p_invariants(&net);
    let structural =
        crate::invariant::structural_set_bound(&invariants, &[place_indices[0].0 as usize]);
    assert_eq!(structural, Some(1), "P-invariant should give bound 1");

    // LP bound must be >= P-invariant bound (LP relaxation is at least as tight)
    let lp = lp_upper_bound(&net, &place_indices);
    assert!(
        lp.map_or(true, |b| b >= 1),
        "LP bound {lp:?} is less than P-invariant bound 1 — rounding bug"
    );
}

/// LP helper for IBM5964-PT-none UpperBounds-14 must return the exact LP cap.
///
/// The full pipeline now returns the correct value (3) via LP-gap fallback.
/// This test pins the LP helper's isolated result to confirm it returns
/// the exact MCC ground truth, independent of reduction/BFS.
#[test]
fn test_ibm5964_lp_bound_consistency() {
    if !has_benchmark("IBM5964-PT-none") {
        eprintln!("SKIP: IBM5964-PT-none benchmark not available");
        return;
    }

    let dir = mcc_input_dir("IBM5964-PT-none");
    let net = parse_pnml_dir(&dir).expect("failed to parse PNML");
    let properties =
        parse_properties(&dir, "UpperBounds").expect("failed to parse UpperBounds properties");

    // Find property 14
    let prop = properties
        .iter()
        .find(|p| p.id == "IBM5964-PT-none-UpperBounds-14")
        .expect("property 14 not found");

    let aliases = PropertyAliases::identity(&net);
    let place_indices = resolve_place_bound(
        match &prop.formula {
            Formula::PlaceBound(names) => names,
            _ => panic!("expected PlaceBound"),
        },
        &aliases,
    );

    let invariants = compute_p_invariants(&net);
    let structural: Vec<Option<u64>> = place_indices
        .iter()
        .map(|p| crate::invariant::structural_set_bound(&invariants, &[p.0 as usize]))
        .collect();

    let lp = lp_upper_bound(&net, &place_indices);

    eprintln!(
        "IBM5964-PT-none-UpperBounds-14: places={:?}, structural={:?}, lp={:?}",
        place_indices.iter().map(|p| p.0).collect::<Vec<_>>(),
        structural,
        lp
    );

    assert!(
        structural.iter().all(Option::is_none),
        "IBM5964 helper test expects no structural cap, got {structural:?}"
    );
    assert_eq!(
        lp,
        Some(3),
        "IBM5964 LP helper should return the exact MCC bound in isolation"
    );
}

/// End-to-end regression: SwimmingPool-PT-01 all 16 UpperBounds formulas.
///
/// Ground truth from `registry/mcc-labels/upper-bounds-2024.csv`:
/// `20 10 10 10 10 10 10 20 10 15 10 10 10 10 15 15`
///
/// SwimmingPool-PT-01 is the smallest variant (same topology as PT-07).
/// Before the fix (#1501), the pipeline returned 0 for many formulas because
/// structural reduction removed query-target places, and LP rounding truncated
/// bounds below their true value.
#[test]
fn test_swimming_pool_upper_bounds_end_to_end() {
    if !has_benchmark("SwimmingPool-PT-01") {
        eprintln!("SKIP: SwimmingPool-PT-01 benchmark not available");
        return;
    }

    let dir = mcc_input_dir("SwimmingPool-PT-01");
    let net = parse_pnml_dir(&dir).expect("failed to parse PNML");
    let properties =
        parse_properties(&dir, "UpperBounds").expect("failed to parse UpperBounds properties");

    let config = crate::explorer::ExplorationConfig::new(10_000_000);
    let results = crate::examinations::upper_bounds::check_upper_bounds_properties(
        &net,
        &properties,
        &config,
    );

    let expected: [u64; 16] = [
        20, 10, 10, 10, 10, 10, 10, 20, 10, 15, 10, 10, 10, 10, 15, 15,
    ];

    let mut wrong = 0usize;
    for (i, (id, value)) in results.iter().enumerate() {
        let exp = expected[i];
        match value {
            Some(v) if *v == exp => {}
            Some(v) => {
                eprintln!("WRONG: {id}: got {v}, expected {exp}");
                wrong += 1;
            }
            None => {
                eprintln!("CANNOT_COMPUTE: {id} (expected {exp})");
                wrong += 1;
            }
        }
    }

    assert_eq!(
        wrong, 0,
        "SwimmingPool-PT-01 UpperBounds: {wrong}/16 wrong answers — #1501 regression"
    );
}

/// End-to-end regression: NQueens-PT-05 all 16 UpperBounds formulas.
///
/// Ground truth: all 1. Before LP rounding fix, floor(0.999) = 0 caused
/// LP to override correct P-invariant bound of 1, producing wrong 0s.
/// Uses PT-05 (smallest available variant) instead of PT-30 which times out.
#[test]
fn test_nqueens_upper_bounds_end_to_end() {
    if !has_benchmark("NQueens-PT-05") {
        eprintln!("SKIP: NQueens-PT-05 benchmark not available");
        return;
    }

    let dir = mcc_input_dir("NQueens-PT-05");
    let net = parse_pnml_dir(&dir).expect("failed to parse PNML");
    let properties =
        parse_properties(&dir, "UpperBounds").expect("failed to parse UpperBounds properties");

    let config = crate::explorer::ExplorationConfig::new(10_000_000);
    let results = crate::examinations::upper_bounds::check_upper_bounds_properties(
        &net,
        &properties,
        &config,
    );

    let mut wrong = 0usize;
    for (id, value) in &results {
        match value {
            Some(1) => {}
            Some(v) => {
                eprintln!("WRONG: {id}: got {v}, expected 1");
                wrong += 1;
            }
            None => {
                eprintln!("CANNOT_COMPUTE: {id} (expected 1)");
                wrong += 1;
            }
        }
    }

    assert_eq!(
        wrong, 0,
        "NQueens-PT-05 UpperBounds: {wrong}/16 wrong answers — #1501 LP rounding regression"
    );
}

/// End-to-end regression: IBM5964-PT-none all 16 UpperBounds formulas.
///
/// Formula 14 (expected=3) previously returned 2 due to unsound reduction.
/// Fixed by LP-gap fallback (1f25b46). All other formulas expected 0.
/// Ground truth from `registry/mcc-labels/upper-bounds-2024.csv`.
///
/// Design: `designs/2026-03-22-upperbounds-ibm5964-reduction-unsoundness.md`.
#[test]
fn test_ibm5964_upper_bounds_end_to_end() {
    if !has_benchmark("IBM5964-PT-none") {
        eprintln!("SKIP: IBM5964-PT-none benchmark not available");
        return;
    }

    let dir = mcc_input_dir("IBM5964-PT-none");
    let net = parse_pnml_dir(&dir).expect("failed to parse PNML");
    let properties =
        parse_properties(&dir, "UpperBounds").expect("failed to parse UpperBounds properties");

    let config = crate::explorer::ExplorationConfig::new(10_000_000);
    let results = crate::examinations::upper_bounds::check_upper_bounds_properties(
        &net,
        &properties,
        &config,
    );

    // Ground truth: 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3 0
    let expected: [u64; 16] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0];

    let mut wrong = 0usize;
    for (i, (id, value)) in results.iter().enumerate() {
        let exp = expected[i];
        match value {
            Some(v) if *v == exp => {}
            Some(v) => {
                eprintln!("WRONG: {id}: got {v}, expected {exp}");
                wrong += 1;
            }
            None => {
                eprintln!("CANNOT_COMPUTE: {id} (expected {exp})");
                wrong += 1;
            }
        }
    }

    assert_eq!(
        wrong, 0,
        "IBM5964-PT-none UpperBounds: {wrong}/16 wrong answers — #1501 regression"
    );
}
