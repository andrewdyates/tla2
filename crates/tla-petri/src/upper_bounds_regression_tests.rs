// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for UpperBounds wrong answers (#1501).
//!
//! Root cause: `reduce_with_protected` in structural.rs did not check the
//! `self_loop_protected` mask when removing constant places, isolated places,
//! and agglomerated places. After iterative reduction made query-target places
//! "constant" in the reduced topology, they were removed and reconstructed
//! with their initial value (often 0), causing wrong UpperBounds answers.
//!
//! Fix: added `if !self_loop_protected[p]` guards for constant, isolated,
//! pre-agglomeration, and post-agglomeration place removal.

use std::path::PathBuf;

use crate::model::PropertyAliases;
use crate::parser::parse_pnml_dir;
use crate::property_xml::{parse_properties, Formula};
use crate::reduction::reduce_iterative_structural_query_with_protected;
use crate::resolved_predicate::resolve_place_bound;

fn mcc_input_dir(model: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/mcc/2024/INPUTS")
        .join(model)
}

fn has_benchmark(model: &str) -> bool {
    mcc_input_dir(model).join("model.pnml").exists()
}

/// Build a protection mask from UpperBounds properties.
fn upper_bounds_protected_mask(
    net: &crate::petri_net::PetriNet,
    dir: &std::path::Path,
) -> Vec<bool> {
    let properties =
        parse_properties(dir, "UpperBounds").expect("failed to parse UpperBounds properties");
    let aliases = PropertyAliases::identity(net);
    let mut protected = vec![false; net.num_places()];
    for prop in &properties {
        if let Formula::PlaceBound(place_names) = &prop.formula {
            for place_idx in resolve_place_bound(place_names, &aliases) {
                protected[place_idx.0 as usize] = true;
            }
        }
    }
    protected
}

/// Verify that protected places survive iterative structural reduction.
///
/// Uses SwimmingPool-PT-01 (smallest variant, same topology as PT-07).
/// Before the fix, query-target places became "constant" after agglomeration
/// removed surrounding transitions, and were then removed with value 0.
///
/// After the fix, these places are preserved because `self_loop_protected`
/// prevents their removal even when detected as constant.
#[test]
fn test_swimming_pool_protected_places_survive_reduction() {
    if !has_benchmark("SwimmingPool-PT-01") {
        eprintln!("SKIP: SwimmingPool-PT-01 benchmark not available");
        return;
    }

    let dir = mcc_input_dir("SwimmingPool-PT-01");
    let net = parse_pnml_dir(&dir).expect("failed to parse PNML");
    let protected = upper_bounds_protected_mask(&net, &dir);

    let protected_count = protected.iter().filter(|&&p| p).count();
    assert!(
        protected_count > 0,
        "SwimmingPool-PT-01 should have at least one protected UpperBounds place"
    );

    let reduced = reduce_iterative_structural_query_with_protected(&net, &protected)
        .expect("reduction should succeed");

    for (orig_idx, &is_protected) in protected.iter().enumerate() {
        if !is_protected {
            continue;
        }
        let survived = reduced.place_map.get(orig_idx).copied().flatten().is_some();
        let name = net.places[orig_idx]
            .name
            .as_deref()
            .unwrap_or(&net.places[orig_idx].id);
        assert!(
            survived,
            "Protected place {} ({}) was removed by reduction — this is the #1501 bug",
            name, orig_idx
        );
    }
}

/// Verify NQueens-PT-30 protected places survive reduction.
#[test]
fn test_nqueens_protected_places_survive_reduction() {
    if !has_benchmark("NQueens-PT-30") {
        eprintln!("SKIP: NQueens-PT-30 benchmark not available");
        return;
    }

    let dir = mcc_input_dir("NQueens-PT-30");
    let net = parse_pnml_dir(&dir).expect("failed to parse PNML");
    let protected = upper_bounds_protected_mask(&net, &dir);

    let reduced = reduce_iterative_structural_query_with_protected(&net, &protected)
        .expect("reduction should succeed");

    for (orig_idx, &is_protected) in protected.iter().enumerate() {
        if !is_protected {
            continue;
        }
        let survived = reduced.place_map.get(orig_idx).copied().flatten().is_some();
        let name = net.places[orig_idx]
            .name
            .as_deref()
            .unwrap_or(&net.places[orig_idx].id);
        assert!(
            survived,
            "Protected place {} ({}) was removed by reduction — this is the #1501 bug",
            name, orig_idx
        );
    }
}
