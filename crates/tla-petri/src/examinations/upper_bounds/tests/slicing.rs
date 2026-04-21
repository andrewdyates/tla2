// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Query-slice-specific UpperBounds tests.

use crate::examinations::query_support::{closure_on_reduced_net, upper_bounds_support};
use crate::property_xml::{Formula, Property};
use crate::query_slice::build_query_slice;
use crate::reduction::ReducedNet;

use super::super::model::prepare_upper_bounds_properties;
use super::super::pipeline::{build_upper_bounds_slice, check_upper_bounds_properties};
use super::fixtures::*;

/// Helper: run the production-matching protected reduction pipeline for a
/// given net + trackers, returning the reduced net. Mirrors the production
/// pipeline's reduction steps (protected structural + query-guarded + GCD)
/// without the slicing step.
fn reduce_for_upper_bounds(
    net: &crate::petri_net::PetriNet,
    trackers: &[super::super::model::BoundTracker],
) -> crate::reduction::ReducedNet {
    use crate::reduction::{
        apply_final_place_gcd_scaling, reduce_iterative_structural_with_protected,
        reduce_query_guarded,
    };
    let unresolved_place_sets: Vec<Vec<_>> = trackers
        .iter()
        .map(|tracker| tracker.place_indices.clone())
        .collect();
    let initial_protected =
        upper_bounds_support(&ReducedNet::identity(net), &unresolved_place_sets)
            .map(|s| s.places)
            .unwrap_or_else(|| vec![true; net.num_places()]);
    let reduced = reduce_iterative_structural_with_protected(net, &initial_protected)
        .expect("protected reduction should succeed");
    let mut reduced = reduce_query_guarded(reduced, |r| {
        let support = upper_bounds_support(r, &unresolved_place_sets)?;
        Some(support.places)
    })
    .expect("query-guarded reduction should succeed");
    apply_final_place_gcd_scaling(&mut reduced).expect("GCD scaling should succeed");
    reduced
}

#[test]
fn test_query_slice_shrinks_upper_bounds_budget_net() {
    let net = query_slice_budget_net();
    let props = vec![Property {
        id: "budget-UpperBounds-00".to_string(),
        formula: Formula::PlaceBound(vec!["r1".to_string()]),
    }];

    let (_prepared, trackers) = prepare_upper_bounds_properties(&net, &props);
    let reduced = reduce_for_upper_bounds(&net, &trackers);
    let (slice, _slots, _trackers) = build_upper_bounds_slice(&reduced, &trackers)
        .expect("slice should shrink disconnected components");

    assert!(slice.net.num_places() < reduced.net.num_places());
    assert!(slice.net.num_transitions() < reduced.net.num_transitions());
}

#[test]
fn test_query_slice_matches_unsliced_upper_bounds_results() {
    let net = query_slice_budget_net();
    let props = vec![Property {
        id: "budget-UpperBounds-00".to_string(),
        formula: Formula::PlaceBound(vec!["r1".to_string()]),
    }];

    let sliced = check_upper_bounds_properties(&net, &props, &default_config());
    let unsliced = check_upper_bounds_properties_unsliced(&net, &props, &default_config());

    assert_eq!(sliced, unsliced);
}

#[test]
fn test_query_slice_shrinks_connected_component_sink_tail() {
    let net = connected_sink_tail_net();
    let props = vec![Property {
        id: "sink-tail-UpperBounds-00".to_string(),
        formula: Formula::PlaceBound(vec!["p1".to_string()]),
    }];

    let (_prepared, trackers) = prepare_upper_bounds_properties(&net, &props);
    let reduced = ReducedNet::identity(&net);
    let unresolved_place_sets: Vec<Vec<_>> = trackers
        .iter()
        .map(|tracker| tracker.place_indices.clone())
        .collect();
    let support = upper_bounds_support(&reduced, &unresolved_place_sets)
        .expect("support should resolve on identity reduction");
    let closure = closure_on_reduced_net(&reduced.net, support);

    assert!(
        build_query_slice(&reduced.net, &closure).is_none(),
        "the old induced-subnet path keeps the full connected component",
    );

    let (slice, _slots, _trackers) = build_upper_bounds_slice(&reduced, &trackers)
        .expect("query-local slice should shrink the connected sink tail");

    assert_eq!(slice.net.num_places(), 2);
    assert_eq!(slice.net.num_transitions(), 1);
    assert_eq!(slice.net.transitions[0].outputs.len(), 1);
}

#[test]
fn test_query_slice_matches_unsliced_upper_bounds_results_on_connected_sink_tail() {
    let net = connected_sink_tail_net();
    let props = vec![Property {
        id: "sink-tail-UpperBounds-00".to_string(),
        formula: Formula::PlaceBound(vec!["p1".to_string()]),
    }];

    let sliced = check_upper_bounds_properties(&net, &props, &default_config());
    let unsliced = check_upper_bounds_properties_unsliced(&net, &props, &default_config());

    assert_eq!(sliced, unsliced);
    assert_eq!(
        sliced,
        vec![(String::from("sink-tail-UpperBounds-00"), Some(1))]
    );
}

#[test]
fn test_query_slice_upper_bounds_avoids_cannot_compute_under_budget() {
    let net = query_slice_budget_net();
    let props = vec![Property {
        id: "budget-UpperBounds-00".to_string(),
        formula: Formula::PlaceBound(vec!["r1".to_string()]),
    }];
    let config = parallel_budget_config(4);

    let sliced = check_upper_bounds_properties(&net, &props, &config);
    let unsliced = check_upper_bounds_properties_unsliced(&net, &props, &config);

    // Structural reductions now prune the irrelevant i-components
    // from the budget net, so both paths solve within the budget.
    assert_eq!(
        sliced,
        vec![(String::from("budget-UpperBounds-00"), Some(2))]
    );
    assert_eq!(
        unsliced,
        vec![(String::from("budget-UpperBounds-00"), Some(2))]
    );
}
