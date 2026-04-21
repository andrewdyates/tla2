// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Query-guarded prefire tests for UpperBounds.

use crate::examinations::query_support::upper_bounds_support;
use crate::property_xml::{Formula, Property};
use crate::reduction::{
    apply_final_place_gcd_scaling, reduce_iterative_structural_with_protected,
    reduce_query_guarded, ReducedNet,
};

use super::super::model::prepare_upper_bounds_properties;
use super::super::pipeline::{apply_upper_bounds_prefire, check_upper_bounds_properties};
use super::fixtures::*;

#[test]
fn test_upper_bounds_prefire_advances_unobserved_setup_places() {
    let net = prefire_setup_net();
    let props = vec![Property {
        id: "prefire-UpperBounds-00".to_string(),
        formula: Formula::PlaceBound(vec!["query".to_string()]),
    }];

    let (_prepared, trackers) = prepare_upper_bounds_properties(&net, &props);
    let mut reduced = ReducedNet::identity(&net);
    let changed =
        apply_upper_bounds_prefire(&mut reduced, &trackers).expect("prefire should succeed");

    assert!(changed);
    assert_eq!(reduced.net.initial_marking, vec![0, 3, 0]);
    assert_eq!(
        check_upper_bounds_properties(&net, &props, &default_config()),
        vec![(String::from("prefire-UpperBounds-00"), Some(3))]
    );
}

#[test]
fn test_upper_bounds_prefire_protects_query_places() {
    let net = prefire_setup_net();
    let props = vec![Property {
        id: "protected-UpperBounds-00".to_string(),
        formula: Formula::PlaceBound(vec!["setup".to_string()]),
    }];

    let (_prepared, trackers) = prepare_upper_bounds_properties(&net, &props);
    let mut reduced = ReducedNet::identity(&net);
    let changed =
        apply_upper_bounds_prefire(&mut reduced, &trackers).expect("prefire should succeed");

    assert!(!changed);
    assert_eq!(reduced.net.initial_marking, net.initial_marking);
}

#[test]
fn test_upper_bounds_prefire_protects_reconstructed_query_places() {
    let net = reconstructed_query_prefire_net();
    let props = vec![Property {
        id: "reconstructed-UpperBounds-00".to_string(),
        formula: Formula::PlaceBound(vec!["p2".to_string()]),
    }];

    let (_prepared, trackers) = prepare_upper_bounds_properties(&net, &props);

    // Use query-protected reduction (matching production pipeline) so that
    // the support mapping can trace p2 through reconstruction terms.
    let unresolved_place_sets = vec![trackers[0].place_indices.clone()];
    let initial_protected =
        upper_bounds_support(&ReducedNet::identity(&net), &unresolved_place_sets)
            .map(|s| s.places)
            .unwrap_or_else(|| vec![true; net.num_places()]);
    let reduced = reduce_iterative_structural_with_protected(&net, &initial_protected)
        .expect("protected reduction should succeed");
    let mut reduced = reduce_query_guarded(reduced, |r| {
        let support = upper_bounds_support(r, &unresolved_place_sets)?;
        Some(support.places)
    })
    .expect("query-guarded reduction should succeed");
    apply_final_place_gcd_scaling(&mut reduced).expect("GCD scaling should succeed");

    let support = upper_bounds_support(&reduced, &unresolved_place_sets)
        .expect("reconstructed queried place should map through reconstruction terms");

    // After protected reduction, p2 is reconstructed from the remaining places.
    assert!(
        support.places.iter().any(|&p| p),
        "at least one place should be in support"
    );

    let changed =
        apply_upper_bounds_prefire(&mut reduced, &trackers).expect("prefire should succeed");

    // Prefire should not advance places that are in the query support.
    assert!(!changed);
}
