// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
use crate::reduction::ReducedNet;

pub(super) fn place(id: &str) -> PlaceInfo {
    PlaceInfo {
        id: id.to_string(),
        name: Some(id.to_string()),
    }
}

pub(super) fn arc(place: u32, weight: u64) -> Arc {
    Arc {
        place: PlaceIdx(place),
        weight,
    }
}

pub(super) fn trans(id: &str, inputs: Vec<Arc>, outputs: Vec<Arc>) -> TransitionInfo {
    TransitionInfo {
        id: id.to_string(),
        name: Some(id.to_string()),
        inputs,
        outputs,
    }
}

/// Net with two P-invariants enabling cross-bound tightening:
///   Inv1: p_cap + 2*p_mid = 10   (from t_fwd/t_back incidence)
///   Inv2: p_mid + p_obs  = 3     (from t_fwd/t_back incidence)
///
/// Upper(p_mid) = min(10/2, 3/1) = 3  (tightened by Inv2)
/// Lower(p_cap) = (10 - 2*3)/1  = 4   (positive → never-disabling proof)
///
/// t_fwd consumes 2 from p_cap → 4 >= 2 → never_disabling_arc exists.
/// p_aux is only produced (by t_back), never consumed → source place.
pub(super) fn token_elimination_net() -> PetriNet {
    PetriNet {
        name: Some("token-elimination".to_string()),
        places: vec![
            place("p_cap"),
            place("p_mid"),
            place("p_obs"),
            place("p_aux"),
        ],
        transitions: vec![
            // t_fwd: consumes 2 from p_cap, 1 from p_obs; produces 1 to p_mid
            trans("t_fwd", vec![arc(0, 2), arc(2, 1)], vec![arc(1, 1)]),
            // t_back: consumes 1 from p_mid; produces 2 to p_cap, 1 to p_obs, 1 to p_aux
            trans(
                "t_back",
                vec![arc(1, 1)],
                vec![arc(0, 2), arc(2, 1), arc(3, 1)],
            ),
        ],
        initial_marking: vec![4, 3, 0, 0],
    }
}

pub(super) fn parallel_token_elimination_net() -> PetriNet {
    PetriNet {
        name: Some("parallel-token-elimination".to_string()),
        places: vec![
            place("p_cap0"),
            place("p_cap1"),
            place("p_use"),
            place("p_res"),
            place("p_aux"),
        ],
        transitions: vec![
            trans(
                "t_use",
                vec![arc(0, 1), arc(1, 1), arc(3, 2)],
                vec![arc(2, 2)],
            ),
            trans(
                "t_release",
                vec![arc(2, 2)],
                vec![arc(0, 1), arc(1, 1), arc(3, 2)],
            ),
            trans("t_buffer", vec![arc(2, 2)], vec![arc(3, 2), arc(4, 1)]),
        ],
        initial_marking: vec![5, 5, 0, 3, 0],
    }
}

pub(super) fn assert_same_reduced_net(actual: &ReducedNet, expected: &ReducedNet) {
    assert_eq!(actual.place_map, expected.place_map);
    assert_eq!(actual.place_unmap, expected.place_unmap);
    assert_eq!(actual.place_scales, expected.place_scales);
    assert_eq!(actual.transition_map, expected.transition_map);
    assert_eq!(actual.transition_unmap, expected.transition_unmap);
    assert_eq!(actual.constant_values, expected.constant_values);
    assert_eq!(
        actual.report.constant_places,
        expected.report.constant_places
    );
    assert_eq!(
        actual.report.dead_transitions,
        expected.report.dead_transitions
    );
    assert_eq!(actual.report.source_places, expected.report.source_places);
    assert_eq!(
        actual.report.isolated_places,
        expected.report.isolated_places
    );
    assert_eq!(
        actual.report.token_eliminated_places,
        expected.report.token_eliminated_places
    );
    assert_eq!(
        actual.report.pre_agglomerations.len(),
        expected.report.pre_agglomerations.len()
    );
    assert_eq!(
        actual.report.post_agglomerations.len(),
        expected.report.post_agglomerations.len()
    );
    assert_eq!(actual.net.name, expected.net.name);
    assert_eq!(actual.net.initial_marking, expected.net.initial_marking);

    let actual_places: Vec<_> = actual
        .net
        .places
        .iter()
        .map(|place| (place.id.as_str(), place.name.as_deref()))
        .collect();
    let expected_places: Vec<_> = expected
        .net
        .places
        .iter()
        .map(|place| (place.id.as_str(), place.name.as_deref()))
        .collect();
    assert_eq!(actual_places, expected_places);

    let actual_transitions: Vec<_> = actual
        .net
        .transitions
        .iter()
        .map(|transition| {
            (
                transition.id.as_str(),
                transition.name.as_deref(),
                transition
                    .inputs
                    .iter()
                    .map(|arc| (arc.place.0, arc.weight))
                    .collect::<Vec<_>>(),
                transition
                    .outputs
                    .iter()
                    .map(|arc| (arc.place.0, arc.weight))
                    .collect::<Vec<_>>(),
            )
        })
        .collect();
    let expected_transitions: Vec<_> = expected
        .net
        .transitions
        .iter()
        .map(|transition| {
            (
                transition.id.as_str(),
                transition.name.as_deref(),
                transition
                    .inputs
                    .iter()
                    .map(|arc| (arc.place.0, arc.weight))
                    .collect::<Vec<_>>(),
                transition
                    .outputs
                    .iter()
                    .map(|arc| (arc.place.0, arc.weight))
                    .collect::<Vec<_>>(),
            )
        })
        .collect();
    assert_eq!(actual_transitions, expected_transitions);
}
