// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared test fixtures and helpers for UpperBounds tests.

use crate::examinations::query_support::upper_bounds_support;
use crate::explorer::ExplorationConfig;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
use crate::property_xml::Property;
use crate::reduction::{
    apply_final_place_gcd_scaling, reduce_iterative_structural_with_protected,
    reduce_query_guarded, ReducedNet,
};

use super::super::model::{
    assemble_upper_bounds_results, prepare_upper_bounds_properties, structural_query_bound,
    BoundTracker,
};
use super::super::observer::UpperBoundsObserver;
use super::super::pipeline::explore_upper_bounds_on_reduced_net;

pub(super) fn simple_net() -> PetriNet {
    // Simple net: p0 -> t0 -> p1, initial marking [3, 0]
    PetriNet {
        name: Some("test".to_string()),
        places: vec![
            PlaceInfo {
                id: "p0".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "p1".to_string(),
                name: None,
            },
        ],
        transitions: vec![TransitionInfo {
            id: "t0".to_string(),
            name: None,
            inputs: vec![Arc {
                place: PlaceIdx(0),
                weight: 1,
            }],
            outputs: vec![Arc {
                place: PlaceIdx(1),
                weight: 1,
            }],
        }],
        initial_marking: vec![3, 0],
    }
}

pub(super) fn default_config() -> ExplorationConfig {
    ExplorationConfig::default()
}

pub(super) fn parallel_config() -> ExplorationConfig {
    ExplorationConfig::default().with_workers(4)
}

pub(super) fn parallel_budget_config(max_states: usize) -> ExplorationConfig {
    ExplorationConfig::new(max_states).with_workers(4)
}

pub(super) fn query_slice_budget_net() -> PetriNet {
    PetriNet {
        name: Some("upper-bounds-query-slice-budget".to_string()),
        places: vec![
            PlaceInfo {
                id: "r0".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "r1".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "i0_l".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "i0_r".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "i1_l".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "i1_r".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "i2_l".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "i2_r".to_string(),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "i0_f".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(3),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "i0_b".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(3),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "i1_f".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(4),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(5),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "i1_b".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(5),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(4),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "i2_f".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(6),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(7),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "i2_b".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(7),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(6),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "t0".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "t1".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "t2".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
                outputs: vec![],
            },
        ],
        initial_marking: vec![1, 1, 1, 0, 1, 0, 1, 0],
    }
}

pub(super) fn connected_sink_tail_net() -> PetriNet {
    PetriNet {
        name: Some("upper-bounds-connected-sink-tail".to_string()),
        places: vec![
            PlaceInfo {
                id: "p0".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "p1".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "p_sink".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "p_dead".to_string(),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "t0".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
                outputs: vec![
                    Arc {
                        place: PlaceIdx(1),
                        weight: 1,
                    },
                    Arc {
                        place: PlaceIdx(2),
                        weight: 1,
                    },
                ],
            },
            TransitionInfo {
                id: "t_sink".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(3),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![1, 0, 0, 0],
    }
}

pub(super) fn prefire_setup_net() -> PetriNet {
    PetriNet {
        name: Some("prefire-setup".to_string()),
        places: vec![
            PlaceInfo {
                id: "setup".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "buffer".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "query".to_string(),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "t_setup".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "t_use".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![3, 0, 0],
    }
}

pub(super) fn reconstructed_query_prefire_net() -> PetriNet {
    PetriNet {
        name: Some("reconstructed-query-prefire".to_string()),
        places: vec![
            PlaceInfo {
                id: "p0".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "p1".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "p2".to_string(),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "t_blocked".to_string(),
                name: None,
                inputs: vec![
                    Arc {
                        place: PlaceIdx(0),
                        weight: 10,
                    },
                    Arc {
                        place: PlaceIdx(1),
                        weight: 1,
                    },
                ],
                outputs: vec![
                    Arc {
                        place: PlaceIdx(0),
                        weight: 10,
                    },
                    Arc {
                        place: PlaceIdx(2),
                        weight: 1,
                    },
                ],
            },
            TransitionInfo {
                id: "t_ok".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![1, 3, 0],
    }
}

/// Non-slicing version of check_upper_bounds_properties for comparison tests.
pub(super) fn check_upper_bounds_properties_unsliced(
    net: &PetriNet,
    properties: &[Property],
    config: &ExplorationConfig,
) -> Vec<(String, Option<u64>)> {
    let (prepared, mut trackers) = prepare_upper_bounds_properties(net, properties);
    if trackers.is_empty() {
        return prepared
            .into_iter()
            .map(|property| match property {
                super::super::model::PreparedUpperBoundProperty::Invalid { id } => (id, None),
                super::super::model::PreparedUpperBoundProperty::Valid { .. } => unreachable!(),
            })
            .collect();
    }

    let invariants = crate::invariant::compute_p_invariants(net);
    let mut structural_count = 0usize;
    for tracker in &mut trackers {
        tracker.structural_bound = structural_query_bound(&invariants, &tracker.place_indices);
        tracker.max_bound = tracker
            .place_indices
            .iter()
            .map(|place| net.initial_marking[place.0 as usize])
            .sum();
        if tracker.is_structurally_resolved() {
            structural_count += 1;
        }
    }

    for tracker in &mut trackers {
        if tracker.is_structurally_resolved() {
            continue;
        }
        if let Some(bound) = crate::lp_state_equation::lp_upper_bound(net, &tracker.place_indices) {
            tracker.lp_bound = Some(bound);
            if tracker.is_structurally_resolved() {
                structural_count += 1;
            }
        }
    }

    if structural_count == trackers.len() {
        return assemble_upper_bounds_results(&prepared, &trackers, true);
    }

    // Mirror the production pipeline's query-protected reduction (without slicing).
    // Using bare `reduce_iterative` (unprotected) can eliminate query-relevant
    // places, causing the expanding observer to reconstruct wrong bounds.
    let unresolved_place_sets: Vec<Vec<PlaceIdx>> = trackers
        .iter()
        .filter(|tracker| !tracker.is_structurally_resolved())
        .map(|tracker| tracker.place_indices.clone())
        .collect();
    let initial_protected = if unresolved_place_sets.is_empty() {
        vec![false; net.num_places()]
    } else {
        upper_bounds_support(&ReducedNet::identity(net), &unresolved_place_sets)
            .map(|support| support.places)
            .unwrap_or_else(|| vec![true; net.num_places()])
    };
    let reduced = reduce_iterative_structural_with_protected(net, &initial_protected)
        .expect("protected reduction should succeed");
    let mut reduced = reduce_query_guarded(reduced, |r| {
        let sets: Vec<Vec<PlaceIdx>> = trackers
            .iter()
            .filter(|t| !t.is_structurally_resolved())
            .map(|t| t.place_indices.clone())
            .collect();
        if sets.is_empty() {
            return None;
        }
        let support = upper_bounds_support(r, &sets)?;
        Some(support.places)
    })
    .expect("query-guarded reduction should succeed");
    apply_final_place_gcd_scaling(&mut reduced).expect("GCD scaling should succeed");
    let config = config.refitted_for_net(&reduced.net);
    let (result, trackers) = explore_upper_bounds_on_reduced_net(&reduced, trackers, &config)
        .expect("reduced-net exploration should not overflow");
    assemble_upper_bounds_results(&prepared, &trackers, result.completed)
}

pub(super) fn single_tracker_observer(
    id: &str,
    place_indices: Vec<PlaceIdx>,
) -> UpperBoundsObserver {
    UpperBoundsObserver::new(vec![BoundTracker {
        id: id.to_string(),
        place_indices,
        max_bound: 0,
        structural_bound: None,
        lp_bound: None,
    }])
}
