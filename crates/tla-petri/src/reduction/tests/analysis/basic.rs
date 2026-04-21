// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};
use crate::reduction::{
    analyze, find_never_disabling_arcs, find_non_decreasing_places, find_parallel_places,
    find_source_places, find_token_eliminated_places,
};

use super::super::super::model::{NeverDisablingArc, NeverDisablingProof};
use super::super::support::{
    arc, parallel_token_elimination_net, place, token_elimination_net, trans,
};

#[test]
fn test_constant_place_self_loop() {
    let net = PetriNet {
        name: Some("self-loop".into()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1), arc(1, 1)], vec![arc(0, 1)])],
        initial_marking: vec![5, 3],
    };

    let report = analyze(&net);
    assert_eq!(report.constant_places, vec![PlaceIdx(0)]);
    assert!(report.dead_transitions.is_empty());
}

#[test]
fn test_no_constant_places_in_producer_consumer() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![3, 0],
    };

    let report = analyze(&net);
    assert!(report.constant_places.is_empty());
}

#[test]
fn test_constant_place_multiple_transitions() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1), arc(1, 1)], vec![arc(0, 1)]),
            trans("t1", vec![arc(0, 1)], vec![arc(0, 1), arc(1, 1)]),
        ],
        initial_marking: vec![1, 1],
    };

    let report = analyze(&net);
    assert_eq!(report.constant_places, vec![PlaceIdx(0)]);
}

#[test]
fn test_dead_transition_no_producer() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 5)], vec![arc(1, 1)])],
        initial_marking: vec![0, 0],
    };

    let report = analyze(&net);
    assert_eq!(report.dead_transitions, vec![TransitionIdx(0)]);
}

#[test]
fn test_not_dead_if_has_producer() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(1, 1)], vec![arc(0, 3)]),
            trans("t1", vec![arc(0, 3)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![0, 5],
    };

    let report = analyze(&net);
    assert!(report.dead_transitions.is_empty());
}

#[test]
fn test_not_dead_if_initial_sufficient() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 3)], vec![arc(1, 1)])],
        initial_marking: vec![3, 0],
    };

    let report = analyze(&net);
    assert!(report.dead_transitions.is_empty());
}

#[test]
fn test_isolated_place() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![1, 0, 42],
    };

    let report = analyze(&net);
    assert_eq!(report.isolated_places, vec![PlaceIdx(2)]);
}

#[test]
fn test_no_isolated_places() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![1, 0],
    };

    let report = analyze(&net);
    assert!(report.isolated_places.is_empty());
}

#[test]
fn test_report_places_removed_deduplicates() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(0, 1)])],
        initial_marking: vec![1, 0, 0],
    };

    let report = analyze(&net);
    assert_eq!(report.constant_places, vec![PlaceIdx(0)]);
    assert_eq!(report.isolated_places, vec![PlaceIdx(1), PlaceIdx(2)]);
    assert_eq!(report.places_removed(), 3);
}

#[test]
fn test_source_place_detection_finds_unprotected_accumulator_only() {
    let net = PetriNet {
        name: Some("source-place".into()),
        places: vec![
            place("p_gate"),
            place("p_acc"),
            place("p_work"),
            place("p_iso"),
        ],
        transitions: vec![
            trans(
                "t_fill",
                vec![arc(0, 1)],
                vec![arc(0, 1), arc(1, 1), arc(2, 1)],
            ),
            trans("t_consume", vec![arc(2, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0, 0, 7],
    };

    let detected = find_source_places(&net, &[], &[false, false, false, false]);

    assert_eq!(detected, vec![PlaceIdx(1)]);
}

#[test]
fn test_source_place_detection_skips_protected_accumulator() {
    let net = PetriNet {
        name: Some("protected-source-place".into()),
        places: vec![place("p_gate"), place("p_acc"), place("p_work")],
        transitions: vec![
            trans(
                "t_fill",
                vec![arc(0, 1)],
                vec![arc(0, 1), arc(1, 1), arc(2, 1)],
            ),
            trans("t_consume", vec![arc(2, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0, 0],
    };

    let detected = find_source_places(&net, &[], &[false, true, false]);

    assert!(detected.is_empty());
}

#[test]
fn test_analyze_populates_non_decreasing_place_report() {
    let net = PetriNet {
        name: Some("rule-f-detect".into()),
        places: vec![place("p_mono"), place("p_keep")],
        transitions: vec![
            trans("t_grow", vec![arc(0, 1)], vec![arc(0, 2), arc(1, 1)]),
            trans("t_keep", vec![arc(1, 1)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    let report = analyze(&net);

    assert_eq!(report.non_decreasing_places, vec![PlaceIdx(0)]);
}

#[test]
fn test_non_decreasing_place_helper_skips_protected_place() {
    let net = PetriNet {
        name: Some("protected-rule-f".into()),
        places: vec![place("p_mono"), place("p_keep")],
        transitions: vec![
            trans("t_grow", vec![arc(0, 1)], vec![arc(0, 2), arc(1, 1)]),
            trans("t_keep", vec![arc(1, 1)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    let report = analyze(&net);
    let detected = find_non_decreasing_places(&net, &report.dead_transitions, &[true, false], &[]);

    assert!(detected.is_empty());
}

#[test]
fn test_non_decreasing_place_requires_initial_marking_guard() {
    let net = PetriNet {
        name: Some("rule-f-initial-guard".into()),
        places: vec![place("p_mono"), place("p_seed"), place("p_keep")],
        transitions: vec![
            trans("t_seed", vec![arc(1, 1)], vec![arc(1, 1), arc(0, 2)]),
            trans("t_grow", vec![arc(0, 2)], vec![arc(0, 3), arc(2, 1)]),
            trans("t_keep", vec![arc(2, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![1, 1, 0],
    };

    let report = analyze(&net);
    let detected = find_non_decreasing_places(&net, &report.dead_transitions, &[false; 3], &[]);

    assert!(
        !detected.contains(&PlaceIdx(0)),
        "Rule F must keep p_mono when its initial marking does not cover the maximum consumer weight; got {:?}, dead={:?}",
        detected, report.dead_transitions,
    );
}

#[test]
fn test_non_decreasing_place_not_confused_with_source() {
    let net = PetriNet {
        name: Some("rule-f-vs-source".into()),
        places: vec![place("p_src"), place("p_gate"), place("p_sink")],
        transitions: vec![trans("t_fill", vec![arc(1, 1)], vec![arc(0, 1), arc(2, 1)])],
        initial_marking: vec![0, 1, 0],
    };

    let report = analyze(&net);
    let detected = find_non_decreasing_places(&net, &report.dead_transitions, &[false; 3], &[]);

    assert!(detected.is_empty());
}

#[test]
fn test_never_disabling_arc_detected_from_invariant_lower_bound() {
    let net = PetriNet {
        name: Some("rule-n-detect".into()),
        places: vec![
            place("p_cap"),
            place("p_use"),
            place("p_res"),
            place("p_probe"),
        ],
        transitions: vec![
            trans("t_use", vec![arc(0, 1), arc(2, 1)], vec![arc(1, 1)]),
            trans("t_release", vec![arc(1, 1)], vec![arc(0, 1), arc(2, 1)]),
            trans(
                "t_probe",
                vec![arc(0, 1), arc(3, 1)],
                vec![arc(0, 1), arc(3, 1)],
            ),
        ],
        initial_marking: vec![5, 0, 3, 1],
    };

    let report = analyze(&net);
    let detected = find_never_disabling_arcs(
        &net,
        &report.dead_transitions,
        &report.self_loop_transitions,
        &[false, false, false, false],
    );

    assert_eq!(detected.len(), 1, "only p_cap -> t_use should be removable");
    assert_eq!(detected[0].transition, TransitionIdx(0));
    assert_eq!(detected[0].place, PlaceIdx(0));
    assert_eq!(detected[0].weight, 1);
    assert!(
        detected[0].proof.lower_bound() >= 2,
        "P-invariants should prove p_cap always has at least 2 tokens"
    );
}

#[test]
fn test_never_disabling_arc_skips_insufficient_lower_bound() {
    let net = PetriNet {
        name: Some("rule-n-negative".into()),
        places: vec![place("p_free"), place("p_busy")],
        transitions: vec![
            trans("t_enter", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_exit", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    let report = analyze(&net);
    let detected = find_never_disabling_arcs(
        &net,
        &report.dead_transitions,
        &report.self_loop_transitions,
        &[false, false],
    );

    assert!(
        detected.is_empty(),
        "mutex arcs should stay because the invariant only proves a zero lower bound"
    );
}

#[test]
fn test_token_eliminated_place_detected_beyond_rule_f() {
    let net = token_elimination_net();

    let report = analyze(&net);
    let source_places = find_source_places(&net, &report.dead_transitions, &[false; 4]);
    let never_disabling = find_never_disabling_arcs(
        &net,
        &report.dead_transitions,
        &report.self_loop_transitions,
        &[false; 4],
    );
    let non_decreasing =
        find_non_decreasing_places(&net, &report.dead_transitions, &[false; 4], &source_places);
    let token_eliminated = find_token_eliminated_places(
        &net,
        &report.dead_transitions,
        &report.self_loop_transitions,
        &[false; 4],
        &report.parallel_places,
        &source_places,
        &non_decreasing,
        &never_disabling,
    );

    assert_eq!(source_places, vec![PlaceIdx(3)]);
    assert!(
        !non_decreasing.contains(&PlaceIdx(0)),
        "p_cap must not be mistaken for Rule F"
    );
    assert_eq!(never_disabling.len(), 1);
    assert_eq!(never_disabling[0].place, PlaceIdx(0));
    assert_eq!(never_disabling[0].transition, TransitionIdx(0));
    assert_eq!(token_eliminated, vec![PlaceIdx(0)]);
}

#[test]
fn test_token_elimination_skips_parallel_place_participants() {
    let net = parallel_token_elimination_net();

    let report = analyze(&net);
    let source_places = find_source_places(&net, &report.dead_transitions, &[false; 5]);
    let never_disabling = vec![
        NeverDisablingArc {
            transition: TransitionIdx(0),
            place: PlaceIdx(0),
            weight: 1,
            proof: NeverDisablingProof::PInvariant {
                invariant_idx: 0,
                lower_bound: 1,
            },
        },
        NeverDisablingArc {
            transition: TransitionIdx(0),
            place: PlaceIdx(1),
            weight: 1,
            proof: NeverDisablingProof::PInvariant {
                invariant_idx: 1,
                lower_bound: 1,
            },
        },
    ];
    let non_decreasing =
        find_non_decreasing_places(&net, &report.dead_transitions, &[false; 5], &source_places);
    let token_eliminated = find_token_eliminated_places(
        &net,
        &report.dead_transitions,
        &report.self_loop_transitions,
        &[false; 5],
        &report.parallel_places,
        &source_places,
        &non_decreasing,
        &never_disabling,
    );

    assert_eq!(report.parallel_places.len(), 1);
    assert!(token_eliminated.is_empty());
}

#[test]
fn test_cascading_dead_transitions() {
    let net = PetriNet {
        name: Some("cascade-chain".into()),
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t2", vec![arc(2, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![0, 0, 0, 0],
    };

    let report = analyze(&net);
    assert_eq!(report.dead_transitions.len(), 3);
}

#[test]
fn test_cascade_with_partial_chain() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t2", vec![arc(3, 1)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![0, 0, 0, 5],
    };

    let report = analyze(&net);
    assert_eq!(report.dead_transitions, vec![TransitionIdx(0)]);
}

#[test]
fn test_cascade_isolated_places() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans("t0_dead", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1_live", vec![arc(2, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![0, 0, 3, 0],
    };

    let report = analyze(&net);
    assert_eq!(report.dead_transitions, vec![TransitionIdx(0)]);
    assert_eq!(report.isolated_places.len(), 2);
}

// ---------------------------------------------------------------------------
// Parallel place detection (Tapaal Rule B)
// ---------------------------------------------------------------------------

#[test]
fn test_parallel_places_detected_for_identical_connectivity() {
    // p0 and p1 have identical arcs to the same transitions with same weights.
    let net = PetriNet {
        name: Some("rule-b-detect".into()),
        places: vec![place("p0"), place("p1"), place("p_other")],
        transitions: vec![
            trans("t0", vec![arc(0, 1), arc(1, 1)], vec![arc(2, 1)]),
            trans("t1", vec![arc(2, 1)], vec![arc(0, 1), arc(1, 1)]),
        ],
        initial_marking: vec![3, 3, 0],
    };

    let report = analyze(&net);
    let detected = find_parallel_places(&net, &report.dead_transitions, &[false, false, false]);

    assert_eq!(report.parallel_places, detected);
    assert_eq!(detected.len(), 1);
    assert_eq!(detected[0].canonical, PlaceIdx(0));
    assert_eq!(detected[0].duplicate, PlaceIdx(1));
}

#[test]
fn test_parallel_places_skipped_when_protected() {
    let net = PetriNet {
        name: Some("rule-b-protected".into()),
        places: vec![place("p0"), place("p1"), place("p_other")],
        transitions: vec![
            trans("t0", vec![arc(0, 1), arc(1, 1)], vec![arc(2, 1)]),
            trans("t1", vec![arc(2, 1)], vec![arc(0, 1), arc(1, 1)]),
        ],
        initial_marking: vec![3, 3, 0],
    };

    let report = analyze(&net);
    let detected = find_parallel_places(
        &net,
        &report.dead_transitions,
        &[false, true, false], // p1 protected
    );

    assert!(detected.is_empty(), "protected place should not be merged");
}

#[test]
fn test_parallel_places_different_marking_not_merged() {
    // Same arcs but different initial markings -> not parallel in k=1 strict mode.
    let net = PetriNet {
        name: Some("rule-b-diff-marking".into()),
        places: vec![place("p0"), place("p1"), place("p_other")],
        transitions: vec![
            trans("t0", vec![arc(0, 1), arc(1, 1)], vec![arc(2, 1)]),
            trans("t1", vec![arc(2, 1)], vec![arc(0, 1), arc(1, 1)]),
        ],
        initial_marking: vec![3, 5, 0], // different markings
    };

    let report = analyze(&net);
    let detected = find_parallel_places(&net, &report.dead_transitions, &[false, false, false]);

    assert!(
        detected.is_empty(),
        "different initial markings -> not parallel (strict k=1)"
    );
}
