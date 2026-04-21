// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};
use crate::reduction::{reduce, reduce_iterative, reduce_iterative_structural_with_protected};

use super::super::support::{arc, place, trans};

#[test]
fn test_reduce_removes_constant_and_isolated() {
    let net = PetriNet {
        name: Some("test".into()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![trans("t0", vec![arc(0, 1), arc(1, 1)], vec![arc(0, 1)])],
        initial_marking: vec![5, 3, 42],
    };

    let reduced = reduce(&net);

    assert_eq!(reduced.net.num_places(), 1);
    assert_eq!(reduced.net.places[0].id, "p1");
    assert_eq!(reduced.net.initial_marking, vec![3]);
    assert_eq!(
        reduced.constant_values,
        vec![(PlaceIdx(0), 5), (PlaceIdx(2), 42)]
    );
    assert_eq!(reduced.place_map[0], None);
    assert_eq!(reduced.place_map[1], Some(PlaceIdx(0)));
    assert_eq!(reduced.place_map[2], None);

    let t = &reduced.net.transitions[0];
    assert_eq!(t.inputs.len(), 1);
    assert_eq!(t.inputs[0].place, PlaceIdx(0));
    assert!(t.outputs.is_empty());
}

#[test]
fn test_reduce_removes_dead_transitions() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans("t0_dead", vec![arc(0, 10)], vec![arc(2, 1)]),
            trans("t1_live", vec![arc(1, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![0, 5, 0],
    };

    let reduced = reduce(&net);

    assert_eq!(reduced.net.num_transitions(), 1);
    assert_eq!(reduced.net.transitions[0].id, "t1_live");
    assert_eq!(reduced.transition_map[0], None);
    assert_eq!(reduced.transition_map[1], Some(TransitionIdx(0)));
}

#[test]
fn test_reduce_duplicate_transition_aliases_removed_id_to_survivor() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_back", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    let reduced = reduce(&net);

    assert_eq!(reduced.net.num_transitions(), 2);
    assert_eq!(reduced.net.transitions[0].id, "t0");
    assert_eq!(
        reduced.transition_unmap,
        vec![TransitionIdx(0), TransitionIdx(2)]
    );
    assert_eq!(reduced.transition_map[0], Some(TransitionIdx(0)));
    assert_eq!(reduced.transition_map[1], Some(TransitionIdx(0)));
    assert_eq!(reduced.transition_map[2], Some(TransitionIdx(1)));
    assert_eq!(reduced.report.duplicate_transitions.len(), 1);
    assert_eq!(
        reduced.report.duplicate_transitions[0].canonical,
        TransitionIdx(0)
    );
    assert_eq!(
        reduced.report.duplicate_transitions[0].duplicates,
        vec![TransitionIdx(1)]
    );
}

#[test]
fn test_reduce_duplicate_transition_keeps_canonical_id_stable() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t2", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_back", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    let reduced = reduce(&net);

    assert_eq!(reduced.net.num_transitions(), 2);
    assert_eq!(reduced.transition_unmap[0], TransitionIdx(0));
    assert_eq!(reduced.transition_map[0], Some(TransitionIdx(0)));
    assert_eq!(reduced.transition_map[1], Some(TransitionIdx(0)));
    assert_eq!(reduced.transition_map[2], Some(TransitionIdx(0)));
    assert_eq!(
        reduced.report.duplicate_transitions[0].duplicates,
        vec![TransitionIdx(1), TransitionIdx(2)]
    );
}

#[test]
fn test_reduce_identity_when_no_reductions() {
    // Mutex net: both places constrain their transitions, so neither is
    // LP-redundant despite the P-invariant p0 + p1 = 1.
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t_enter", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_exit", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    let reduced = reduce(&net);
    assert_eq!(reduced.net.num_places(), net.num_places());
    assert_eq!(reduced.net.num_transitions(), net.num_transitions());
    assert!(!reduced.report.has_reductions());
}

#[test]
fn test_reduce_removes_source_place_accumulator() {
    let net = PetriNet {
        name: Some("source-place-removal".into()),
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

    let reduced = reduce(&net);

    assert_eq!(reduced.report.source_places, vec![PlaceIdx(1)]);
    assert!(
        reduced.place_map[1].is_none(),
        "source place should be removed"
    );
    // p_gate is also removed by Rule F (non-decreasing: net effect >= 0 from all
    // alive transitions, initial(1) >= max_consume(1)).
    assert!(
        reduced.report.non_decreasing_places.contains(&PlaceIdx(0)),
        "p_gate should be removed by Rule F"
    );
    assert_eq!(reduced.net.num_places(), 1);
}

#[test]
fn test_reduce_with_protected_keeps_source_place() {
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

    let reduced = reduce_iterative_structural_with_protected(&net, &[false, true, false])
        .expect("protected reduction should succeed");

    // p_acc (index 1) is protected and must NOT appear in source_places.
    // Other places may become source places due to Rule K stripping self-loops.
    assert!(
        !reduced.report.source_places.contains(&PlaceIdx(1)),
        "protected source place must not be reported as removable"
    );
    assert!(
        reduced.place_map[1].is_some(),
        "protected p_acc must survive reduction"
    );
}

#[test]
fn test_reduce_iterative_structural_removes_non_decreasing_place() {
    let net = PetriNet {
        name: Some("rule-f-removal".into()),
        places: vec![place("p_mono"), place("p_keep")],
        transitions: vec![
            trans("t_grow", vec![arc(0, 1)], vec![arc(0, 2), arc(1, 1)]),
            trans("t_keep", vec![arc(1, 1)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    let reduced =
        reduce_iterative_structural_with_protected(&net, &[false, false]).expect("reduce");

    assert!(reduced.report.non_decreasing_places.contains(&PlaceIdx(0)));
    assert!(
        reduced.place_map[0].is_none(),
        "non-decreasing place should be removed from the reduced state vector"
    );
}

#[test]
fn test_reduce_with_protected_keeps_non_decreasing_place() {
    let net = PetriNet {
        name: Some("protected-rule-f-removal".into()),
        places: vec![place("p_mono"), place("p_keep")],
        transitions: vec![
            trans("t_grow", vec![arc(0, 1)], vec![arc(0, 2), arc(1, 1)]),
            trans("t_keep", vec![arc(1, 1)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    let reduced = reduce_iterative_structural_with_protected(&net, &[true, false]).expect("reduce");

    assert!(
        !reduced.report.non_decreasing_places.contains(&PlaceIdx(0)),
        "protected non-decreasing place must not be reported as removable"
    );
    assert!(
        reduced.place_map[0].is_some(),
        "protected non-decreasing place must survive reduction"
    );
}

#[test]
fn test_constant_place_blocks_transition() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans(
                "t0_blocked",
                vec![arc(0, 5), arc(1, 1)],
                vec![arc(0, 5), arc(2, 1)],
            ),
            trans(
                "t1_ok",
                vec![arc(0, 1), arc(1, 1)],
                vec![arc(0, 1), arc(2, 1)],
            ),
        ],
        initial_marking: vec![1, 3, 0],
    };

    let reduced = reduce(&net);

    assert_eq!(reduced.net.num_transitions(), 1);
    assert_eq!(reduced.net.transitions[0].id, "t1_ok");
    // p0 removed (constant), p2 LP-redundant (p2 = 3 - p1, never constrains t1_ok).
    assert_eq!(reduced.net.num_places(), 1);
    assert_eq!(reduced.net.places[0].id, "p1");
}

#[test]
fn test_reduced_net_same_reachable_behavior() {
    let net = PetriNet {
        name: Some("mutex".into()),
        places: vec![place("p_free"), place("p_cs")],
        transitions: vec![
            trans("t_enter", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_exit", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    let reduced = reduce(&net);
    assert_eq!(reduced.net.num_places(), 2);
    assert_eq!(reduced.net.num_transitions(), 2);
    assert!(!reduced.report.has_reductions());
}

#[test]
fn test_reduced_net_preserves_enabled_transitions() {
    // t0_dead can't fire (p0 has no producer, initial=0).
    // t1_live reads from p1, writes to p2.
    // t2_sink reads from p2 to prevent Rule C removing p2 as a source place.
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans("t0_dead", vec![arc(0, 100)], vec![arc(1, 1)]),
            trans("t1_live", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t2_sink", vec![arc(2, 1)], vec![]),
        ],
        initial_marking: vec![0, 5, 0],
    };

    let reduced = reduce(&net);

    assert_eq!(reduced.net.num_transitions(), 1);
    assert_eq!(reduced.net.num_places(), 1);
    assert_eq!(reduced.net.places[0].id, "p1");

    let t = TransitionIdx(0);
    assert!(reduced.net.is_enabled(&reduced.net.initial_marking, t));
    let result = reduced.net.fire(&reduced.net.initial_marking, t);
    assert_eq!(result, vec![4]);
}

#[test]
fn test_cascade_with_partial_chain_reduction_keeps_live_suffix() {
    // t0 is dead (p0 has no producer, initial=0).
    // After dead transition removal, t2→p1→t1 forms a pre-agglomeration
    // chain: t2 has one output (p1), p1 has one producer (t2 — t0 is dead),
    // p1 initial=0, t1 reads 1 from p1. Berthelot condition 6 passes
    // (•t2={p3}, t1•={p2}, disjoint).
    // Result: t0 dead, t2+p1 agglomerated, merged t1 reads from p3.
    // t3_sink prevents p2 from being removed as a source place (Rule C).
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t2", vec![arc(3, 1)], vec![arc(1, 1)]),
            trans("t3_sink", vec![arc(2, 1)], vec![]),
        ],
        initial_marking: vec![0, 0, 0, 5],
    };

    let reduced = reduce(&net);
    // t0 dead; the live path survives alongside the sink.
    assert_eq!(reduced.net.num_transitions(), 2);
    let live_path = reduced
        .net
        .transitions
        .iter()
        .find(|transition| transition.id != "t3_sink")
        .expect("the live path transition should survive");
    // The surviving live path now reads from p3 (was p1 before agglomeration).
    assert_eq!(live_path.inputs.len(), 1);
    assert_eq!(live_path.outputs.len(), 1);
}

#[test]
fn test_cascade_isolated_places_reduction_prunes_dead_branch() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans("t0_dead", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1_live", vec![arc(2, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![0, 0, 3, 0],
    };

    let reduced = reduce(&net);
    // t0 dead → p0 and p1 cascade-isolated → p3 LP-redundant.
    assert_eq!(reduced.net.num_places(), 1);
    assert_eq!(reduced.net.num_transitions(), 1);
    assert_eq!(reduced.net.places[0].id, "p2");
}

#[test]
fn test_reduce_iterative_finds_constant_place_after_dead_transition_removal() {
    let net = PetriNet {
        name: Some("iterative-constant".into()),
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans("t_dead", vec![arc(1, 1)], vec![arc(0, 1)]),
            trans(
                "t_live",
                vec![arc(0, 1), arc(2, 1)],
                vec![arc(0, 1), arc(3, 1)],
            ),
        ],
        initial_marking: vec![5, 0, 1, 0],
    };

    // Single pass: t_dead is dead, p1 cascade-isolated, p3 LP-redundant.
    // p0 is non-decreasing (Rule F): only alive transition t_live has net effect 0,
    // consumes(1) <= produces(1), and initial(5) >= max_consume(1).
    let single_pass = reduce(&net);
    assert_eq!(single_pass.report.dead_transitions, vec![TransitionIdx(0)]);
    assert!(single_pass.report.constant_places.is_empty());
    assert!(
        single_pass
            .report
            .non_decreasing_places
            .contains(&PlaceIdx(0)),
        "p0 should be detected as non-decreasing by Rule F"
    );
    assert_eq!(single_pass.net.num_places(), 1);
    assert_eq!(
        single_pass
            .net
            .places
            .iter()
            .map(|place| place.id.as_str())
            .collect::<Vec<_>>(),
        vec!["p2"]
    );

    // Iterative: Rule F removes p0 in pass 1 (non-decreasing with initial(5) >= max_consume(1)).
    // p1 cascade-isolated (dead t_dead), p3 removed as source (Rule C).
    // Final: only p2 survives.
    let iterative = reduce_iterative(&net).expect("reduction should succeed");
    assert_eq!(iterative.report.dead_transitions, vec![TransitionIdx(0)]);
    assert!(iterative.report.constant_places.is_empty());
    // p0 removed by Rule F (non-decreasing).
    assert!(iterative
        .report
        .non_decreasing_places
        .contains(&PlaceIdx(0)));
    // p1 cascade-isolated (dead t_dead).
    assert!(iterative.report.isolated_places.contains(&PlaceIdx(1)));
    assert_eq!(iterative.net.num_places(), 1);
    assert_eq!(iterative.place_map[0], None);
    assert_eq!(
        iterative
            .net
            .places
            .iter()
            .map(|place| place.id.as_str())
            .collect::<Vec<_>>(),
        vec!["p2"]
    );
    assert_eq!(iterative.net.initial_marking, vec![1]);
    assert_eq!(
        iterative
            .expand_marking(&iterative.net.initial_marking)
            .expect("marking expansion should succeed"),
        vec![5, 0, 1, 0]
    );
}
