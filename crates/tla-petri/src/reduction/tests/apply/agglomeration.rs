// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::petri_net::{PetriNet, PlaceIdx};
use crate::reduction::{reduce, reduce_iterative};

use super::super::support::{arc, place, trans};

#[test]
fn test_reduce_pre_agglomeration_simple_chain() {
    // t0: p_in →(1) t0 →(1) p_mid →(1) t1 →(1) p_out
    // Pre-agg removes t0 and p_mid, merges t0's inputs into t1.
    // t_sink prevents p_out from being removed as source (Rule C).
    let net = PetriNet {
        name: None,
        places: vec![place("p_in"), place("p_mid"), place("p_out")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t_sink", vec![arc(2, 1)], vec![]),
        ],
        initial_marking: vec![1, 0, 0],
    };

    let reduced = reduce(&net);

    // p_mid removed, then t_sink/p_out collapse away via post-agglomeration.
    assert_eq!(reduced.net.num_places(), 1);
    assert_eq!(reduced.net.num_transitions(), 1);
    assert_eq!(reduced.net.places[0].id, "p_in");

    // Surviving transition t1, now reading from p_in instead of p_mid.
    let t = &reduced.net.transitions[0];
    assert_eq!(t.id, "t1");
    assert_eq!(t.inputs.len(), 1);
    assert_eq!(t.inputs[0].place, PlaceIdx(0)); // p_in (remapped)
    assert_eq!(t.inputs[0].weight, 1);
    assert_eq!(t.outputs.len(), 0);

    // Marking expansion: p_mid gets its constant value (0).
    assert_eq!(
        reduced
            .expand_marking(&reduced.net.initial_marking)
            .expect("marking expansion should succeed"),
        vec![1, 0, 0]
    );
}

#[test]
fn test_reduce_pre_agglomeration_multiple_successors() {
    // t0 →(1) p_mid, p_mid →(1) t1, p_mid →(1) t2
    // Both t1 and t2 get t0's inputs merged in.
    // t1 and t2 write to shared p_out, which has a consumer to prevent Rule C.
    let net = PetriNet {
        name: None,
        places: vec![place("p_in"), place("p_mid"), place("p_out")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t2", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t_sink", vec![arc(2, 1)], vec![]),
        ],
        initial_marking: vec![1, 0, 0],
    };

    let reduced = reduce(&net);

    // p_mid removed, then t_sink/p_out collapse away and the merged successors
    // deduplicate into one surviving transition.
    assert_eq!(reduced.net.num_places(), 1); // p_in
    assert_eq!(reduced.net.num_transitions(), 1);
    assert_eq!(reduced.net.transitions[0].inputs[0].place, PlaceIdx(0)); // p_in
}

#[test]
fn test_reduce_pre_agglomeration_shared_input_combines_weights() {
    // t0 reads 2 from p_shared, writes 1 to p_mid.
    // t1 reads 1 from p_mid and 3 from p_shared, writes to p_out.
    // After pre-agg: merged t1 reads 2+3=5 from p_shared.
    // t_sink prevents p_out from being removed as source (Rule C).
    let net = PetriNet {
        name: None,
        places: vec![place("p_shared"), place("p_mid"), place("p_out")],
        transitions: vec![
            trans("t0", vec![arc(0, 2)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1), arc(0, 3)], vec![arc(2, 1)]),
            trans("t_sink", vec![arc(2, 1)], vec![]),
        ],
        initial_marking: vec![10, 0, 0],
    };

    let reduced = reduce(&net);

    assert_eq!(reduced.net.num_places(), 1); // p_shared
    assert_eq!(reduced.net.num_transitions(), 1); // t1

    let t = &reduced.net.transitions[0];
    assert_eq!(t.id, "t1");
    // p_shared should have combined weight: 2 (from t0) + 3 (from t1) = 5
    assert_eq!(t.inputs.len(), 1);
    assert_eq!(t.inputs[0].place, PlaceIdx(0)); // p_shared
    assert_eq!(t.inputs[0].weight, 5);
    assert_eq!(t.outputs.len(), 0);
}

#[test]
fn test_reduce_post_agglomeration_multiple_predecessors() {
    // t0 →(1) p_mid, t1 →(1) p_mid, p_mid →(1) t2 →(1) p_out
    // Post-agg removes t2 and p_mid, merges t2's outputs into t0 and t1.
    // t_sink prevents p_out from being removed as a source place (Rule C).
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_in1"),
            place("p_in2"),
            place("p_mid"),
            place("p_out"),
        ],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(2, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t2", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t_sink", vec![arc(3, 1)], vec![]),
        ],
        initial_marking: vec![1, 1, 0, 0],
    };

    let reduced = reduce(&net);

    // p_mid and t2 removed.
    assert_eq!(reduced.net.num_places(), 3); // p_in1, p_in2, p_out
    assert_eq!(reduced.net.num_transitions(), 3); // t0, t1, t_sink

    // Both t0 and t1 now write to p_out (t_sink has no outputs).
    for t in reduced.net.transitions.iter().take(2) {
        assert_eq!(t.outputs.len(), 1);
        assert_eq!(t.outputs[0].place, PlaceIdx(2)); // p_out (remapped)
    }
}

#[test]
fn test_reduce_iterative_agglomeration_then_constant() {
    // t0: p_const →(1) t0 →(1) p_mid →(1) t1 →(1) p_out
    // p_const is a self-loop on t0 (constant place, but t0 also writes to p_mid).
    // Wait — t0 writes to p_mid only. For p_const to be constant, t0 must
    // have net-zero effect. Let me construct properly:
    //
    // t0: reads p_const(1), p_src(1); writes p_const(1), p_mid(1)
    //   — p_const is constant (in=out), p_src consumed.
    // t1: reads p_mid(1); writes p_out(1)
    //
    // Pass 1: pre-agg finds t0→p_mid→t1 chain, removes t0+p_mid.
    //   merged t1 reads from p_const and p_src.
    // Pass 2: p_const still constant. Removed.
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_const"),
            place("p_src"),
            place("p_mid"),
            place("p_out"),
        ],
        transitions: vec![
            trans("t0", vec![arc(0, 1), arc(1, 1)], vec![arc(0, 1), arc(2, 1)]),
            trans("t1", vec![arc(2, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![1, 5, 0, 0],
    };

    let iterative = reduce_iterative(&net).expect("reduction should succeed");

    // Pass 1: p_const removed (constant), p_mid + t0 removed (agglomerated).
    //   Merged t1: {p_src→1}→{p_out→1}.
    // Pass 2: p_out LP-redundant (p_out = 5 - p_src, never constrains).
    //   Surviving: p_src only.
    assert_eq!(iterative.net.num_places(), 1);
    assert_eq!(iterative.net.num_transitions(), 1);
    assert_eq!(iterative.net.places[0].id, "p_src");

    // Merged t1 reads from p_src (weight 1).
    let t = &iterative.net.transitions[0];
    assert_eq!(t.inputs.len(), 1);
    assert_eq!(t.inputs[0].place, PlaceIdx(0)); // p_src
}
