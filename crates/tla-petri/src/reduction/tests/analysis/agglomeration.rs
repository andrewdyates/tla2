// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};
use crate::reduction::analyze;

use super::super::support::{arc, place, trans};

// ---------------------------------------------------------------------------
// Pre-agglomeration detection
// ---------------------------------------------------------------------------

#[test]
fn test_pre_agglomeration_simple_chain() {
    // t0: p_in ->(1) t0 ->(1) p_mid ->(1) t1 ->(1) p_out
    let net = PetriNet {
        name: None,
        places: vec![place("p_in"), place("p_mid"), place("p_out")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![1, 0, 0],
    };

    let report = analyze(&net);
    assert_eq!(report.pre_agglomerations.len(), 1);
    assert_eq!(report.pre_agglomerations[0].transition, TransitionIdx(0));
    assert_eq!(report.pre_agglomerations[0].place, PlaceIdx(1));
    assert_eq!(
        report.pre_agglomerations[0].successors,
        vec![TransitionIdx(1)]
    );
    // transitions_removed counts dead + agglomerated; here only agglomerated.
    assert_eq!(report.transitions_removed(), 1);
    assert!(report.dead_transitions.is_empty());
}

#[test]
fn test_pre_agglomeration_multiple_successors() {
    // t0 ->(1) p_mid, p_mid ->(1) t1, p_mid ->(1) t2
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_in"),
            place("p_mid"),
            place("p_out1"),
            place("p_out2"),
        ],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t2", vec![arc(1, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![1, 0, 0, 0],
    };

    let report = analyze(&net);
    assert_eq!(report.pre_agglomerations.len(), 1);
    assert_eq!(report.pre_agglomerations[0].successors.len(), 2);
}

#[test]
fn test_no_pre_agglomeration_nonzero_initial_tokens() {
    let net = PetriNet {
        name: None,
        places: vec![place("p_in"), place("p_mid"), place("p_out")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![1, 1, 0], // p_mid has initial tokens
    };

    let report = analyze(&net);
    assert!(report.pre_agglomerations.is_empty());
}

#[test]
fn test_no_pre_agglomeration_weight_not_one() {
    let net = PetriNet {
        name: None,
        places: vec![place("p_in"), place("p_mid"), place("p_out")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 2)]), // weight 2
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![1, 0, 0],
    };

    let report = analyze(&net);
    assert!(report.pre_agglomerations.is_empty());
}

#[test]
fn test_chained_pre_agglomeration_no_overlap() {
    // Chain: p0 ->t0-> p1 ->t1-> p2 ->t2-> p3
    // Both p1 and p2 are pre-agglomeration candidates. Without the
    // receiving-transition guard, t1 would be both the successor of p1's
    // agglomeration AND the source of p2's agglomeration. This creates a
    // broken transition (inputs referencing removed places) if both fire
    // in the same pass.
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t2", vec![arc(2, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![1, 0, 0, 0],
    };

    let report = analyze(&net);
    // At most one pre-agglomeration should be selected per pass to avoid
    // chaining. The second candidate must wait for the next iteration.
    assert_eq!(
        report.pre_agglomerations.len(),
        1,
        "chained pre-agglomerations must not both fire in one pass"
    );
}

#[test]
fn test_no_pre_agglomeration_multiple_producers() {
    // Both t0 and t2 produce into p_mid -> violates "single producer" condition.
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_in"),
            place("p_mid"),
            place("p_out"),
            place("p_in2"),
        ],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t2", vec![arc(3, 1)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![1, 0, 0, 1],
    };

    let report = analyze(&net);
    assert!(report.pre_agglomerations.is_empty());
}

// ---------------------------------------------------------------------------
// Post-agglomeration detection
// ---------------------------------------------------------------------------

#[test]
fn test_post_agglomeration_simple_chain() {
    // t0 ->(1) p_mid ->(1) t1 ->(1) p_out
    // t1 has exactly one input (p_mid), p_mid has exactly one consumer (t1).
    let net = PetriNet {
        name: None,
        places: vec![place("p_in"), place("p_mid"), place("p_out")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![1, 0, 0],
    };

    let report = analyze(&net);
    // In a simple 2-transition chain, both pre and post are candidates.
    // Pre-agglomeration gets priority (t0 as source), so post won't select
    // the same place.
    assert!(
        !report.pre_agglomerations.is_empty() || !report.post_agglomerations.is_empty(),
        "at least one agglomeration should be found"
    );
}

#[test]
fn test_post_agglomeration_multiple_predecessors() {
    // t0 ->(1) p_mid, t1 ->(1) p_mid, p_mid ->(1) t2
    // t2 has one input (p_mid), p_mid has one consumer (t2), two producers.
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
        ],
        initial_marking: vec![1, 1, 0, 0],
    };

    let report = analyze(&net);
    assert_eq!(report.post_agglomerations.len(), 1);
    assert_eq!(report.post_agglomerations[0].transition, TransitionIdx(2));
    assert_eq!(report.post_agglomerations[0].place, PlaceIdx(2));
    assert_eq!(report.post_agglomerations[0].predecessors.len(), 2);
}

#[test]
fn test_no_post_agglomeration_self_loop() {
    // t0 produces to p_mid and also consumes from p_mid -> self-loop.
    let net = PetriNet {
        name: None,
        places: vec![place("p_mid"), place("p_out")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(0, 1), arc(1, 1)])],
        initial_marking: vec![0, 0],
    };

    let report = analyze(&net);
    assert!(report.post_agglomerations.is_empty());
}

#[test]
fn test_no_post_agglomeration_nonzero_initial_tokens() {
    // t0 ->(1) p_mid ->(1) t1 ->(1) p_out, but p_mid has initial tokens.
    // Post-agg condition 3 requires zero initial tokens on the intermediate place.
    // p_mid has exactly one consumer (t1) so condition 2 is satisfied -> only
    // the nonzero initial token guard blocks.
    let net = PetriNet {
        name: None,
        places: vec![place("p_in"), place("p_mid"), place("p_out")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![1, 2, 0], // p_mid has initial tokens
    };

    let report = analyze(&net);
    assert!(
        report.post_agglomerations.is_empty(),
        "post-agg should be blocked by nonzero initial tokens on p_mid"
    );
}

#[test]
fn test_no_post_agglomeration_weight_not_one() {
    // t0 ->(2) p_mid ->(1) t1 ->(1) p_out
    // Producer arc weight is 2, violating condition 4 (every producer
    // must produce exactly 1 token).
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_in1"),
            place("p_in2"),
            place("p_mid"),
            place("p_out"),
        ],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(2, 2)]), // weight 2
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t2", vec![arc(2, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![1, 1, 0, 0],
    };

    let report = analyze(&net);
    assert!(
        report.post_agglomerations.is_empty(),
        "post-agg should be blocked by producer arc weight != 1"
    );
}

#[test]
fn test_no_post_agglomeration_multiple_consumers() {
    // t0 ->(1) p_mid, t1 ->(1) p_mid, p_mid ->(1) t2, p_mid ->(1) t3
    // p_mid has two consumers, violating condition 2.
    // Two producers ensure pre-agglomeration is impossible, so this test
    // cannot pass merely because pre-agglomeration wins the conflict.
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_in1"),
            place("p_in2"),
            place("p_mid"),
            place("p_out1"),
            place("p_out2"),
        ],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(2, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t2", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t3", vec![arc(2, 1)], vec![arc(4, 1)]),
        ],
        initial_marking: vec![1, 1, 0, 0, 0],
    };

    let report = analyze(&net);
    assert!(
        report.pre_agglomerations.is_empty(),
        "pre-agg should be blocked by multiple producers of p_mid"
    );
    assert!(
        report.post_agglomerations.is_empty(),
        "post-agg should be blocked by multiple consumers of p_mid"
    );
}

#[test]
fn test_no_post_agglomeration_output_input_overlap() {
    // t0 ->(1) p_mid, t1 ->(1) p_mid, p_mid ->(1) t2 -> p_overlap
    // All post-agg conditions hold except condition 6: t2's output overlaps
    // a predecessor input place, which would create a false self-loop after
    // merging.
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_in"),
            place("p_overlap"),
            place("p_mid"),
            place("p_out"),
        ],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(2, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t2", vec![arc(2, 1)], vec![arc(1, 1), arc(3, 1)]),
        ],
        initial_marking: vec![1, 1, 0, 0],
    };

    let report = analyze(&net);
    assert!(
        report.pre_agglomerations.is_empty(),
        "pre-agg should be blocked by multiple producers of p_mid"
    );
    assert!(
        report.post_agglomerations.is_empty(),
        "post-agg should be blocked by output/input overlap with a predecessor"
    );
}
