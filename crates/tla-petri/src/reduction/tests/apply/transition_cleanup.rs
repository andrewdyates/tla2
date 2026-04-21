// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};
use crate::reduction::{
    reduce, reduce_iterative, reduce_iterative_structural_one_safe,
    reduce_iterative_structural_query_with_protected, reduce_iterative_structural_with_protected,
    reduce_iterative_temporal_projection_candidate,
};

use super::super::support::{
    arc, parallel_token_elimination_net, place, token_elimination_net, trans,
};

#[test]
fn test_reduce_removes_self_loops() {
    // t_loop: p0 →(1) t_loop →(1) p0 (self-loop, removed)
    // t_real: p0 →(1) t_real →(1) p1 (real transition, kept)
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t_loop", vec![arc(0, 1)], vec![arc(0, 1)]),
            trans("t_real", vec![arc(0, 1)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![5, 0],
    };

    let reduced = reduce(&net);

    assert_eq!(reduced.net.num_transitions(), 1);
    assert_eq!(reduced.net.transitions[0].id, "t_real");
    assert_eq!(reduced.transition_map[0], None); // t_loop removed
    assert_eq!(reduced.transition_map[1], Some(TransitionIdx(0))); // t_real kept
    assert_eq!(reduced.report.self_loop_transitions, vec![TransitionIdx(0)]);
}

// ---------------------------------------------------------------------------
// Dominated transition removal (Tapaal Rule L)
// ---------------------------------------------------------------------------

/// Two transitions with identical net effect but different enabling thresholds:
/// the heavier one is dominated and should be removed.
///
/// Net:
///   p0(5) --(t_light,w=1)--> p1(0)   [light: needs 1 token from p0]
///   p0(5) --(t_heavy,w=3)--> p1(0)   [heavy: needs 3 tokens from p0, same effect]
///
/// Both transitions consume from p0 and produce to p1. t_heavy requires weight=3
/// from p0 while t_light requires weight=1. They have the same net effect
/// (delta = -1 on p0, +1 on p1 ... wait, actually different weights mean different
/// effects). Let me reconsider.
///
/// For dominated transition: same NET EFFECT, but different input weights.
/// Example: t_light: p0 --w=1--> t --w=1--> p1  (delta: p0=-1, p1=+1)
///          t_heavy: p0 --w=2--> t --w=2--> p1  (delta: p0=-2, p1=+2) -- DIFFERENT effect
///
/// Correct example: same net effect means same delta on every place.
///   t_light: consumes 1 from p0, produces 1 to p1 (delta: p0=-1, p1=+1)
///   t_heavy: consumes 2 from p0, 1 from p2; produces 1 to p0, 1 to p1
///            (delta: p0=-1, p1=+1, p2=-1) -- has EXTRA input from p2, same effect on p0/p1
///
/// Simplest correct example:
///   t_light: consumes 1 from p0, produces 1 to p1 (delta: p0=-1, p1=+1)
///   t_heavy: consumes 1 from p0 AND 1 from p2, produces 1 to p1 AND 1 to p2
///            (delta: p0=-1, p1=+1, p2=0 -- self-loop on p2)
///            input multiset: {p0:1, p2:1} vs {p0:1}
///            t_heavy is dominated because it needs p2 tokens too but same net effect.
#[test]
fn test_dominated_transition_is_removed() {
    // t_light: p0 --1--> t_light --1--> p1  (delta: p0=-1, p1=+1)
    // t_heavy: p0 --1--> t_heavy --1--> p1, p2 --1--> t_heavy --1--> p2
    //          (delta: p0=-1, p1=+1, p2=0)
    //          Same net effect as t_light, but also requires 1 token from p2.
    let net = PetriNet {
        name: Some("dominated".into()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            // t_light (index 0): p0 --1--> p1
            trans("t_light", vec![arc(0, 1)], vec![arc(1, 1)]),
            // t_heavy (index 1): p0 --1--> p1 AND p2 --1--> p2 (self-loop on p2)
            trans(
                "t_heavy",
                vec![arc(0, 1), arc(2, 1)],
                vec![arc(1, 1), arc(2, 1)],
            ),
        ],
        initial_marking: vec![5, 0, 1],
    };

    let reduced = reduce(&net);

    // t_heavy should be detected as dominated by t_light and removed.
    assert!(
        !reduced.report.dominated_transitions.is_empty(),
        "t_heavy should be dominated"
    );
    assert!(
        reduced
            .report
            .dominated_transitions
            .contains(&TransitionIdx(1)),
        "t_heavy (index 1) should be in the dominated list"
    );
    // The reduced net should have fewer transitions.
    assert!(
        reduced.net.num_transitions() < 2,
        "dominated transition should be removed"
    );
}

/// Same net effect, same input multiset = duplicate, NOT dominated.
/// Dominated requires STRICTLY more preconditions.
#[test]
fn test_identical_input_is_duplicate_not_dominated() {
    let net = PetriNet {
        name: Some("duplicate-not-dominated".into()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(0, 1)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![5, 0],
    };

    let reduced = reduce(&net);

    // These should be detected as duplicates, not dominated.
    assert!(
        reduced.report.dominated_transitions.is_empty(),
        "identical transitions are duplicates, not dominated"
    );
    assert!(
        !reduced.report.duplicate_transitions.is_empty(),
        "identical transitions should be duplicate"
    );
}

/// Different net effect = not dominated even if one has more inputs.
#[test]
fn test_different_net_effect_not_dominated() {
    let net = PetriNet {
        name: Some("different-effect".into()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            // t0: p0 --1--> p1 (delta: p0=-1, p1=+1)
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            // t1: p0 --1--> p2 (delta: p0=-1, p2=+1) -- different effect
            trans("t1", vec![arc(0, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![5, 0, 0],
    };

    let reduced = reduce(&net);

    assert!(
        reduced.report.dominated_transitions.is_empty(),
        "different net effects should not be dominated"
    );
}

/// Heavier input weight on same place = dominated.
///
/// t_light: consumes 2 from p0, produces 1 to p0, 1 to p1 (delta: p0=-1, p1=+1)
/// t_heavy: consumes 3 from p0, produces 2 to p0, 1 to p1 (delta: p0=-1, p1=+1)
/// Same delta, but t_heavy needs 3 tokens from p0 while t_light needs only 2.
#[test]
fn test_dominated_by_heavier_input_weight() {
    let net = PetriNet {
        name: Some("heavier-weight".into()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            // t_light: p0 --2--> t --{p0:1, p1:1}--> (delta: p0=-1, p1=+1)
            trans("t_light", vec![arc(0, 2)], vec![arc(0, 1), arc(1, 1)]),
            // t_heavy: p0 --3--> t --{p0:2, p1:1}--> (delta: p0=-1, p1=+1)
            trans("t_heavy", vec![arc(0, 3)], vec![arc(0, 2), arc(1, 1)]),
        ],
        initial_marking: vec![5, 0],
    };

    let reduced = reduce(&net);

    assert!(
        reduced
            .report
            .dominated_transitions
            .contains(&TransitionIdx(1)),
        "t_heavy should be dominated (needs 3 from p0, t_light needs 2)"
    );
}

/// Reduction fixpoint: removing a dominated transition can make places isolated.
///
/// p0(5) --(t_light)--> p1(0)
/// p0(5), p2(1) --(t_heavy)--> p1(0), p2(1)   [self-loop on p2]
///
/// After dominated-transition removal (t_heavy), p2 has no connected live
/// transitions. Structural re-reduction should detect p2 as isolated.
#[test]
fn test_dominated_removal_cascades_to_isolated_place() {
    let net = PetriNet {
        name: Some("cascade-isolated".into()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans("t_light", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans(
                "t_heavy",
                vec![arc(0, 1), arc(2, 1)],
                vec![arc(1, 1), arc(2, 1)],
            ),
        ],
        initial_marking: vec![5, 0, 1],
    };

    let reduced = reduce_iterative(&net).expect("reduction should succeed");

    // After iterative reduction: t_heavy dominated → removed.
    // p2 connects only to t_heavy → becomes isolated → removed.
    assert!(
        reduced.place_map[2].is_none(),
        "p2 should be removed (isolated after dominated transition removed)"
    );
}

// ---------------------------------------------------------------------------
// Rule K: Self-loop arc removal
// ---------------------------------------------------------------------------

/// A transition with one self-loop arc pair and real arcs should have the
/// self-loop pair stripped, keeping the transition alive with fewer arcs.
///
/// t0: p0 --1--> p1, p2 --1--> p2 (self-loop on p2)
/// t1: p1 --1--> p0 (gives p1 a consumer so it's not a source place)
/// After Rule K: t0 has self-loop arc on p2 stripped.
#[test]
fn test_self_loop_arc_pair_removed_from_transition() {
    let net = PetriNet {
        name: Some("rule-k-basic".into()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans("t0", vec![arc(0, 1), arc(2, 1)], vec![arc(1, 1), arc(2, 1)]),
            // t1 gives p1 a consumer so it's not removed as a source place.
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![5, 0, 3],
    };

    let reduced = reduce(&net);

    // The self-loop arc on p2 should be stripped from t0.
    assert!(
        !reduced.report.self_loop_arcs.is_empty(),
        "should detect self-loop arc pair on p2"
    );

    // Both transitions should survive.
    assert_eq!(
        reduced.net.num_transitions(),
        2,
        "both transitions should survive"
    );

    // After reducing, find t0 in the reduced net (mapped from original index 0).
    let t0_new_idx = reduced.transition_map[0].expect("t0 should survive");
    let t0 = &reduced.net.transitions[t0_new_idx.0 as usize];

    // t0 should only have input from p0 (self-loop arc on p2 stripped).
    assert_eq!(t0.inputs.len(), 1, "t0 should have 1 input (p0 only)");
    // t0 should only have output to p1 (self-loop arc on p2 stripped).
    assert_eq!(t0.outputs.len(), 1, "t0 should have 1 output (p1 only)");
}

#[test]
fn test_self_loop_arc_pair_removed_when_output_weight_is_split_across_arcs() {
    let net = PetriNet {
        name: Some("rule-k-split-output".into()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans(
                "t0",
                vec![arc(0, 2), arc(2, 1)],
                vec![arc(0, 1), arc(0, 1), arc(1, 1)],
            ),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t2", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![5, 0, 3],
    };

    let reduced = reduce(&net);

    assert_eq!(
        reduced.report.self_loop_arcs.len(),
        1,
        "split output arcs should still count as one matched Rule K pair"
    );
    let t0_new_idx = reduced.transition_map[0].expect("t0 should survive");
    let t0 = &reduced.net.transitions[t0_new_idx.0 as usize];
    assert_eq!(t0.inputs.len(), 1, "only the real p2 input should remain");
    assert_eq!(t0.outputs.len(), 1, "only the real p1 output should remain");
    assert_eq!(reduced.net.places[t0.inputs[0].place.0 as usize].id, "p2");
    assert_eq!(reduced.net.places[t0.outputs[0].place.0 as usize].id, "p1");
}

#[test]
fn test_self_loop_arc_pair_removed_when_input_weight_is_split_across_arcs() {
    let net = PetriNet {
        name: Some("rule-k-split-input".into()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans(
                "t0",
                vec![arc(0, 1), arc(0, 1), arc(2, 1)],
                vec![arc(0, 2), arc(1, 1)],
            ),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t2", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![5, 0, 3],
    };

    let reduced = reduce(&net);

    assert_eq!(
        reduced.report.self_loop_arcs.len(),
        1,
        "split input arcs should still count as one matched Rule K pair"
    );
    let t0_new_idx = reduced.transition_map[0].expect("t0 should survive");
    let t0 = &reduced.net.transitions[t0_new_idx.0 as usize];
    assert_eq!(t0.inputs.len(), 1, "only the real p2 input should remain");
    assert_eq!(t0.outputs.len(), 1, "only the real p1 output should remain");
    assert_eq!(reduced.net.places[t0.inputs[0].place.0 as usize].id, "p2");
    assert_eq!(reduced.net.places[t0.outputs[0].place.0 as usize].id, "p1");
}

/// A self-loop arc on a query-protected place should NOT be removed.
///
/// t0: p0 --1--> p1, p2 --1--> p2 (self-loop on p2)
/// t1: p1 --1--> p0
/// t2: p2 --1--> p0 (gives p2 a non-self-loop consumer, so it's not constant)
/// With p2 protected, the self-loop arc pair on p2 in t0 should be kept.
#[test]
fn test_self_loop_arc_on_protected_place_kept() {
    let net = PetriNet {
        name: Some("rule-k-protected".into()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans("t0", vec![arc(0, 1), arc(2, 1)], vec![arc(1, 1), arc(2, 1)]),
            // t1 gives p1 a consumer.
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
            // t2 gives p2 a net-negative consumer, making p2 non-constant.
            trans("t2", vec![arc(2, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![5, 0, 3],
    };

    // Protect p2 — the self-loop place.
    let protected = vec![false, false, true];
    let reduced = reduce_iterative_structural_with_protected(&net, &protected)
        .expect("reduction should succeed");

    // The self-loop arc on p2 should NOT be stripped because p2 is protected.
    assert!(
        reduced.report.self_loop_arcs.is_empty(),
        "self-loop arc on protected place should not be detected"
    );

    // p2 should survive (it's protected and non-constant).
    assert!(
        reduced.place_map[2].is_some(),
        "p2 should survive (protected)"
    );

    // t0 should retain both inputs (p0 and protected p2).
    let t0_new_idx = reduced.transition_map[0].expect("t0 should survive");
    let t0 = &reduced.net.transitions[t0_new_idx.0 as usize];
    assert_eq!(
        t0.inputs.len(),
        2,
        "t0 should retain both inputs (p0 and protected p2)"
    );
}

/// Removing a self-loop arc can make a place consumer-free (source place),
/// which should be removed in the next fixpoint iteration.
///
/// p0(5) --t0--> p1(0), with self-loop on p2(3)
/// After Rule K strips the self-loop, p2 has only a producer (from t0's output
/// that was paired with the input). Wait — that's wrong. The self-loop removes
/// BOTH input and output. So p2 has NO arcs after stripping → isolated.
#[test]
fn test_self_loop_arc_removal_cascades_to_isolated_place() {
    let net = PetriNet {
        name: Some("rule-k-cascade".into()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![trans(
            "t0",
            vec![arc(0, 1), arc(2, 1)],
            vec![arc(1, 1), arc(2, 1)],
        )],
        initial_marking: vec![5, 0, 3],
    };

    let reduced = reduce_iterative(&net).expect("reduction should succeed");

    // After iterative reduction: self-loop arc stripped from t0.
    // p2 loses all arcs → becomes isolated → removed in next pass.
    assert!(
        reduced.place_map[2].is_none(),
        "p2 should be removed (isolated after self-loop arc stripping)"
    );
}

/// A transition where ALL arcs are self-loops should be handled by Rule G
/// (self-loop transition removal), NOT Rule K (individual arc removal).
#[test]
fn test_full_self_loop_transition_handled_by_rule_g_not_k() {
    let net = PetriNet {
        name: Some("rule-g-not-k".into()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            // t0: full self-loop (both arcs cancel)
            trans("t0", vec![arc(0, 1), arc(1, 2)], vec![arc(0, 1), arc(1, 2)]),
            // t1: non-self-loop (real transition)
            trans("t1", vec![arc(0, 1)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![5, 0],
    };

    let reduced = reduce(&net);

    // t0 should be caught by Rule G (self-loop transition), not Rule K.
    assert!(
        reduced
            .report
            .self_loop_transitions
            .contains(&TransitionIdx(0)),
        "t0 should be a self-loop transition (Rule G)"
    );
    assert!(
        reduced.report.self_loop_arcs.is_empty(),
        "no individual self-loop arcs should be reported (Rule G handles t0)"
    );
}

// ---------------------------------------------------------------------------
// Rule N: Never-disabling arc removal
// ---------------------------------------------------------------------------

/// Rule N is only surfaced in the reduced report when another sound rule
/// already removes the place from the reduced net.
#[test]
fn test_never_disabling_arc_reported_when_redundant_place_is_removed() {
    let net = PetriNet {
        name: Some("rule-n-basic".into()),
        places: vec![place("p_cap"), place("p_use"), place("p_res")],
        transitions: vec![
            trans("t_use", vec![arc(0, 1), arc(2, 1)], vec![arc(1, 1)]),
            trans("t_release", vec![arc(1, 1)], vec![arc(0, 1), arc(2, 1)]),
        ],
        initial_marking: vec![5, 0, 3],
    };

    let reduced = reduce(&net);

    assert_eq!(reduced.report.never_disabling_arcs.len(), 1);
    assert_eq!(
        reduced.report.never_disabling_arcs[0].transition,
        TransitionIdx(0)
    );
    assert_eq!(reduced.report.never_disabling_arcs[0].place, PlaceIdx(0));
    assert_eq!(
        reduced.place_map[0], None,
        "Rule N is only reported here because p_cap is removed soundly as redundant"
    );

    let use_idx = reduced.transition_map[0].expect("t_use should survive");
    let t_use = &reduced.net.transitions[use_idx.0 as usize];
    assert_eq!(
        t_use
            .inputs
            .iter()
            .map(|arc| arc.weight)
            .collect::<Vec<_>>(),
        vec![1],
        "p_cap disappears from t_use because the redundant place is removed"
    );
}

/// When P-invariants cannot prove a positive lower bound, the input arc stays.
#[test]
fn test_never_disabling_arc_kept_without_structural_lower_bound() {
    let net = PetriNet {
        name: Some("rule-n-kept".into()),
        places: vec![place("p_free"), place("p_busy")],
        transitions: vec![
            trans("t_enter", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_exit", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    let reduced = reduce(&net);

    assert!(
        reduced.report.never_disabling_arcs.is_empty(),
        "mutex arcs should stay without a positive lower-bound proof"
    );
    let t_enter_idx = reduced.transition_map[0].expect("t_enter should survive");
    let t_enter = &reduced.net.transitions[t_enter_idx.0 as usize];
    assert_eq!(
        t_enter.inputs.len(),
        1,
        "the original input arc must remain"
    );
}

#[test]
fn test_query_relevant_reduction_removes_token_eliminated_place() {
    let net = token_elimination_net();

    let reduced = reduce_iterative_structural_query_with_protected(&net, &[false; 4])
        .expect("query-relevant reduction should succeed");

    assert_eq!(reduced.report.source_places, vec![PlaceIdx(3)]);
    assert_eq!(reduced.report.token_eliminated_places, vec![PlaceIdx(0)]);
    assert_eq!(reduced.place_map[0], None);

    let fwd_idx = reduced.transition_map[0].expect("t_fwd should survive");
    let t_fwd = &reduced.net.transitions[fwd_idx.0 as usize];
    assert_eq!(
        t_fwd.inputs.len(),
        1,
        "query-only token elimination should drop the p_cap input from t_fwd"
    );
}

#[test]
fn test_query_relevant_reduction_keeps_protected_token_eliminated_place() {
    let net = token_elimination_net();

    let reduced =
        reduce_iterative_structural_query_with_protected(&net, &[true, false, false, false])
            .expect("query-relevant reduction should succeed");

    assert!(reduced.report.token_eliminated_places.is_empty());
    assert!(
        reduced.place_map[0].is_some(),
        "protected place must survive query-only token elimination"
    );
}

#[test]
fn test_exact_marking_reduction_does_not_apply_token_elimination() {
    let net = token_elimination_net();

    let reduced = reduce_iterative_structural_with_protected(&net, &[false; 4]).expect("reduce");

    assert_eq!(reduced.report.source_places, vec![PlaceIdx(3)]);
    // Token elimination must not fire in exact-marking mode — it is gated to
    // QueryRelevantOnly semantics only.  (p_cap may still be removed by LP
    // redundancy, which is fine for exact-marking; the key invariant is that
    // the token_eliminated_places list stays empty.)
    assert!(reduced.report.token_eliminated_places.is_empty());
}

#[test]
fn test_query_relevant_reduction_keeps_parallel_place_on_rule_b_lane() {
    let net = parallel_token_elimination_net();

    let reduced = reduce_iterative_structural_query_with_protected(&net, &[false; 5])
        .expect("query-relevant reduction should succeed");

    let canonical = reduced.place_map[0].expect("parallel canonical must survive");
    assert_eq!(
        reduced.place_map[1],
        Some(canonical),
        "parallel duplicate should stay on the exact Rule B aliasing path"
    );
    assert!(
        reduced.report.token_eliminated_places.is_empty(),
        "query-only token elimination must not preempt exact parallel-place reduction"
    );
}

// ---------------------------------------------------------------------------
// Rule F: Non-decreasing place removal (end-to-end)
// ---------------------------------------------------------------------------

#[test]
fn test_reduce_removes_non_decreasing_place() {
    // p_acc: t0 consumes 1 and produces 2, t1 produces 1 more.
    // Initial marking 3 >= max_consume 1 → non-decreasing, removed.
    let net = PetriNet {
        name: Some("rule-f-e2e".into()),
        places: vec![place("p_src"), place("p_acc"), place("p_sink")],
        transitions: vec![
            trans("t0", vec![arc(0, 1), arc(1, 1)], vec![arc(1, 2), arc(2, 1)]),
            trans("t1", vec![arc(0, 1)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![5, 3, 0],
    };

    let reduced = reduce(&net);

    assert!(
        reduced.place_map[1].is_none(),
        "p_acc should be removed by Rule F"
    );
    assert!(
        !reduced.report.non_decreasing_places.is_empty(),
        "report should record non-decreasing places"
    );
}

#[test]
fn test_temporal_projection_candidate_skips_non_decreasing_place_removal() {
    let net = PetriNet {
        name: Some("rule-f-candidate".into()),
        places: vec![place("p_src"), place("p_acc"), place("p_sink")],
        transitions: vec![
            trans("t0", vec![arc(0, 1), arc(1, 1)], vec![arc(1, 2), arc(2, 1)]),
            trans("t1", vec![arc(0, 1)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![5, 3, 0],
    };

    let reduced = reduce_iterative_temporal_projection_candidate(&net).expect("reduce");

    assert!(
        reduced.report.non_decreasing_places.is_empty(),
        "test-only temporal candidate must not inherit Rule F removals"
    );
    assert_eq!(
        reduced.place_map[1],
        Some(PlaceIdx(1)),
        "non-decreasing accumulator should survive the temporal candidate lane"
    );
}

#[test]
fn test_one_safe_reduction_skips_non_decreasing_place_removal() {
    let net = PetriNet {
        name: Some("rule-f-one-safe".into()),
        places: vec![place("p_src"), place("p_acc"), place("p_sink")],
        transitions: vec![
            trans("t0", vec![arc(0, 1), arc(1, 1)], vec![arc(1, 2), arc(2, 1)]),
            trans("t1", vec![arc(0, 1)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![5, 3, 0],
    };

    let reduced = reduce_iterative_structural_one_safe(&net).expect("reduce");

    assert!(
        reduced.report.non_decreasing_places.is_empty(),
        "OneSafe reduction must not inherit Rule F removals"
    );
}

#[test]
fn test_one_safe_reduction_skips_source_place_removal() {
    let net = PetriNet {
        name: Some("source-place-one-safe".into()),
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

    let reduced = reduce_iterative_structural_one_safe(&net).expect("reduce");

    assert!(
        reduced.report.source_places.is_empty(),
        "OneSafe reduction must not inherit source-place removals"
    );
    assert!(
        reduced.place_map[1].is_some(),
        "source accumulator should survive the OneSafe lane"
    );
}

#[test]
fn test_one_safe_reduction_skips_agglomeration() {
    let net = PetriNet {
        name: Some("agglomeration-one-safe".into()),
        places: vec![place("p_in"), place("p_mid"), place("p_out")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![1, 0, 0],
    };

    let reduced = reduce_iterative_structural_one_safe(&net).expect("reduce");

    assert!(
        reduced.report.pre_agglomerations.is_empty(),
        "OneSafe reduction must not pre-agglomerate intermediate places"
    );
    assert!(
        reduced.report.post_agglomerations.is_empty(),
        "OneSafe reduction must not post-agglomerate intermediate places"
    );
    assert!(
        reduced.place_map[1].is_some(),
        "agglomerated middle place must survive the OneSafe lane"
    );
}

// ---------------------------------------------------------------------------
// Rule B: Parallel place removal (end-to-end)
// ---------------------------------------------------------------------------

#[test]
fn test_reduce_removes_parallel_place() {
    // p0 and p1 have identical arcs to 3 transitions. This net avoids simple
    // P-invariant reconstruction so only Rule B fires on the parallel pair.
    // t0 consumes from {p0, p1, p2}, produces to {p3}.
    // t1 consumes from {p3, p4}, produces to {p0, p1}.
    // t2 consumes from {p3}, produces to {p2, p4}.
    let net = PetriNet {
        name: Some("rule-b-e2e".into()),
        places: vec![
            place("p0"),
            place("p1"),
            place("p2"),
            place("p3"),
            place("p4"),
        ],
        transitions: vec![
            trans("t0", vec![arc(0, 1), arc(1, 1), arc(2, 1)], vec![arc(3, 1)]),
            trans("t1", vec![arc(3, 1), arc(4, 1)], vec![arc(0, 1), arc(1, 1)]),
            trans("t2", vec![arc(3, 1)], vec![arc(2, 1), arc(4, 1)]),
        ],
        initial_marking: vec![2, 2, 3, 0, 1],
    };

    let reduced = reduce(&net);

    // p0 (canonical) must survive and get a new index.
    let canonical = reduced.place_map[0].expect("p0 (canonical) should survive in the reduced net");
    // p1 (duplicate) must alias to the canonical's new index.
    assert_eq!(
        reduced.place_map[1],
        Some(canonical),
        "parallel duplicate should alias to the canonical place"
    );
    // The reduced net should have one fewer place (5 - 1 = 4).
    assert_eq!(
        reduced.net.num_places(),
        4,
        "one parallel duplicate removed, four places survive"
    );
    assert!(
        !reduced.report.parallel_places.is_empty(),
        "report should record parallel places"
    );
}

#[test]
fn test_temporal_projection_candidate_skips_parallel_place_removal() {
    let net = PetriNet {
        name: Some("rule-b-candidate".into()),
        places: vec![
            place("p0"),
            place("p1"),
            place("p2"),
            place("p3"),
            place("p4"),
        ],
        transitions: vec![
            trans("t0", vec![arc(0, 1), arc(1, 1), arc(2, 1)], vec![arc(3, 1)]),
            trans("t1", vec![arc(3, 1), arc(4, 1)], vec![arc(0, 1), arc(1, 1)]),
            trans("t2", vec![arc(3, 1)], vec![arc(2, 1), arc(4, 1)]),
        ],
        initial_marking: vec![2, 2, 3, 0, 1],
    };

    let reduced = reduce_iterative_temporal_projection_candidate(&net).expect("reduce");

    assert!(
        reduced.report.parallel_places.is_empty(),
        "test-only temporal candidate must not inherit Rule B merges"
    );
    assert_eq!(
        reduced.place_map[0],
        Some(PlaceIdx(0)),
        "canonical parallel place should stay at its own index in the candidate lane"
    );
    assert_eq!(
        reduced.place_map[1],
        Some(PlaceIdx(1)),
        "parallel duplicate should survive instead of aliasing to the canonical place"
    );
    assert_eq!(
        reduced.net.num_places(),
        5,
        "candidate lane should keep the full parallel-place state vector"
    );
}
