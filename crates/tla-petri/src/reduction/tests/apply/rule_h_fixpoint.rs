// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fixpoint-integration tests for Tapaal Rule H (token cycle merging).
//!
//! These tests verify that `find_token_cycles` + the planning/materialize
//! wiring in `build_structural_plan_for_mode` correctly collapse a ring of
//! simple unit-weight transitions into a single survivor place under the
//! `Reachability` reduction mode, and that the rule is skipped under every
//! other mode.

use crate::petri_net::{PetriNet, PlaceIdx};
use crate::reduction::{reduce_iterative_structural_with_mode, ReductionMode};

use super::super::support::{arc, place, trans};

/// Two-place, two-transition ring:  p0 --t0--> p1 --t1--> p0.
///
/// Under `Reachability`, Rule H should:
///   - pick `p0` as survivor (lowest place idx), absorb `p1`,
///   - drop both `t0` and `t1`,
///   - merge the initial markings of `p0` and `p1` onto the survivor.
#[test]
fn test_rule_h_two_cycle_reachability_merges() {
    let net = PetriNet {
        name: Some("rule-h-two-cycle".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![2, 3],
    };

    let reduced = reduce_iterative_structural_with_mode(&net, &[], ReductionMode::Reachability)
        .expect("reduction should succeed");

    // Report should record the merge, cycle transitions, and survivor.
    assert_eq!(
        reduced.report.token_cycle_merges.len(),
        1,
        "exactly one token-cycle merge expected"
    );
    let merge = &reduced.report.token_cycle_merges[0];
    assert_eq!(merge.survivor, PlaceIdx(0));
    assert_eq!(merge.absorbed, vec![PlaceIdx(1)]);
    assert_eq!(merge.transitions.len(), 2);

    // Reduced net: survivor remains, duplicates removed, transitions dropped.
    assert_eq!(
        reduced.net.num_places(),
        1,
        "only survivor place should remain"
    );
    assert_eq!(
        reduced.net.num_transitions(),
        0,
        "both cycle transitions should be dropped"
    );

    // Aggregate marking preserved on the survivor.
    assert_eq!(reduced.net.initial_marking, vec![5]);

    // place_map: p0 -> survivor, p1 -> survivor (absorbed).
    let survivor_idx = reduced.place_map[0].expect("p0 maps to survivor");
    assert_eq!(reduced.place_map[1], Some(survivor_idx));

    // Expansion restores the original place count. Rule H maps every absorbed
    // cycle place to the survivor, so the expanded marking carries the
    // aggregate on both slots (individual per-place magnitudes are not
    // recoverable — this is why Rule H is reachability-only).
    let expanded = reduced
        .expand_marking(&reduced.net.initial_marking)
        .expect("expand should succeed");
    assert_eq!(expanded.len(), 2);
    assert_eq!(expanded[0], 5);
    assert_eq!(
        expanded[1], 5,
        "absorbed place mirrors survivor aggregate under Rule H"
    );
}

/// Three-place, three-transition ring:  p0 --t0--> p1 --t1--> p2 --t2--> p0.
#[test]
fn test_rule_h_three_cycle_reachability_merges() {
    let net = PetriNet {
        name: Some("rule-h-three-cycle".to_string()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t2", vec![arc(2, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 2, 4],
    };

    let reduced = reduce_iterative_structural_with_mode(&net, &[], ReductionMode::Reachability)
        .expect("reduction should succeed");

    assert_eq!(reduced.report.token_cycle_merges.len(), 1);
    let merge = &reduced.report.token_cycle_merges[0];
    assert_eq!(merge.survivor, PlaceIdx(0));
    assert_eq!(merge.absorbed.len(), 2);
    assert!(merge.absorbed.contains(&PlaceIdx(1)));
    assert!(merge.absorbed.contains(&PlaceIdx(2)));
    assert_eq!(merge.transitions.len(), 3);

    // Aggregate marking = 1 + 2 + 4 = 7.
    assert_eq!(reduced.net.initial_marking, vec![7]);
}

/// Rule H must NOT fire under any non-reachability mode, even when the net
/// has a clear reducible 2-cycle. Only the `token_cycle_merges` report slot
/// is inspected — other rules (LP-redundancy, duplicate-transition removal)
/// may still apply under the relaxed modes and are out of scope for this
/// gate test.
#[test]
fn test_rule_h_gated_off_for_non_reachability_modes() {
    let net = PetriNet {
        name: Some("rule-h-gate".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    for mode in [
        ReductionMode::NextFreeCTL,
        ReductionMode::CTLWithNext,
        ReductionMode::StutterInsensitiveLTL,
        ReductionMode::StutterSensitiveLTL,
    ] {
        let reduced = reduce_iterative_structural_with_mode(&net, &[], mode)
            .expect("reduction should succeed");
        assert!(
            reduced.report.token_cycle_merges.is_empty(),
            "Rule H must be gated off under {mode:?}"
        );
    }
}

/// A protected cycle place blocks the merge — the detection pass rejects
/// any cycle whose places appear in the self-loop-protected mask, and
/// `base_protected` flows into that mask through the fixpoint driver.
#[test]
fn test_rule_h_protected_place_blocks_merge() {
    let net = PetriNet {
        name: Some("rule-h-protected".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    // Protect p1 — it's in the cycle, so Rule H must refuse to fire.
    let protected = vec![false, true];
    let reduced =
        reduce_iterative_structural_with_mode(&net, &protected, ReductionMode::Reachability)
            .expect("reduction should succeed");

    assert!(
        reduced.report.token_cycle_merges.is_empty(),
        "Rule H must skip cycles touching a protected place"
    );
}

/// Two disjoint cycles compress independently under Reachability.
#[test]
fn test_rule_h_two_disjoint_cycles() {
    // Cycle A: p0 <-> p1 via t0, t1
    // Cycle B: p2 <-> p3 via t2, t3
    let net = PetriNet {
        name: Some("rule-h-two-cycles".to_string()),
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
            trans("t2", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t3", vec![arc(3, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![1, 1, 2, 2],
    };

    let reduced = reduce_iterative_structural_with_mode(&net, &[], ReductionMode::Reachability)
        .expect("reduction should succeed");

    assert_eq!(
        reduced.report.token_cycle_merges.len(),
        2,
        "two disjoint cycles must both be merged"
    );
    assert_eq!(reduced.net.num_places(), 2, "one survivor per cycle");
    assert_eq!(
        reduced.net.num_transitions(),
        0,
        "all four cycle transitions dropped"
    );

    // Survivors are p0 (cycle A) and p2 (cycle B), each carrying the sum
    // of its cycle's initial tokens.
    let mut initials = reduced.net.initial_marking.clone();
    initials.sort_unstable();
    assert_eq!(initials, vec![2, 4]);
}
