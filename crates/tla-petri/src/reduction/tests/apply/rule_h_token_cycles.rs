// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Tapaal Rule H Phase 1: token-cycle detection + place merging
//! + arc redirection + query protection, exercised directly against the
//! [`find_token_cycles`] + [`apply_token_cycles`] pair.
//!
//! Reference: Tapaal verifypn `Reducer.cpp:1316-1548` (`ReducebyRuleH`).
//!
//! Phase 1 is the detection + transform slice only. Fixpoint integration
//! (wiring Rule H into `reduce_iterative_structural_with_mode`) is Phase 2
//! and tracked separately under #4303.
//!
//! Note on inhibitor arcs: the Tapaal algorithm skips transitions/places
//! participating in inhibitor arcs (`Reducer.cpp:1325,1345-1346`). The
//! `tla-petri` data model does not yet support inhibitor arcs, so the
//! "inhibitor-blocks-cycle" case is vacuously satisfied. When inhibitor
//! arcs are added upstream, a matching test must be added here.

use crate::petri_net::{PetriNet, PlaceIdx};
use crate::reduction::{apply_token_cycles, find_token_cycles};

use super::super::support::{arc, place, trans};

/// Trivial 2-transition cycle:  p0 --t0--> p1 --t1--> p0.
///
/// Rule H collapses the two cycle places into one survivor (p0, lowest
/// index), drops both cycle transitions, and preserves the aggregate
/// marking on the survivor.
#[test]
fn test_rule_h_two_transition_cycle_merges_markings() {
    let mut net = PetriNet {
        name: Some("rule-h-two-cycle".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![2, 3],
    };

    let cycles = find_token_cycles(&net, &[], &[false, false]);
    assert_eq!(cycles.len(), 1, "exactly one cycle should be found");
    assert_eq!(cycles[0].survivor, PlaceIdx(0));

    let (places_removed, trans_removed) = apply_token_cycles(&mut net, &cycles);
    assert_eq!(places_removed, 1, "one cycle place absorbed");
    assert_eq!(trans_removed, 2, "both cycle transitions dropped");

    assert_eq!(net.num_places(), 1, "only survivor remains");
    assert_eq!(net.num_transitions(), 0, "no transitions remain");
    assert_eq!(
        net.initial_marking,
        vec![5],
        "aggregate marking (2+3) preserved on survivor"
    );
}

/// 3-transition cycle: p0 -> p1 -> p2 -> p0.
/// All three markings should sum onto the single survivor.
#[test]
fn test_rule_h_three_transition_cycle_sums_markings() {
    let mut net = PetriNet {
        name: Some("rule-h-three-cycle".to_string()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t2", vec![arc(2, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 2, 4],
    };

    let cycles = find_token_cycles(&net, &[], &[false, false, false]);
    assert_eq!(cycles.len(), 1);
    assert_eq!(cycles[0].transitions.len(), 3);

    let (places_removed, trans_removed) = apply_token_cycles(&mut net, &cycles);
    assert_eq!(places_removed, 2, "two non-survivor cycle places absorbed");
    assert_eq!(trans_removed, 3, "all three cycle transitions dropped");

    assert_eq!(net.num_places(), 1);
    assert_eq!(net.num_transitions(), 0);
    assert_eq!(
        net.initial_marking,
        vec![7],
        "markings 1+2+4 summed on survivor"
    );
}

/// No cycle in the net → detection returns empty → apply is a no-op and
/// every place/transition/arc is unchanged.
#[test]
fn test_rule_h_no_cycle_leaves_net_unchanged() {
    // Linear chain p0 -> p1 -> p2 — no back edge, no cycle.
    let mut net = PetriNet {
        name: Some("rule-h-chain".to_string()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![1, 0, 0],
    };
    let snapshot = net.clone();

    let cycles = find_token_cycles(&net, &[], &[false, false, false]);
    assert!(cycles.is_empty(), "linear chain has no cycle");

    let (places_removed, trans_removed) = apply_token_cycles(&mut net, &cycles);
    assert_eq!(places_removed, 0);
    assert_eq!(trans_removed, 0);
    assert_eq!(net.num_places(), snapshot.num_places());
    assert_eq!(net.num_transitions(), snapshot.num_transitions());
    assert_eq!(net.initial_marking, snapshot.initial_marking);
}

/// Query-protected cycle: marking a cycle place as protected forbids
/// Rule H from merging — detection returns empty, transform is a no-op,
/// net is unchanged.
#[test]
fn test_rule_h_query_protected_cycle_unchanged() {
    let mut net = PetriNet {
        name: Some("rule-h-protected".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };
    let snapshot = net.clone();

    // p1 is in the query — Rule H must not merge it away.
    let protected_places = vec![false, true];
    let cycles = find_token_cycles(&net, &[], &protected_places);
    assert!(
        cycles.is_empty(),
        "detection must reject any cycle touching a query-protected place"
    );

    apply_token_cycles(&mut net, &cycles);
    assert_eq!(net.num_places(), snapshot.num_places());
    assert_eq!(net.num_transitions(), snapshot.num_transitions());
    assert_eq!(net.initial_marking, snapshot.initial_marking);
}

/// Inhibitor-blocked cycle: the `tla-petri` data model has no inhibitor
/// arcs yet, so this case is documented here as vacuously satisfied.
///
/// Tapaal's `ReducebyRuleH` at `Reducer.cpp:1325,1345-1346` rejects any
/// transition whose `trans.inhib` flag is set, and any cycle whose places
/// have `place.inhib` set. When inhibitor-arc support lands in
/// `crate::petri_net`, this test must be extended to verify Rule H skips
/// such cycles. Tracked alongside Phase 2 work (#4303).
#[test]
fn test_rule_h_inhibitor_arcs_not_yet_supported_by_data_model() {
    // Placeholder that asserts the current data model has no inhibitor
    // surface. When `Arc`/`TransitionInfo`/`PlaceInfo` grow an `inhib`
    // flag, replace this with a real cycle-blocked-by-inhibitor test.
    //
    // Proof that no inhibitor surface exists: the `Arc` and
    // `TransitionInfo` non_exhaustive structs expose only `place/weight`
    // and `id/name/inputs/outputs`. If an `inhib` field is ever added,
    // construction of these literals below will break at compile time
    // and force the test to be updated.
    let _sentinel_arc = crate::petri_net::Arc {
        place: PlaceIdx(0),
        weight: 1,
    };
    let _sentinel_transition = crate::petri_net::TransitionInfo {
        id: "t".to_string(),
        name: None,
        inputs: vec![],
        outputs: vec![],
    };
}

/// Weight-2 arc breaks the "simple transition" invariant → Rule H skips
/// the cycle entirely. Tapaal requires both the pre-arc and post-arc of
/// every cycle transition to have weight 1 (`Reducer.cpp:1342-1343`).
#[test]
fn test_rule_h_weight_two_arc_breaks_cycle_detection() {
    let mut net = PetriNet {
        name: Some("rule-h-weight-two".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            // t0's output weight is 2 → not a simple transition.
            trans("t0", vec![arc(0, 1)], vec![arc(1, 2)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };
    let snapshot = net.clone();

    let cycles = find_token_cycles(&net, &[], &[false, false]);
    assert!(
        cycles.is_empty(),
        "weight-2 arc disqualifies the cycle transition from Rule H"
    );

    apply_token_cycles(&mut net, &cycles);
    assert_eq!(net.num_places(), snapshot.num_places());
    assert_eq!(net.num_transitions(), snapshot.num_transitions());
    assert_eq!(net.initial_marking, snapshot.initial_marking);
}
