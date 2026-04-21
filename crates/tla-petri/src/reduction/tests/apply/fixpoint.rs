// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::petri_net::PetriNet;
use crate::reduction::{
    apply_query_guarded_prefire, reduce_iterative_structural, reduce_query_guarded,
};

use super::super::support::{arc, place, trans};

/// Fixpoint produces a smaller net than one-shot prefire by re-running
/// structural reduction after marking changes.
///
/// Net:
///   p_src(5) --(t_pump,w=1)--> p_dst(0)   [sole consumer of p_src]
///   p_qa(1)  --(t_q)--> p_qb(0)           [query places, protected]
///   p_qb(0)  --(t_back)--> p_qa(1)        [cycle keeps query places alive]
///
/// After initial structural reduction: p_dst is LP-redundant (never constrains
/// a transition), removed. Net: p_src, p_qa, p_qb.
///
/// One-shot prefire: t_pump fires 5 times → p_src=0. Net still has 3 places.
/// Fixpoint: prefire fires t_pump → p_src=0. Re-reduce: p_src=0 with no
/// producer → dead. t_pump dead (input gone). Removed. Net: p_qa, p_qb (2).
#[test]
fn test_query_guarded_fixpoint_reduces_more_than_one_shot() {
    let net = PetriNet {
        name: Some("fixpoint-vs-one-shot".into()),
        places: vec![
            place("p_src"), // 0: initial=5
            place("p_dst"), // 1: initial=0 (LP-redundant, removed by structural)
            place("p_qa"),  // 2: initial=1, protected
            place("p_qb"),  // 3: initial=0, protected
        ],
        transitions: vec![
            trans("t_pump", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_q", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t_back", vec![arc(3, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![5, 0, 1, 0],
    };

    // One-shot: structural reduce, then a single prefire.
    let mut one_shot = reduce_iterative_structural(&net).expect("structural should succeed");
    let one_shot_places_after_structural = one_shot.net.num_places();
    // Build protected mask for the structurally-reduced net.
    let mut one_shot_prot = vec![false; one_shot.net.num_places()];
    if let Some(idx) = one_shot.place_map[2] {
        one_shot_prot[idx.0 as usize] = true;
    }
    if let Some(idx) = one_shot.place_map[3] {
        one_shot_prot[idx.0 as usize] = true;
    }
    let _changed =
        apply_query_guarded_prefire(&mut one_shot, &one_shot_prot).expect("prefire should succeed");
    // After one-shot prefire: marking changed but structure unchanged.
    assert_eq!(
        one_shot.net.num_places(),
        one_shot_places_after_structural,
        "one-shot prefire should not change net structure"
    );

    // Fixpoint: structural reduce, then prefire + re-reduce loop.
    let reduced_struct = reduce_iterative_structural(&net).expect("structural should succeed");
    let fixpoint = reduce_query_guarded(reduced_struct, |r| {
        let mut prot = vec![false; r.net.num_places()];
        if let Some(idx) = r.place_map[2] {
            prot[idx.0 as usize] = true;
        }
        if let Some(idx) = r.place_map[3] {
            prot[idx.0 as usize] = true;
        }
        Some(prot)
    })
    .expect("fixpoint should succeed");

    // Fixpoint should remove dead p_src and t_pump that one-shot leaves.
    assert!(
        fixpoint.net.num_places() < one_shot.net.num_places(),
        "fixpoint ({} places) should be smaller than one-shot ({} places)",
        fixpoint.net.num_places(),
        one_shot.net.num_places(),
    );

    // Query places must survive.
    assert!(fixpoint.place_map[2].is_some(), "p_qa must survive");
    assert!(fixpoint.place_map[3].is_some(), "p_qb must survive");
}

/// After fixpoint, `place_map` and `expand_marking` correctly reference
/// original-net indices through the composed reduction.
///
/// Uses the same net as `test_query_guarded_fixpoint_reduces_more_than_one_shot`
/// and verifies that the final ReducedNet can expand a marking back to
/// original-net dimensions.
#[test]
fn test_query_guarded_fixpoint_compose_preserves_original_indices() {
    let net = PetriNet {
        name: Some("compose-check".into()),
        places: vec![
            place("p_src"), // 0: initial=5
            place("p_dst"), // 1: initial=0 (LP-redundant)
            place("p_qa"),  // 2: initial=1, protected
            place("p_qb"),  // 3: initial=0, protected
        ],
        transitions: vec![
            trans("t_pump", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_q", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t_back", vec![arc(3, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![5, 0, 1, 0],
    };

    let reduced_struct = reduce_iterative_structural(&net).expect("structural should succeed");
    let fixpoint = reduce_query_guarded(reduced_struct, |r| {
        let mut prot = vec![false; r.net.num_places()];
        if let Some(idx) = r.place_map[2] {
            prot[idx.0 as usize] = true;
        }
        if let Some(idx) = r.place_map[3] {
            prot[idx.0 as usize] = true;
        }
        Some(prot)
    })
    .expect("fixpoint should succeed");

    // place_map should have 4 entries (one per original place).
    assert_eq!(fixpoint.place_map.len(), 4);
    // p_src (0) and p_dst (1) should be eliminated.
    assert!(fixpoint.place_map[0].is_none(), "p_src should be removed");
    assert!(fixpoint.place_map[1].is_none(), "p_dst should be removed");
    // p_qa (2) and p_qb (3) should survive.
    assert!(fixpoint.place_map[2].is_some(), "p_qa must survive");
    assert!(fixpoint.place_map[3].is_some(), "p_qb must survive");

    // Marking expansion should recover a 4-element original-net marking.
    let expanded = fixpoint
        .expand_marking(&fixpoint.net.initial_marking)
        .expect("marking expansion should succeed");
    assert_eq!(expanded.len(), 4);
    // p_qa should have its initial token.
    assert_eq!(expanded[2], 1, "p_qa should have 1 token");
    // p_qb starts at 0.
    assert_eq!(expanded[3], 0, "p_qb should have 0 tokens");
}

/// Protected places must remain untouched through the fixpoint.
///
/// Uses a mutex net (cycle) that resists structural reduction, then
/// protects all places so prefire cannot fire.
#[test]
fn test_query_guarded_fixpoint_protected_places_unchanged() {
    // Mutex net: p0(1)→t0→p1(0)→t1→p0. Both places constrain their
    // respective transitions. No LP-redundancy, no agglomeration.
    let net = PetriNet {
        name: Some("all-protected".into()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t_enter", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_exit", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    let reduced_struct = reduce_iterative_structural(&net).expect("structural should succeed");
    assert_eq!(
        reduced_struct.net.num_places(),
        2,
        "mutex net should resist structural reduction"
    );
    let original_marking = reduced_struct.net.initial_marking.clone();

    let fixpoint = reduce_query_guarded(reduced_struct, |r| Some(vec![true; r.net.num_places()]))
        .expect("fixpoint should succeed");

    // Nothing should change: all places protected → no prefire → no new reductions.
    assert_eq!(fixpoint.net.initial_marking, original_marking);
    assert_eq!(fixpoint.net.num_places(), 2);
    assert_eq!(fixpoint.net.num_transitions(), 2);
}

/// Callback returning None skips prefire entirely.
#[test]
fn test_query_guarded_fixpoint_none_callback_is_identity() {
    let net = PetriNet {
        name: Some("none-callback".into()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![5, 0],
    };

    let reduced_struct = reduce_iterative_structural(&net).expect("structural should succeed");
    let before_places = reduced_struct.net.num_places();
    let before_marking = reduced_struct.net.initial_marking.clone();

    let fixpoint = reduce_query_guarded(reduced_struct, |_| None).expect("fixpoint should succeed");

    assert_eq!(fixpoint.net.num_places(), before_places);
    assert_eq!(fixpoint.net.initial_marking, before_marking);
}
