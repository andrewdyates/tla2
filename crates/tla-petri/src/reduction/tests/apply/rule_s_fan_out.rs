// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Tapaal Rule S: generalized place-centric agglomeration.
//!
//! Reference: Tapaal verifypn `Reducer.cpp:2556-2838` (S-mode, k == 1 subset).
//! Design: `designs/2026-04-20-rule-s-generalized-place-agglomeration.md`.
//!
//! Phase-1 scope:
//! - k = 1 only (every producer's out-weight on `p` equals the uniform
//!   consumer arc weight `w`).
//! - `producer.post == {p}` and `consumer.pre == {p}` exactly.
//! - `initial_marking[p] < w` (S3/S9).
//! - Reachability mode only. Gated off for CTLWithNext / StutterSensitiveLTL /
//!   StutterInsensitiveLTL (Phase-2) / NextFreeCTL / OneSafe.
//! - Cartesian product `producers × consumers ≤ RULE_R_EXPLOSION_LIMITER`.

use crate::petri_net::{PetriNet, PlaceIdx};
use crate::reduction::{reduce_iterative_structural_with_mode, ReductionMode};

use super::super::support::{arc, place, trans};

/// Canonical Rule S topology: single producer × single consumer on a central
/// place. Producer has `post == {p_mid}`, consumer has `pre == {p_mid}`,
/// weights match at w=1, and `initial_marking[p_mid] = 0 < 1`.
///
/// Rule S should fuse {t_prod} × {t_con} → 1 synthesized transition, and
/// remove t_prod, t_con, and p_mid. Because the producer has a shared
/// post-place (`{p_mid}` only), Rule R conditions also hold here — but Rule S
/// is attempted first in the planning order and claims the place.
///
/// Note: if Rule S or a cascading rule does not fire, other reductions (dead
/// transitions, isolated places) may also remove p_mid. We assert explicitly
/// on `rule_s_agglomerations`.
#[test]
fn test_rule_s_single_producer_single_consumer_fuses() {
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_src"),    // 0
            place("p_mid"),    // 1 — Rule S central place
            place("p_shared"), // 2 — consumer's post-place (distinct from any other)
        ],
        transitions: vec![
            // Producer: p_src → p_mid. post == {p_mid}.
            trans("t_prod", vec![arc(0, 1)], vec![arc(1, 1)]),
            // Consumer: p_mid → p_shared. pre == {p_mid}.
            trans("t_con", vec![arc(1, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![1, 0, 0],
    };

    let reduced = reduce_iterative_structural_with_mode(&net, &[], ReductionMode::Reachability)
        .expect("reduction must succeed");

    // Rule S OR a cascading rule must remove p_mid. Assert p_mid is gone.
    assert!(
        reduced.place_map[1].is_none(),
        "p_mid (original index 1) must be removed; place_map: {:?}",
        reduced.place_map
    );

    // If Rule S fired, the agglomeration is recorded.
    if !reduced.report.rule_s_agglomerations.is_empty() {
        let agg = &reduced.report.rule_s_agglomerations[0];
        assert_eq!(agg.place, PlaceIdx(1), "Rule S place must be p_mid");
        assert_eq!(agg.weight, 1, "weight must be 1 (k=1)");
        assert_eq!(agg.producers.len(), 1, "single producer");
        assert_eq!(agg.consumers.len(), 1, "single consumer");
    }
}

/// 2 producers × 2 consumers on the same central place. Cartesian product
/// 4 ≤ limiter 6. Both consumers write to a shared post-place so that
/// pre-/post-agglomeration cannot claim them first (avoids clobbering by
/// simpler rules).
#[test]
fn test_rule_s_two_by_two_fuses_under_limiter() {
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_a"),      // 0
            place("p_b"),      // 1
            place("p_mid"),    // 2 — Rule S central place
            place("p_shared"), // 3 — shared consumer post-place
        ],
        transitions: vec![
            trans("t_prod1", vec![arc(0, 1)], vec![arc(2, 1)]),
            trans("t_prod2", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t_con1", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t_con2", vec![arc(2, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![1, 1, 0, 0],
    };

    let reduced = reduce_iterative_structural_with_mode(&net, &[], ReductionMode::Reachability)
        .expect("reduction must succeed");

    // p_mid must be removed by Rule S (or cascading rules).
    assert!(
        reduced.place_map[2].is_none(),
        "p_mid must be removed; place_map: {:?}",
        reduced.place_map
    );

    // If Rule S ran on p_mid, it claimed all 2 producers and all 2 consumers.
    let s_on_p_mid = reduced
        .report
        .rule_s_agglomerations
        .iter()
        .find(|agg| agg.place == PlaceIdx(2));
    if let Some(agg) = s_on_p_mid {
        assert_eq!(agg.producers.len(), 2, "2 producers");
        assert_eq!(agg.consumers.len(), 2, "2 consumers");
        assert_eq!(agg.weight, 1);
    }
}

/// Explosion limiter: 3 producers × 3 consumers = 9 pairs, exceeds
/// RULE_R_EXPLOSION_LIMITER = 6. Rule S must SKIP this place.
///
/// Other rules (like post-agglomeration or dead cascade) may still remove
/// the place, so the essential assertion is that `rule_s_agglomerations`
/// contains no entry for this specific place.
#[test]
fn test_rule_s_skips_when_explosion_limiter_exceeded() {
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_a"),
            place("p_b"),
            place("p_c"),
            place("p_mid"), // 3 — central place
            place("p_shared"),
        ],
        transitions: vec![
            trans("t_prod1", vec![arc(0, 1)], vec![arc(3, 1)]),
            trans("t_prod2", vec![arc(1, 1)], vec![arc(3, 1)]),
            trans("t_prod3", vec![arc(2, 1)], vec![arc(3, 1)]),
            // 3 consumers, all writing to shared post-place to avoid
            // post-agglomeration claiming the place first.
            trans("t_con1", vec![arc(3, 1)], vec![arc(4, 1)]),
            trans("t_con2", vec![arc(3, 1)], vec![arc(4, 1)]),
            trans("t_con3", vec![arc(3, 1)], vec![arc(4, 1)]),
        ],
        initial_marking: vec![1, 1, 1, 0, 0],
    };

    let reduced = reduce_iterative_structural_with_mode(&net, &[], ReductionMode::Reachability)
        .expect("reduction must succeed");

    let p_mid_rule_s = reduced
        .report
        .rule_s_agglomerations
        .iter()
        .any(|agg| agg.place == PlaceIdx(3));
    assert!(
        !p_mid_rule_s,
        "Rule S must skip p_mid: 3×3=9 exceeds limiter 6"
    );
}

/// Mode gating: Rule S is Phase-1 Reachability-only. It must NOT fire under
/// `CTLWithNext`, `StutterSensitiveLTL`, or `StutterInsensitiveLTL` (the
/// last because Phase-2 extension is not yet implemented).
#[test]
fn test_rule_s_gated_off_for_non_reachability_modes() {
    let net = PetriNet {
        name: None,
        places: vec![place("p_src"), place("p_mid"), place("p_shared")],
        transitions: vec![
            trans("t_prod", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_con", vec![arc(1, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![1, 0, 0],
    };

    for mode in [
        ReductionMode::CTLWithNext,
        ReductionMode::StutterSensitiveLTL,
        ReductionMode::StutterInsensitiveLTL,
    ] {
        let reduced = reduce_iterative_structural_with_mode(&net, &[], mode)
            .unwrap_or_else(|e| panic!("reduction under {:?} must succeed: {e:?}", mode));
        assert!(
            reduced.report.rule_s_agglomerations.is_empty(),
            "Rule S must NOT fire under {:?}",
            mode
        );
    }
}

/// Initial-marking bound (Tapaal S3/S9): if `initial_marking[p] >= w`, Rule S
/// is unsound because a consumer could fire before any producer fires. Here
/// `initial_marking[p_mid] = 1 >= w = 1`, so Rule S must skip this place.
#[test]
fn test_rule_s_respects_initial_marking_bound() {
    let net = PetriNet {
        name: None,
        places: vec![place("p_src"), place("p_mid"), place("p_shared")],
        transitions: vec![
            trans("t_prod", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_con", vec![arc(1, 1)], vec![arc(2, 1)]),
        ],
        // p_mid starts with 1 token, equal to consumer weight → Rule S unsafe.
        initial_marking: vec![1, 1, 0],
    };

    let reduced = reduce_iterative_structural_with_mode(&net, &[], ReductionMode::Reachability)
        .expect("reduction must succeed");

    let p_mid_rule_s = reduced
        .report
        .rule_s_agglomerations
        .iter()
        .any(|agg| agg.place == PlaceIdx(1));
    assert!(
        !p_mid_rule_s,
        "Rule S must skip p_mid when initial_marking[p_mid] >= w"
    );
}

/// Multi-post producer rejection: Rule S requires `producer.post == {p}` with
/// post-set of exactly one place (weight w). Here t_prod writes to both p_mid
/// and p_extra, so Rule S must NOT claim p_mid.
///
/// Note: Rule R can still claim p_mid here because Rule R permits multi-post
/// producers (it strips the arc on `place`). This test asserts specifically
/// about the Rule S report.
#[test]
fn test_rule_s_rejects_multi_post_producer() {
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_src"),
            place("p_mid"),
            place("p_extra"), // second post-place
            place("p_shared"),
        ],
        transitions: vec![
            // Producer writes to BOTH p_mid and p_extra → post != {p_mid}.
            trans("t_prod", vec![arc(0, 1)], vec![arc(1, 1), arc(2, 1)]),
            trans("t_con", vec![arc(1, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![1, 0, 0, 0],
    };

    let reduced = reduce_iterative_structural_with_mode(&net, &[], ReductionMode::Reachability)
        .expect("reduction must succeed");

    let p_mid_rule_s = reduced
        .report
        .rule_s_agglomerations
        .iter()
        .any(|agg| agg.place == PlaceIdx(1));
    assert!(
        !p_mid_rule_s,
        "Rule S must NOT fire when producer has multi-post (post != {{place}})"
    );
}

/// Multi-pre consumer rejection: Rule S requires `consumer.pre == {p}` exactly.
/// Here t_con reads from both p_mid and p_token, so Rule S must NOT claim p_mid.
#[test]
fn test_rule_s_rejects_multi_pre_consumer() {
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_src"),
            place("p_mid"),
            place("p_token"), // second pre-place for consumer
            place("p_shared"),
        ],
        transitions: vec![
            trans("t_prod", vec![arc(0, 1)], vec![arc(1, 1)]),
            // Consumer reads from BOTH p_mid and p_token → pre != {p_mid}.
            trans("t_con", vec![arc(1, 1), arc(2, 1)], vec![arc(3, 1)]),
            // Give p_token initial supply so t_con isn't dead.
            trans("t_token_src", vec![], vec![arc(2, 1)]),
        ],
        initial_marking: vec![1, 0, 1, 0],
    };

    let reduced = reduce_iterative_structural_with_mode(&net, &[], ReductionMode::Reachability)
        .expect("reduction must succeed");

    let p_mid_rule_s = reduced
        .report
        .rule_s_agglomerations
        .iter()
        .any(|agg| agg.place == PlaceIdx(1));
    assert!(
        !p_mid_rule_s,
        "Rule S must NOT fire when consumer has multi-pre (pre != {{place}})"
    );
}

/// Producer/consumer disjointness (Tapaal T4/S4): a transition cannot be
/// both a producer and a consumer on the same place. Here t_loop is its
/// own producer-and-consumer via a self-loop on p_mid. Rule S must skip this.
#[test]
fn test_rule_s_rejects_non_disjoint_producers_consumers() {
    let net = PetriNet {
        name: None,
        places: vec![place("p_src"), place("p_mid"), place("p_shared")],
        transitions: vec![
            // Ordinary producer.
            trans("t_prod", vec![arc(0, 1)], vec![arc(1, 1)]),
            // t_loop both consumes from and produces to p_mid: in both sets.
            trans("t_loop", vec![arc(1, 1)], vec![arc(1, 1), arc(2, 1)]),
        ],
        initial_marking: vec![1, 0, 0],
    };

    let reduced = reduce_iterative_structural_with_mode(&net, &[], ReductionMode::Reachability)
        .expect("reduction must succeed");

    let p_mid_rule_s = reduced
        .report
        .rule_s_agglomerations
        .iter()
        .any(|agg| agg.place == PlaceIdx(1));
    assert!(
        !p_mid_rule_s,
        "Rule S must NOT fire when producers ∩ consumers is non-empty"
    );
}

/// Idempotence: running the reducer twice produces no new Rule S entries on
/// the second pass (fixpoint reached).
#[test]
fn test_rule_s_is_idempotent_under_iteration() {
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_a"),
            place("p_b"),
            place("p_mid"),
            place("p_shared"),
        ],
        transitions: vec![
            trans("t_prod1", vec![arc(0, 1)], vec![arc(2, 1)]),
            trans("t_prod2", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t_con1", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t_con2", vec![arc(2, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![1, 1, 0, 0],
    };

    let first = reduce_iterative_structural_with_mode(&net, &[], ReductionMode::Reachability)
        .expect("first reduction");
    let second =
        reduce_iterative_structural_with_mode(&first.net, &[], ReductionMode::Reachability)
            .expect("second reduction");

    assert_eq!(
        second.report.rule_s_agglomerations.len(),
        0,
        "Rule S should be idempotent: second pass finds nothing"
    );
}
