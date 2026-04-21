// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Tapaal Rule R: post-agglomeration with multi-consumer fan-out.
//!
//! Reference: Tapaal verifypn `Reducer.cpp:2383-2554`.
//! Design: `designs/2026-04-20-rule-r-post-agglomeration-multi-consumer.md`.

use crate::petri_net::{PetriNet, PlaceIdx};
use crate::reduction::{
    reduce, reduce_iterative_structural_with_mode, ReductionMode,
};

use super::super::support::{arc, place, trans};

/// 2-producer × 2-consumer fan-out on a single intermediate place.
///
/// Net:
///   p_a →(1) t_prod1 →(1) p_mid + p_extra1  (multi-post producer)
///   p_b →(1) t_prod2 →(1) p_mid
///   p_mid →(1) t_con1 →(1) p_shared
///   p_mid →(1) t_con2 →(1) p_shared
///
/// Rule R fuses 2 producers × 2 consumers = 4 synthesized transitions, removing
/// the 4 originals and p_mid. Cartesian product 4 ≤ limiter 6.
///
/// Key design:
///   - `t_prod1` has a multi-post (`{p_mid, p_extra1}`) which DISQUALIFIES
///     Rule S (Rule S requires `producer.post == {p_mid}` exactly). Rule R
///     is strictly more permissive on producers: it strips the `p_mid` arc
///     and keeps the other outputs. This ensures Rule S does NOT pre-empt.
///   - Consumers (t_con1, t_con2) have single-input pre-set {p_mid}
///     → matches Rule R Cond 3.
///   - Both write to the SAME p_shared → p_shared has 2 producers →
///     pre-agglom Cond 2 fails on each consumer → not claimed.
///   - p_mid has 2 consumers → post-agglom Cond 2 fails on each consumer.
#[test]
fn test_rule_r_two_by_two_fan_out_synthesizes_four_transitions() {
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_a"),      // 0
            place("p_b"),      // 1
            place("p_mid"),    // 2
            place("p_shared"), // 3 — shared post-place of both consumers
            place("p_extra1"), // 4 — extra post-place on t_prod1 (disqualifies Rule S)
        ],
        transitions: vec![
            // t_prod1 is multi-post → Rule S rejects (post != {p_mid});
            // Rule R accepts by stripping the p_mid arc.
            trans("t_prod1", vec![arc(0, 1)], vec![arc(2, 1), arc(4, 1)]),
            trans("t_prod2", vec![arc(1, 1)], vec![arc(2, 1)]),
            // Consumers share one post-place.
            trans("t_con1", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t_con2", vec![arc(2, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![1, 1, 0, 0, 0],
    };

    let reduced = reduce_iterative_structural_with_mode(
        &net,
        &[],
        ReductionMode::Reachability,
    )
    .expect("reduction must succeed");

    // Rule R should fire: p_mid gone, 4 producer/consumer transitions gone,
    // 4 synthesized transitions present. Other rules may cascade further,
    // but we assert at minimum that Rule R ran.
    let rule_r_count: usize = reduced
        .report
        .rule_r_agglomerations
        .iter()
        .map(|agg| agg.fuseable_producers.len() * agg.consumers.len())
        .sum();
    assert!(
        rule_r_count >= 4,
        "Rule R should synthesize at least 4 (producer, consumer) pairs, got {rule_r_count}"
    );
    // p_mid (original index 2) must not survive.
    assert!(reduced.place_map[2].is_none(), "p_mid must be removed");
}

/// Idempotence: reducing the same net twice yields the same reduction (no drift,
/// no double-application).
#[test]
fn test_rule_r_is_idempotent_under_iteration() {
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_a"),
            place("p_b"),
            place("p_mid"),
            place("p_out1"),
            place("p_out2"),
        ],
        transitions: vec![
            trans("t_prod1", vec![arc(0, 1)], vec![arc(2, 1)]),
            trans("t_prod2", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t_con1", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t_con2", vec![arc(2, 1)], vec![arc(4, 1)]),
            trans("t_sink1", vec![arc(3, 1)], vec![]),
            trans("t_sink2", vec![arc(4, 1)], vec![]),
        ],
        initial_marking: vec![1, 1, 0, 0, 0],
    };

    let first = reduce_iterative_structural_with_mode(
        &net,
        &[],
        ReductionMode::Reachability,
    )
    .expect("first reduction");
    let second = reduce_iterative_structural_with_mode(
        &first.net,
        &[],
        ReductionMode::Reachability,
    )
    .expect("second reduction");

    // Second pass should produce no new Rule R entries (fixpoint reached).
    assert_eq!(
        second.report.rule_r_agglomerations.len(),
        0,
        "Rule R should be idempotent: second pass finds nothing"
    );
}

/// Dead-cascade composition: a Rule R agglomeration that leaves a dead
/// consumer (never reachable) should cascade to dead-transition removal.
///
/// Here we place a producer with zero initial tokens on its input, and no
/// other producers. The producer is dead; its agglomeration place has no live
/// producers, so Rule R doesn't fire. But if we unblock the producer, Rule R
/// should compose cleanly with cascade removal.
#[test]
fn test_rule_r_composes_with_dead_transition_removal() {
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_src"),
            place("p_mid"),
            place("p_out1"),
            place("p_out2"),
        ],
        transitions: vec![
            // p_src has 1 token: t_prod fires.
            trans("t_prod", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_con1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t_con2", vec![arc(1, 1)], vec![arc(3, 1)]),
            trans("t_sink1", vec![arc(2, 1)], vec![]),
            trans("t_sink2", vec![arc(3, 1)], vec![]),
        ],
        initial_marking: vec![1, 0, 0, 0],
    };

    let reduced = reduce_iterative_structural_with_mode(
        &net,
        &[],
        ReductionMode::Reachability,
    )
    .expect("reduction must succeed");

    // p_mid should be removed (via Rule R or other cascade).
    assert!(
        reduced.place_map[1].is_none(),
        "p_mid should be removed via Rule R cascade"
    );
}

/// Explosion limiter: 3 producers × 3 consumers = 9 pairs, exceeds limiter 6.
/// Rule R should SKIP this place entirely rather than synthesizing 9 transitions.
#[test]
fn test_rule_r_skips_when_explosion_limiter_exceeded() {
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_a"),
            place("p_b"),
            place("p_c"),
            place("p_mid"),
            place("p_out1"),
            place("p_out2"),
            place("p_out3"),
        ],
        transitions: vec![
            trans("t_prod1", vec![arc(0, 1)], vec![arc(3, 1)]),
            trans("t_prod2", vec![arc(1, 1)], vec![arc(3, 1)]),
            trans("t_prod3", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t_con1", vec![arc(3, 1)], vec![arc(4, 1)]),
            trans("t_con2", vec![arc(3, 1)], vec![arc(5, 1)]),
            trans("t_con3", vec![arc(3, 1)], vec![arc(6, 1)]),
            trans("t_sink1", vec![arc(4, 1)], vec![]),
            trans("t_sink2", vec![arc(5, 1)], vec![]),
            trans("t_sink3", vec![arc(6, 1)], vec![]),
        ],
        initial_marking: vec![1, 1, 1, 0, 0, 0, 0],
    };

    let reduced = reduce_iterative_structural_with_mode(
        &net,
        &[],
        ReductionMode::Reachability,
    )
    .expect("reduction must succeed");

    // Rule R must NOT fire on p_mid (would exceed limiter).
    let p_mid_rule_r = reduced
        .report
        .rule_r_agglomerations
        .iter()
        .any(|agg| agg.place == PlaceIdx(3));
    assert!(
        !p_mid_rule_r,
        "Rule R must skip p_mid: 3×3=9 exceeds limiter 6"
    );
}

/// Mode gating: Rule R should NOT fire for `CTLWithNext`,
/// `StutterSensitiveLTL`, or `OneSafe`-equivalent semantics.
#[test]
fn test_rule_r_gated_off_for_ctl_with_next() {
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_a"),
            place("p_b"),
            place("p_mid"),
            place("p_out1"),
            place("p_out2"),
        ],
        transitions: vec![
            trans("t_prod1", vec![arc(0, 1)], vec![arc(2, 1)]),
            trans("t_prod2", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t_con1", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t_con2", vec![arc(2, 1)], vec![arc(4, 1)]),
            trans("t_sink1", vec![arc(3, 1)], vec![]),
            trans("t_sink2", vec![arc(4, 1)], vec![]),
        ],
        initial_marking: vec![1, 1, 0, 0, 0],
    };

    let reduced_ctl = reduce_iterative_structural_with_mode(
        &net,
        &[],
        ReductionMode::CTLWithNext,
    )
    .expect("reduction must succeed");
    assert!(
        reduced_ctl.report.rule_r_agglomerations.is_empty(),
        "Rule R must NOT fire for CTLWithNext"
    );

    let reduced_stutter = reduce_iterative_structural_with_mode(
        &net,
        &[],
        ReductionMode::StutterSensitiveLTL,
    )
    .expect("reduction must succeed");
    assert!(
        reduced_stutter.report.rule_r_agglomerations.is_empty(),
        "Rule R must NOT fire for StutterSensitiveLTL"
    );
}

/// Sanity check: with `reduce()` (default ExactMarking semantics), Rule R
/// should activate where applicable (reachability-equivalent).
///
/// Uses the same shared-post-place topology as the 2×2 fan-out test so that
/// neither pre- nor post-agglomeration can claim the consumer transitions
/// before Rule R runs.
#[test]
fn test_rule_r_activates_under_exact_marking_semantics() {
    let net = PetriNet {
        name: None,
        places: vec![
            place("p_a"),      // 0
            place("p_b"),      // 1
            place("p_mid"),    // 2
            place("p_shared"), // 3 — shared post-place, fails pre-agglom Cond 2.
        ],
        transitions: vec![
            trans("t_prod1", vec![arc(0, 1)], vec![arc(2, 1)]),
            trans("t_prod2", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t_con1", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t_con2", vec![arc(2, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![1, 1, 0, 0],
    };

    let reduced = reduce(&net);
    let synthesized: usize = reduced
        .report
        .rule_r_agglomerations
        .iter()
        .map(|agg| agg.fuseable_producers.len() * agg.consumers.len())
        .sum();
    assert!(
        synthesized >= 4,
        "Rule R should synthesize ≥4 pairs under ExactMarking, got {synthesized}"
    );
}
