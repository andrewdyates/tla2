// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::examinations::one_safe::{one_safe_por_config, OneSafeObserver};
use crate::explorer::{explore_observer, ExplorationConfig};
use crate::output::Verdict;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
use crate::reduction::{reduce_iterative, ReducedNet};
use crate::stubborn::PorStrategy;

use super::super::one_safe_verdict;

fn place(id: &str) -> PlaceInfo {
    PlaceInfo {
        id: id.to_string(),
        name: None,
    }
}

fn arc(place: u32, weight: u64) -> Arc {
    Arc {
        place: PlaceIdx(place),
        weight,
    }
}

fn trans(id: &str, inputs: Vec<Arc>, outputs: Vec<Arc>) -> TransitionInfo {
    TransitionInfo {
        id: id.to_string(),
        name: None,
        inputs,
        outputs,
    }
}

/// Chain + independent subnets: token-conservative everywhere, so
/// P-invariant analysis proves all places ≤ 1. POR correctly disables.
fn one_safe_por_budget_net() -> PetriNet {
    PetriNet {
        name: Some("one-safe-por-budget".to_string()),
        places: vec![
            place("r0"),
            place("r1"),
            place("r2"),
            place("r3"),
            place("r4"),
            place("i0_in"),
            place("i0_out"),
            place("i1_in"),
            place("i1_out"),
            place("i2_in"),
            place("i2_out"),
            place("i3_in"),
            place("i3_out"),
        ],
        transitions: vec![
            trans("i0", vec![arc(5, 1)], vec![arc(6, 1)]),
            trans("i1", vec![arc(7, 1)], vec![arc(8, 1)]),
            trans("i2", vec![arc(9, 1)], vec![arc(10, 1)]),
            trans("i3", vec![arc(11, 1)], vec![arc(12, 1)]),
            trans("a0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("a1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("a2", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("a3", vec![arc(3, 1)], vec![arc(4, 1)]),
        ],
        initial_marking: vec![1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0],
    }
}

fn one_safe_unsafe_with_invisible_subnet() -> PetriNet {
    // drain consumes from r1, preventing LP from removing it via P-invariant
    // analysis (no invariant exists for r0/r1 with the drain transition).
    PetriNet {
        name: Some("one-safe-por-unsafe".to_string()),
        places: vec![
            place("r0"),
            place("r1"),
            place("safe_in"),
            place("safe_out"),
        ],
        transitions: vec![
            trans("dup", vec![arc(0, 1)], vec![arc(1, 2)]),
            trans("drain", vec![arc(1, 1)], vec![]),
            trans("safe", vec![arc(2, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![1, 0, 1, 0],
    }
}

/// Verify that reduction correctly preserves 1-safety for a chain net.
///
/// Before the agglomeration chaining fix, `reduce_iterative` could
/// chain multiple pre-agglomerations in one pass, creating transitions
/// with no inputs (always enabled → unbounded token production).
/// After the fix, the chain collapses correctly over multiple passes.
#[test]
fn test_one_safe_por_uses_risky_visible_subset() {
    let net = one_safe_por_budget_net();
    let reduced = reduce_iterative(&net).expect("reduction should succeed");
    let base_config = ExplorationConfig::new(1000);
    let por_config = one_safe_por_config(&reduced, &base_config);

    // All places in this net are covered by P-invariants with bound ≤ 1,
    // so POR correctly disables (no risky transitions to separate from
    // invisible ones).
    assert!(
        matches!(por_config.por_strategy, PorStrategy::None),
        "POR should be None for structurally 1-safe reduced net"
    );

    // Full BFS on the reduced net must complete and confirm 1-safety.
    let mut full_observer = OneSafeObserver::new();
    let full_result = explore_observer(&reduced.net, &base_config, &mut full_observer);
    assert!(full_result.completed);
    assert!(full_observer.is_safe());
}

/// Verdict uses P-invariant structural shortcut when all places bounded.
#[test]
fn test_one_safe_verdict_finishes_budgeted_safe_net_with_por() {
    let net = one_safe_por_budget_net();
    let reduced = reduce_iterative(&net).expect("reduction should succeed");
    let tight_budget = ExplorationConfig::new(9);

    let mut full_observer = OneSafeObserver::new();
    let full_result = explore_observer(&reduced.net, &tight_budget, &mut full_observer);
    assert!(
        !full_result.completed,
        "full BFS should exceed the tight budget without POR"
    );
    assert!(full_observer.is_safe());

    // one_safe_verdict uses the P-invariant structural shortcut,
    // returning True without exploration.
    assert_eq!(one_safe_verdict(&net, &tight_budget, &[]), Verdict::True);
}

#[test]
fn test_one_safe_por_finds_unsafe_visible_transition_before_invisible_work() {
    let net = one_safe_unsafe_with_invisible_subnet();
    let reduced = reduce_iterative(&net).expect("reduction should succeed");
    let por_config = one_safe_por_config(&reduced, &ExplorationConfig::new(32));

    let mut observer = OneSafeObserver::new();
    let result = explore_observer(&reduced.net, &por_config, &mut observer);

    assert!(!observer.is_safe());
    assert!(result.stopped_by_observer);
    assert_eq!(
        one_safe_verdict(&net, &ExplorationConfig::new(32), &[]),
        Verdict::False
    );
}

#[test]
fn test_one_safe_por_preserves_config_invariants() {
    let net = one_safe_unsafe_with_invisible_subnet();
    let reduced = ReducedNet::identity(&net);

    let fingerprint_on = ExplorationConfig::auto_sized(&net, None, Some(0.01));
    let fingerprint_on_budget = fingerprint_on.max_states();
    let base_config = fingerprint_on.with_fingerprint_dedup(false).with_workers(4);
    let fingerprint_off_budget = base_config.max_states();

    let por_config = one_safe_por_config(&reduced, &base_config);
    assert!(
        matches!(
            por_config.por_strategy,
            PorStrategy::SafetyPreserving { .. }
        ),
        "one-safe POR should remain active on the unsafe visible-subset net"
    );
    assert!(
        !por_config.fingerprint_dedup(),
        "derived POR config should preserve fingerprint-off mode"
    );
    assert_eq!(
        por_config.max_states(),
        fingerprint_off_budget,
        "derived POR config should preserve the active fingerprint-off budget"
    );
    assert_eq!(
        por_config.workers(),
        4,
        "derived POR config should preserve worker settings"
    );

    let restored = por_config.with_fingerprint_dedup(true);
    assert_eq!(
        restored.max_states(),
        fingerprint_on_budget,
        "derived POR config should retain auto-sizing basis for future recomputation"
    );
}
