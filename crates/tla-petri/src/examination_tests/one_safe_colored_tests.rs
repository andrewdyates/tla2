// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for OneSafe on colored (unfolded) models.
//!
//! MCC defines 1-safe for colored nets as: no colored place holds more than
//! 1 token total (sum across all color instances). When a colored net is
//! unfolded, each (place, color) pair becomes a separate PT place. The
//! `colored_groups` parameter groups these unfolded places back together.
//!
//! Before fa6a77108, OneSafe checked individual unfolded place bounds instead
//! of group sums, producing false TRUE on models like TokenRing-COL-015.

use crate::examination::one_safe_verdict;
use crate::examinations::one_safe::OneSafeObserver;
use crate::explorer::{explore_observer, ExplorationConfig};
use crate::output::Verdict;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};

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

/// Simulates an unfolded colored net with 2 colors for one colored place.
///
/// Colored place C0 unfolds to PT places P0 (color a), P1 (color b).
/// T0 moves a token from P0 to P1 (color rotation).
///
/// Initial marking: P0=1, P1=0.
/// The group sum is always 1 (token-conservative within the group).
/// Individual places are each bounded ≤ 1 by a P-invariant (P0 + P1 = 1).
/// The group bound is also ≤ 1.
fn two_color_safe_rotation() -> PetriNet {
    PetriNet {
        name: Some("two-color-safe-rotation".into()),
        places: vec![place("C0_a"), place("C0_b")],
        transitions: vec![
            trans("rotate_ab", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("rotate_ba", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    }
}

/// Simulates an unfolded colored net where a transition duplicates tokens
/// across color instances, violating the group-level 1-safe property.
///
/// Colored place C0 unfolds to P0 (color a), P1 (color b).
/// T0 takes 1 token from P0 and puts 1 in both P0 and P1.
///
/// Initial marking: P0=1, P1=0. Group sum = 1 initially.
/// After T0 fires: P0=1, P1=1. Group sum = 2 > 1.
/// Each individual place is ≤ 1, but the group sum exceeds 1.
///
/// This is the core pattern that caused false TRUE on TokenRing-COL-015.
fn two_color_unsafe_duplication() -> PetriNet {
    PetriNet {
        name: Some("two-color-unsafe-dup".into()),
        places: vec![place("C0_a"), place("C0_b")],
        transitions: vec![trans("dup", vec![arc(0, 1)], vec![arc(0, 1), arc(1, 1)])],
        initial_marking: vec![1, 0],
    }
}

/// OneSafe returns FALSE when initial marking group sum > 1.
#[test]
fn test_one_safe_colored_initial_marking_group_sum_exceeds_one() {
    let net = PetriNet {
        name: Some("colored-initial-unsafe".into()),
        places: vec![place("C0_a"), place("C0_b")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![1, 1], // group sum = 2 > 1
    };
    let groups = vec![vec![0, 1]];
    let config = ExplorationConfig::new(100);

    assert_eq!(
        one_safe_verdict(&net, &config, &groups),
        Verdict::False,
        "OneSafe should be FALSE when initial colored group sum > 1"
    );
}

/// OneSafe returns TRUE via structural shortcut when P-invariant proves
/// group bound ≤ 1.
#[test]
fn test_one_safe_colored_structural_shortcut_group_bounded() {
    let net = two_color_safe_rotation();
    let groups = vec![vec![0, 1]]; // both places are one colored group
    let config = ExplorationConfig::new(100);

    assert_eq!(
        one_safe_verdict(&net, &config, &groups),
        Verdict::True,
        "OneSafe should be TRUE: P-invariant P0+P1=1 proves group bound ≤ 1"
    );
}

/// OneSafe returns FALSE via exploration when a reachable state has
/// group sum > 1, even though individual places never exceed 1.
///
/// Regression: before fa6a77108, this returned TRUE because only individual
/// place bounds were checked.
#[test]
fn test_one_safe_colored_exploration_finds_group_violation() {
    let net = two_color_unsafe_duplication();
    let groups = vec![vec![0, 1]]; // both places form one colored group
    let config = ExplorationConfig::new(100);

    let verdict = one_safe_verdict(&net, &config, &groups);
    assert_eq!(
        verdict,
        Verdict::False,
        "OneSafe should be FALSE: after T0 fires, group sum = 2 > 1"
    );
}

/// OneSafeObserver with colored groups detects group-level violation.
#[test]
fn test_one_safe_observer_colored_detects_group_sum_violation() {
    let net = two_color_unsafe_duplication();
    let groups = vec![vec![0, 1]];
    let config = ExplorationConfig::new(100);

    let mut observer = OneSafeObserver::new_colored(groups);
    let result = explore_observer(&net, &config, &mut observer);

    assert!(
        !observer.is_safe(),
        "colored observer should detect group sum > 1"
    );
    assert!(
        result.stopped_by_observer,
        "exploration should stop when observer detects violation"
    );
}

/// OneSafeObserver with colored groups confirms safety on a safe net.
#[test]
fn test_one_safe_observer_colored_confirms_safe_rotation() {
    let net = two_color_safe_rotation();
    let groups = vec![vec![0, 1]];
    let config = ExplorationConfig::new(100);

    let mut observer = OneSafeObserver::new_colored(groups);
    let result = explore_observer(&net, &config, &mut observer);

    assert!(observer.is_safe(), "colored observer should confirm safety");
    assert!(
        result.completed,
        "exploration should complete on small safe net"
    );
}

/// Multiple colored groups: one safe, one unsafe.
#[test]
fn test_one_safe_colored_mixed_groups_unsafe_detected() {
    // C0 unfolds to P0, P1 (safe rotation). C1 unfolds to P2, P3 (unsafe dup).
    let net = PetriNet {
        name: Some("mixed-groups".into()),
        places: vec![place("C0_a"), place("C0_b"), place("C1_a"), place("C1_b")],
        transitions: vec![
            trans("rotate", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("rotate_back", vec![arc(1, 1)], vec![arc(0, 1)]),
            trans("dup", vec![arc(2, 1)], vec![arc(2, 1), arc(3, 1)]),
        ],
        initial_marking: vec![1, 0, 1, 0],
    };
    let groups = vec![vec![0, 1], vec![2, 3]];
    let config = ExplorationConfig::new(200);

    assert_eq!(
        one_safe_verdict(&net, &config, &groups),
        Verdict::False,
        "OneSafe should be FALSE: group C1 sum reaches 2"
    );
}

/// Without colored_groups (empty), the duplication net is NOT 1-safe:
/// place C0_b (P1) is an accumulator that reaches token count 2 after
/// two firings of `dup`. Before #1489, structural reductions (source
/// place removal) hid this accumulation and returned a wrong TRUE.
#[test]
fn test_one_safe_non_colored_dup_net_is_unsafe() {
    let net = two_color_unsafe_duplication();
    let config = ExplorationConfig::new(100);

    // P1 (C0_b) starts at 0, gains +1 per firing with no consumer → reaches 2.
    let verdict = one_safe_verdict(&net, &config, &[]);
    assert_eq!(
        verdict,
        Verdict::False,
        "P1 accumulates tokens without bound — not 1-safe"
    );
}
