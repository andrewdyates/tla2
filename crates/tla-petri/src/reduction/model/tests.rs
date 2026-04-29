// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{PlaceReconstruction, ReducedNet, ReductionMode, ReductionReport};
use crate::error::PnmlError;
use crate::petri_net::{PetriNet, PlaceIdx, PlaceInfo};

fn place(id: &str) -> PlaceInfo {
    PlaceInfo {
        id: id.to_string(),
        name: None,
    }
}

fn reduced_net_with_reconstruction(constant: u64) -> ReducedNet {
    ReducedNet {
        net: PetriNet {
            name: Some("reduced".to_string()),
            places: vec![place("kept")],
            transitions: Vec::new(),
            initial_marking: vec![4],
        },
        place_map: vec![None, Some(PlaceIdx(0))],
        place_unmap: vec![PlaceIdx(1)],
        place_scales: vec![1, 1],
        transition_map: Vec::new(),
        transition_unmap: Vec::new(),
        constant_values: Vec::new(),
        reconstructions: vec![PlaceReconstruction {
            place: PlaceIdx(0),
            constant,
            divisor: 1,
            terms: vec![(PlaceIdx(1), 1)],
        }],
        report: ReductionReport {
            redundant_places: vec![PlaceIdx(0)],
            ..ReductionReport::default()
        },
    }
}

#[test]
fn test_expand_marking_into_reconstructs_redundant_place() {
    let reduced = reduced_net_with_reconstruction(7);
    let mut full = Vec::new();

    reduced
        .expand_marking_into(&[4], &mut full)
        .expect("reconstruction should succeed");

    assert_eq!(full, vec![3, 4]);
}

#[test]
fn test_expand_marking_into_returns_error_on_reconstruction_underflow() {
    let reduced = reduced_net_with_reconstruction(3);
    let mut full = Vec::new();

    let error = reduced
        .expand_marking_into(&[4], &mut full)
        .expect_err("impossible reconstruction should fail closed");
    assert!(matches!(
        error,
        PnmlError::ReductionOverflow { ref context }
            if context.contains("reconstruction underflow")
    ));
}

/// Build a ReducedNet with custom reconstruction terms for overflow tests.
fn reduced_net_with_custom_recon(
    kept_marking: u64,
    terms: Vec<(PlaceIdx, u64)>,
    constant: u64,
) -> ReducedNet {
    ReducedNet {
        net: PetriNet {
            name: Some("reduced".to_string()),
            places: vec![place("kept")],
            transitions: Vec::new(),
            initial_marking: vec![kept_marking],
        },
        place_map: vec![None, Some(PlaceIdx(0))],
        place_unmap: vec![PlaceIdx(1)],
        place_scales: vec![1, 1],
        transition_map: Vec::new(),
        transition_unmap: Vec::new(),
        constant_values: Vec::new(),
        reconstructions: vec![PlaceReconstruction {
            place: PlaceIdx(0),
            constant,
            divisor: 1,
            terms,
        }],
        report: ReductionReport {
            redundant_places: vec![PlaceIdx(0)],
            ..ReductionReport::default()
        },
    }
}

#[test]
fn test_expand_marking_into_returns_error_on_reconstruction_mul_overflow() {
    let reduced = reduced_net_with_custom_recon(2, vec![(PlaceIdx(1), u64::MAX)], u64::MAX);
    let mut full = Vec::new();

    let error = reduced
        .expand_marking_into(&[2], &mut full)
        .expect_err("checked_mul overflow should fail closed");
    assert!(matches!(
        error,
        PnmlError::ReductionOverflow { ref context }
            if context.contains("reconstruction overflow")
    ));
}

#[test]
fn test_expand_marking_into_returns_error_on_reconstruction_sum_overflow() {
    let reduced = ReducedNet {
        net: PetriNet {
            name: Some("reduced".to_string()),
            places: vec![place("kept_a"), place("kept_b")],
            transitions: Vec::new(),
            initial_marking: vec![u64::MAX, 1],
        },
        place_map: vec![None, Some(PlaceIdx(0)), Some(PlaceIdx(1))],
        place_unmap: vec![PlaceIdx(1), PlaceIdx(2)],
        place_scales: vec![1, 1, 1],
        transition_map: Vec::new(),
        transition_unmap: Vec::new(),
        constant_values: Vec::new(),
        reconstructions: vec![PlaceReconstruction {
            place: PlaceIdx(0),
            constant: u64::MAX,
            divisor: 1,
            terms: vec![(PlaceIdx(1), 1), (PlaceIdx(2), 1)],
        }],
        report: ReductionReport {
            redundant_places: vec![PlaceIdx(0)],
            ..ReductionReport::default()
        },
    };
    let mut full = Vec::new();

    let error = reduced
        .expand_marking_into(&[u64::MAX, 1], &mut full)
        .expect_err("checked_add overflow should fail closed");
    assert!(matches!(
        error,
        PnmlError::ReductionOverflow { ref context }
            if context.contains("reconstruction overflow")
    ));
}

#[test]
fn test_compose_returns_error_on_place_scale_overflow() {
    let net = PetriNet {
        name: Some("compose-overflow".to_string()),
        places: vec![place("p0")],
        transitions: Vec::new(),
        initial_marking: vec![1],
    };
    let outer = ReducedNet {
        net: net.clone(),
        place_map: vec![Some(PlaceIdx(0))],
        place_unmap: vec![PlaceIdx(0)],
        place_scales: vec![u64::MAX],
        transition_map: Vec::new(),
        transition_unmap: Vec::new(),
        constant_values: Vec::new(),
        reconstructions: Vec::new(),
        report: ReductionReport::default(),
    };
    let inner = ReducedNet {
        net,
        place_map: vec![Some(PlaceIdx(0))],
        place_unmap: vec![PlaceIdx(0)],
        place_scales: vec![2],
        transition_map: Vec::new(),
        transition_unmap: Vec::new(),
        constant_values: Vec::new(),
        reconstructions: Vec::new(),
        report: ReductionReport::default(),
    };

    let error = outer
        .compose(&inner)
        .expect_err("place-scale overflow should fail closed");
    assert!(matches!(
        error,
        PnmlError::ReductionOverflow { ref context }
            if context.contains("composing reduction")
    ));
}

// ── ReductionMode gating tests ──

#[test]
fn test_reduction_mode_reachability_allows_all_rules() {
    let mode = ReductionMode::Reachability;
    assert!(mode.allows_dead_transition_removal());
    assert!(mode.allows_constant_place_removal());
    assert!(mode.allows_isolated_place_removal());
    assert!(mode.allows_source_place_removal());
    assert!(mode.allows_agglomeration());
    assert!(mode.allows_duplicate_transition_removal());
    assert!(mode.allows_self_loop_transition_removal());
    assert!(mode.allows_self_loop_arc_removal());
    assert!(mode.allows_never_disabling_arc_removal());
    assert!(mode.allows_parallel_place_merge());
    assert!(mode.allows_non_decreasing_place_removal());
    assert!(mode.allows_redundant_place_removal());
    assert!(mode.allows_token_eliminated_place_removal());
    assert!(mode.allows_dominated_transition_removal());
}

#[test]
fn test_reduction_mode_next_free_ctl_forbids_agglomeration() {
    let mode = ReductionMode::NextFreeCTL;
    // Safe: dead/constant/isolated + most invariant-based rules.
    assert!(mode.allows_dead_transition_removal());
    assert!(mode.allows_constant_place_removal());
    assert!(mode.allows_isolated_place_removal());
    assert!(mode.allows_source_place_removal());
    assert!(mode.allows_duplicate_transition_removal());
    assert!(mode.allows_self_loop_transition_removal());
    assert!(mode.allows_parallel_place_merge());
    assert!(mode.allows_redundant_place_removal());
    // Forbidden: agglomeration changes path structure.
    assert!(!mode.allows_agglomeration());
    // Token-eliminated is reachability-only.
    assert!(!mode.allows_token_eliminated_place_removal());
}

#[test]
fn test_reduction_mode_ctl_with_next_minimal_safe_set() {
    let mode = ReductionMode::CTLWithNext;
    // Only dead/constant/isolated are universally safe.
    assert!(mode.allows_dead_transition_removal());
    assert!(mode.allows_constant_place_removal());
    assert!(mode.allows_isolated_place_removal());
    // Everything else is forbidden for CTL with EX/AX.
    assert!(!mode.allows_source_place_removal());
    assert!(!mode.allows_agglomeration());
    assert!(!mode.allows_duplicate_transition_removal());
    assert!(!mode.allows_self_loop_transition_removal());
    assert!(!mode.allows_self_loop_arc_removal());
    assert!(!mode.allows_never_disabling_arc_removal());
    assert!(!mode.allows_parallel_place_merge());
    assert!(!mode.allows_non_decreasing_place_removal());
    assert!(!mode.allows_redundant_place_removal());
    assert!(!mode.allows_token_eliminated_place_removal());
    assert!(!mode.allows_dominated_transition_removal());
}

#[test]
fn test_reduction_mode_stutter_insensitive_ltl_matches_next_free_ctl() {
    let ltl = ReductionMode::StutterInsensitiveLTL;
    let ctl = ReductionMode::NextFreeCTL;
    // Stutter-insensitive LTL and next-free CTL allow the same rules.
    assert_eq!(
        ltl.allows_source_place_removal(),
        ctl.allows_source_place_removal()
    );
    assert_eq!(ltl.allows_agglomeration(), ctl.allows_agglomeration());
    assert_eq!(
        ltl.allows_duplicate_transition_removal(),
        ctl.allows_duplicate_transition_removal()
    );
    assert_eq!(
        ltl.allows_redundant_place_removal(),
        ctl.allows_redundant_place_removal()
    );
}

#[test]
fn test_reduction_mode_stutter_sensitive_ltl_minimal() {
    let mode = ReductionMode::StutterSensitiveLTL;
    // Only dead/constant/isolated.
    assert!(mode.allows_dead_transition_removal());
    assert!(mode.allows_constant_place_removal());
    assert!(mode.allows_isolated_place_removal());
    assert!(!mode.allows_source_place_removal());
    assert!(!mode.allows_agglomeration());
    assert!(!mode.allows_parallel_place_merge());
}

#[test]
fn test_examination_reduction_mode_mapping() {
    use crate::examination::Examination;

    assert_eq!(
        Examination::ReachabilityCardinality.reduction_mode(),
        ReductionMode::Reachability
    );
    assert_eq!(
        Examination::ReachabilityFireability.reduction_mode(),
        ReductionMode::Reachability
    );
    assert_eq!(
        Examination::ReachabilityDeadlock.reduction_mode(),
        ReductionMode::Reachability
    );
    assert_eq!(
        Examination::CTLCardinality.reduction_mode(),
        ReductionMode::NextFreeCTL
    );
    assert_eq!(
        Examination::CTLFireability.reduction_mode(),
        ReductionMode::NextFreeCTL
    );
    assert_eq!(
        Examination::LTLCardinality.reduction_mode(),
        ReductionMode::StutterInsensitiveLTL
    );
    assert_eq!(
        Examination::LTLFireability.reduction_mode(),
        ReductionMode::StutterInsensitiveLTL
    );
    assert_eq!(
        Examination::StateSpace.reduction_mode(),
        ReductionMode::Reachability
    );
    assert_eq!(
        Examination::UpperBounds.reduction_mode(),
        ReductionMode::Reachability
    );
}
