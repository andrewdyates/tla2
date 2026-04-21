// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};
use crate::reduction::ReductionMode;

use super::super::super::analysis::analyze_efmnop_fixpoint;
use super::super::support::{arc, place, trans};

#[test]
fn test_efmnop_fixpoint_cascade_dead_to_orphan_exposes_isolated_places() {
    let net = PetriNet {
        name: Some("cascade-dead-to-orphan".into()),
        places: vec![
            place("p0"),
            place("p1"),
            place("p2"),
            place("p_live_in"),
            place("p_live_out"),
        ],
        transitions: vec![
            trans("t0_dead", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1_dead", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t_live", vec![arc(3, 1)], vec![arc(4, 1)]),
        ],
        initial_marking: vec![0, 0, 0, 1, 0],
    };

    let analysis = analyze_efmnop_fixpoint(&net, &[], ReductionMode::Reachability);

    assert_eq!(
        analysis.report.dead_transitions,
        vec![TransitionIdx(0), TransitionIdx(1)]
    );
    assert_eq!(
        analysis.report.isolated_places,
        vec![PlaceIdx(0), PlaceIdx(1), PlaceIdx(2)]
    );
    assert_eq!(analysis.dead_removed_by_cascade, 1);
    assert_eq!(analysis.per_rule_progress.rule_o_dead, 2);
    assert_eq!(analysis.per_rule_progress.rule_o_orphan, 3);
    assert_eq!(analysis.iterations, 2);
}

#[test]
fn test_efmnop_fixpoint_single_pass_simple_net_stabilizes() {
    let net = PetriNet {
        name: Some("single-pass-duplicate".into()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_back", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };

    let analysis = analyze_efmnop_fixpoint(&net, &[], ReductionMode::Reachability);

    assert_eq!(analysis.iterations, 1);
    assert!(analysis.report.dead_transitions.is_empty());
    assert_eq!(analysis.report.duplicate_transitions.len(), 1);
    assert_eq!(
        analysis.report.duplicate_transitions[0].duplicates,
        vec![TransitionIdx(1)]
    );
    assert_eq!(analysis.per_rule_progress.rule_m_duplicate, 1);
}

#[test]
fn test_efmnop_fixpoint_multi_pass_dead_removal_enables_agglomeration() {
    let net = PetriNet {
        name: Some("dead-enables-agglomeration".into()),
        places: vec![
            place("p_block"),
            place("p_in"),
            place("p_mid"),
            place("p_out"),
        ],
        transitions: vec![
            trans("t_dead", vec![arc(0, 1)], vec![arc(2, 2)]),
            trans("t_src", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t_sink", vec![arc(2, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![0, 1, 0, 0],
    };

    let analysis = analyze_efmnop_fixpoint(&net, &[], ReductionMode::Reachability);

    assert_eq!(analysis.report.dead_transitions, vec![TransitionIdx(0)]);
    assert_eq!(analysis.report.pre_agglomerations.len(), 1);
    assert_eq!(
        analysis.report.pre_agglomerations[0].transition,
        TransitionIdx(1)
    );
    assert_eq!(analysis.report.pre_agglomerations[0].place, PlaceIdx(2));
    assert_eq!(analysis.per_rule_progress.rule_p_pre_agglomeration, 1);
    assert_eq!(analysis.iterations, 2);
}

#[test]
fn test_efmnop_fixpoint_mode_gating_ctl_with_next_restricts_rules() {
    let net = PetriNet {
        name: Some("ctl-with-next-gating".into()),
        places: vec![
            place("p_dead"),
            place("p_dead_out"),
            place("p0"),
            place("p1"),
        ],
        transitions: vec![
            trans("t_dead", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t0", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t1", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t_back", vec![arc(3, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![0, 0, 1, 0],
    };

    let reachability = analyze_efmnop_fixpoint(&net, &[], ReductionMode::Reachability);
    let ctl_with_next = analyze_efmnop_fixpoint(&net, &[], ReductionMode::CTLWithNext);

    assert_eq!(reachability.report.duplicate_transitions.len(), 1);
    assert_eq!(
        ctl_with_next.report.dead_transitions,
        vec![TransitionIdx(0)]
    );
    assert_eq!(
        ctl_with_next.report.isolated_places,
        vec![PlaceIdx(0), PlaceIdx(1)]
    );
    assert!(ctl_with_next.report.duplicate_transitions.is_empty());
    assert!(ctl_with_next.report.pre_agglomerations.is_empty());
    assert_eq!(ctl_with_next.iterations, 2);
}

#[test]
fn test_efmnop_fixpoint_empty_net_returns_zero_iterations() {
    let net = PetriNet {
        name: Some("empty".into()),
        places: Vec::new(),
        transitions: Vec::new(),
        initial_marking: Vec::new(),
    };

    let analysis = analyze_efmnop_fixpoint(&net, &[], ReductionMode::Reachability);

    assert_eq!(analysis.iterations, 0);
    assert_eq!(analysis.dead_removed_by_cascade, 0);
    assert!(!analysis.report.has_reductions());
}

#[test]
fn test_efmnop_fixpoint_combined_m_and_o_rules_both_reported() {
    let net = PetriNet {
        name: Some("combined-m-o".into()),
        places: vec![
            place("p_dead"),
            place("p_dead_out"),
            place("p0"),
            place("p1"),
        ],
        transitions: vec![
            trans("t_dead", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t0", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t1", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t_back", vec![arc(3, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![0, 0, 1, 0],
    };

    let analysis = analyze_efmnop_fixpoint(&net, &[], ReductionMode::Reachability);

    assert_eq!(analysis.report.dead_transitions, vec![TransitionIdx(0)]);
    assert_eq!(analysis.report.duplicate_transitions.len(), 1);
    assert_eq!(analysis.per_rule_progress.rule_o_dead, 1);
    assert_eq!(analysis.per_rule_progress.rule_m_duplicate, 1);
    assert_eq!(
        analysis.report.duplicate_transitions[0].duplicates,
        vec![TransitionIdx(2)]
    );
}
