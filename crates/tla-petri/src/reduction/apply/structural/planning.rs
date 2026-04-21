// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};

use super::super::super::analysis::{
    find_never_disabling_arcs, find_non_decreasing_places, find_parallel_places,
    find_self_loop_arcs, find_source_places, find_token_eliminated_places,
};
use super::super::super::model::PlaceReconstruction;
use super::super::super::redundant::find_redundant_places;
use super::super::super::ReductionReport;
use super::StructuralReductionSemantics;

/// Internal plan produced by the planning phase, consumed by materialization.
pub(super) struct StructuralPlan {
    pub(super) report: ReductionReport,
    pub(super) place_removed: Vec<bool>,
    pub(super) place_agglomerated: Vec<bool>,
    pub(super) redundant_set: Vec<bool>,
    pub(super) reconstructions: Vec<PlaceReconstruction>,
}

/// Analyze the net under the given semantics and produce a removal plan.
///
/// Returns `None` when no reductions were found (caller should return identity).
pub(super) fn build_structural_plan(
    net: &PetriNet,
    protected_places: &[bool],
    semantics: StructuralReductionSemantics,
) -> Option<StructuralPlan> {
    let mut report = super::super::super::analysis::analyze(net);

    let temporal_projection_candidate = super::uses_temporal_projection_candidate(semantics);
    let one_safe_semantics = matches!(semantics, StructuralReductionSemantics::OneSafe);

    // Test-only temporal candidate: keep only dead transitions, constant
    // places, and isolated places.
    if temporal_projection_candidate {
        report.source_places.clear();
        report.pre_agglomerations.clear();
        report.post_agglomerations.clear();
        report.self_loop_transitions.clear();
        report.duplicate_transitions.clear();
        report.dominated_transitions.clear();
        report.parallel_places.clear();
        report.non_decreasing_places.clear();
        report.token_eliminated_places.clear();
    }

    if one_safe_semantics {
        report.source_places.clear();
        report.pre_agglomerations.clear();
        report.post_agglomerations.clear();
        report.non_decreasing_places.clear();
        report.parallel_places.clear();
    }

    if !temporal_projection_candidate && !one_safe_semantics {
        report.source_places = find_source_places(net, &report.dead_transitions, protected_places);
    }

    // Build self-loop protection mask EARLY: places touched by self-loop
    // transitions must be protected from ALL removal rules.
    let num_places = net.num_places();
    let mut self_loop_protected = vec![false; num_places];
    if !temporal_projection_candidate {
        for &TransitionIdx(t) in &report.self_loop_transitions {
            let trans = &net.transitions[t as usize];
            for arc in &trans.inputs {
                self_loop_protected[arc.place.0 as usize] = true;
            }
            for arc in &trans.outputs {
                self_loop_protected[arc.place.0 as usize] = true;
            }
        }
    }
    for (p, &ext) in protected_places.iter().enumerate() {
        if ext {
            self_loop_protected[p] = true;
        }
    }

    // Skip Rule K and Rule N in deadlock-safe/one-safe mode and temporal candidate.
    if !matches!(
        semantics,
        StructuralReductionSemantics::DeadlockSafe | StructuralReductionSemantics::OneSafe
    ) && !temporal_projection_candidate
    {
        report.self_loop_arcs = find_self_loop_arcs(
            net,
            &report.dead_transitions,
            &report.self_loop_transitions,
            protected_places,
        );
        report.never_disabling_arcs = find_never_disabling_arcs(
            net,
            &report.dead_transitions,
            &report.self_loop_transitions,
            protected_places,
        );
    }
    if !temporal_projection_candidate && !one_safe_semantics {
        report.non_decreasing_places = find_non_decreasing_places(
            net,
            &report.dead_transitions,
            &self_loop_protected,
            &report.source_places,
        );
    }
    if !temporal_projection_candidate && !one_safe_semantics {
        report.parallel_places =
            find_parallel_places(net, &report.dead_transitions, &self_loop_protected);
    }
    if matches!(semantics, StructuralReductionSemantics::QueryRelevantOnly) {
        report.token_eliminated_places = find_token_eliminated_places(
            net,
            &report.dead_transitions,
            &report.self_loop_transitions,
            protected_places,
            &report.parallel_places,
            &report.source_places,
            &report.non_decreasing_places,
            &report.never_disabling_arcs,
        );
    }

    // Build set of places to remove.
    let mut place_removed = vec![false; num_places];
    let mut place_agglomerated = vec![false; num_places];

    for &PlaceIdx(p) in &report.constant_places {
        if !self_loop_protected[p as usize] {
            place_removed[p as usize] = true;
        }
    }
    for &PlaceIdx(p) in &report.source_places {
        place_removed[p as usize] = true;
    }
    for &PlaceIdx(p) in &report.isolated_places {
        if !self_loop_protected[p as usize] {
            place_removed[p as usize] = true;
        }
    }
    for agg in &report.pre_agglomerations {
        if !self_loop_protected[agg.place.0 as usize] {
            place_removed[agg.place.0 as usize] = true;
            place_agglomerated[agg.place.0 as usize] = true;
        }
    }
    for agg in &report.post_agglomerations {
        if !self_loop_protected[agg.place.0 as usize] {
            place_removed[agg.place.0 as usize] = true;
            place_agglomerated[agg.place.0 as usize] = true;
        }
    }
    for merge in &report.parallel_places {
        place_removed[merge.duplicate.0 as usize] = true;
    }
    for &PlaceIdx(p) in &report.non_decreasing_places {
        place_removed[p as usize] = true;
    }
    for &PlaceIdx(p) in &report.token_eliminated_places {
        place_removed[p as usize] = true;
    }

    // Extend self_loop_protected with canonical places of parallel merges.
    for merge in &report.parallel_places {
        self_loop_protected[merge.canonical.0 as usize] = true;
    }

    // LP-based redundant place detection (Colom & Silva 1991).
    let implied = if temporal_projection_candidate {
        Vec::new()
    } else {
        find_redundant_places(
            net,
            &place_removed,
            &report.dead_transitions,
            &self_loop_protected,
        )
    };
    let mut redundant_set = vec![false; num_places];
    report.redundant_places = implied
        .iter()
        .map(|ip| {
            let pidx = PlaceIdx(ip.place as u32);
            place_removed[ip.place] = true;
            redundant_set[ip.place] = true;
            pidx
        })
        .collect();

    // Rule N: keep only proofs for already-removed places.
    report
        .never_disabling_arcs
        .retain(|arc| place_removed[arc.place.0 as usize]);

    // Synchronize report lists with actual removal decisions.
    report
        .constant_places
        .retain(|p| place_removed[p.0 as usize]);
    report
        .isolated_places
        .retain(|p| place_removed[p.0 as usize]);
    report
        .pre_agglomerations
        .retain(|agg| place_removed[agg.place.0 as usize]);
    report
        .post_agglomerations
        .retain(|agg| place_removed[agg.place.0 as usize]);

    // Build reconstruction equations for redundant places (original-net indices).
    let reconstructions: Vec<PlaceReconstruction> = implied
        .iter()
        .map(|ip| PlaceReconstruction {
            place: PlaceIdx(ip.place as u32),
            constant: ip.reconstruction.constant,
            divisor: ip.reconstruction.divisor,
            terms: ip
                .reconstruction
                .terms
                .iter()
                .map(|&(p, w)| (PlaceIdx(p as u32), w))
                .collect(),
        })
        .collect();

    if !report.has_reductions() {
        return None;
    }

    Some(StructuralPlan {
        report,
        place_removed,
        place_agglomerated,
        redundant_set,
        reconstructions,
    })
}
