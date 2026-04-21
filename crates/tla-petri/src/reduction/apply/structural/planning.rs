// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};

use super::super::super::analysis::{
    find_never_disabling_arcs, find_non_decreasing_places, find_parallel_places,
    find_self_loop_arcs, find_sink_transitions, find_source_places,
    find_token_eliminated_places,
};
use super::super::super::analysis_agglomeration::{
    build_place_connectivity, find_rule_r_agglomerations, find_rule_s_agglomerations,
    resolve_rule_r_conflicts_with_rule_s, resolve_rule_s_conflicts,
};
use super::super::super::analysis_cycle::find_token_cycles;
use super::super::super::model::{PlaceReconstruction, TokenCycleMerge, RULE_R_EXPLOSION_LIMITER};
use super::super::super::redundant::find_redundant_places;
use super::super::super::ReductionReport;
use super::super::super::ReductionMode;
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

    // Sink transition detection: pure consumer transitions with no outputs.
    if !temporal_projection_candidate {
        report.sink_transitions =
            find_sink_transitions(net, &report.dead_transitions, protected_places);
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

    // Tapaal Rule R: post-agglomeration. Sound for reachability-equivalent
    // semantics (ExactMarking, QueryRelevantOnly, DeadlockSafe). NOT safe for
    // OneSafe or temporal-projection candidate.
    //
    // Rule S is NOT invoked here because Tapaal Rule S preserves only
    // "atomic-viable" reachability (macro-step semantics), which is strictly
    // weaker than ExactMarking semantics — it can collapse interleaved
    // reachable markings (e.g., the intermediate state of a producer; consumer
    // cycle) into a single fused step. That is unsound for `reduce()` /
    // `reduce_iterative()` callers that rely on ExactMarking. Rule S runs
    // ONLY via `build_structural_plan_for_mode` under `ReductionMode::Reachability`.
    if !temporal_projection_candidate && !one_safe_semantics {
        // See matching mask in `build_structural_plan_for_mode`. Only
        // visibility-relevant places are protected from Rule R;
        // places going away via independent rules do not need protection.
        let mut rule_agg_protected = vec![false; num_places];
        for (p, &ext) in protected_places.iter().enumerate() {
            if ext {
                rule_agg_protected[p] = true;
            }
        }
        for (p, &slp) in self_loop_protected.iter().enumerate() {
            if slp {
                rule_agg_protected[p] = true;
            }
        }
        for merge in &report.parallel_places {
            rule_agg_protected[merge.duplicate.0 as usize] = true;
            rule_agg_protected[merge.canonical.0 as usize] = true;
        }
        for agg in &report.pre_agglomerations {
            rule_agg_protected[agg.place.0 as usize] = true;
        }
        for agg in &report.post_agglomerations {
            rule_agg_protected[agg.place.0 as usize] = true;
        }

        let conn = build_place_connectivity(net, &report.dead_transitions);

        // Rule R (no Rule S here — ExactMarking-safe only).
        let candidates = find_rule_r_agglomerations(
            net,
            &rule_agg_protected,
            &report.dead_transitions,
            &conn,
            RULE_R_EXPLOSION_LIMITER,
        );
        report.rule_r_agglomerations = resolve_rule_r_conflicts_with_rule_s(
            candidates,
            &report.pre_agglomerations,
            &report.post_agglomerations,
            &[],
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
    for agg in &report.rule_r_agglomerations {
        if agg.remove_place {
            place_removed[agg.place.0 as usize] = true;
            place_agglomerated[agg.place.0 as usize] = true;
        }
    }
    for agg in &report.rule_s_agglomerations {
        place_removed[agg.place.0 as usize] = true;
        place_agglomerated[agg.place.0 as usize] = true;
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

/// Build a structural reduction plan gated by a [`ReductionMode`].
///
/// Each rule is included only if the mode's `allows_*` method returns true.
/// This provides fine-grained per-rule gating based on the temporal logic
/// class of the property being checked.
pub(super) fn build_structural_plan_for_mode(
    net: &PetriNet,
    protected_places: &[bool],
    mode: ReductionMode,
) -> Option<StructuralPlan> {
    let mut report = super::super::super::analysis::analyze(net);

    // Gate agglomeration by mode.
    if !mode.allows_agglomeration() {
        report.pre_agglomerations.clear();
        report.post_agglomerations.clear();
    }

    // Gate dead transitions — always allowed (the method always returns true).
    if !mode.allows_dead_transition_removal() {
        report.dead_transitions.clear();
    }

    // Gate constant places.
    if !mode.allows_constant_place_removal() {
        report.constant_places.clear();
    }

    // Gate isolated places.
    if !mode.allows_isolated_place_removal() {
        report.isolated_places.clear();
    }

    // Gate duplicate and dominated transition removal.
    if !mode.allows_duplicate_transition_removal() {
        report.duplicate_transitions.clear();
    }
    if !mode.allows_dominated_transition_removal() {
        report.dominated_transitions.clear();
    }

    // Gate self-loop transition removal.
    if !mode.allows_self_loop_transition_removal() {
        report.self_loop_transitions.clear();
    }

    // Source place detection (Tapaal Rule C): only if the mode allows it.
    if mode.allows_source_place_removal() {
        report.source_places = find_source_places(net, &report.dead_transitions, protected_places);
    }

    // Sink transition detection: pure consumer transitions with no outputs.
    if mode.allows_sink_transition_removal() {
        report.sink_transitions =
            find_sink_transitions(net, &report.dead_transitions, protected_places);
    }

    // Build self-loop protection mask EARLY.
    let num_places = net.num_places();
    let mut self_loop_protected = vec![false; num_places];
    for &TransitionIdx(t) in &report.self_loop_transitions {
        let trans = &net.transitions[t as usize];
        for arc in &trans.inputs {
            self_loop_protected[arc.place.0 as usize] = true;
        }
        for arc in &trans.outputs {
            self_loop_protected[arc.place.0 as usize] = true;
        }
    }
    for (p, &ext) in protected_places.iter().enumerate() {
        if ext {
            self_loop_protected[p] = true;
        }
    }

    // Self-loop arc removal (Tapaal Rule K) and never-disabling arc removal (Rule N).
    if mode.allows_self_loop_arc_removal() {
        report.self_loop_arcs = find_self_loop_arcs(
            net,
            &report.dead_transitions,
            &report.self_loop_transitions,
            protected_places,
        );
    }
    if mode.allows_never_disabling_arc_removal() {
        report.never_disabling_arcs = find_never_disabling_arcs(
            net,
            &report.dead_transitions,
            &report.self_loop_transitions,
            protected_places,
        );
    }

    // Non-decreasing places (Tapaal Rule F).
    if mode.allows_non_decreasing_place_removal() {
        report.non_decreasing_places = find_non_decreasing_places(
            net,
            &report.dead_transitions,
            &self_loop_protected,
            &report.source_places,
        );
    }

    // Parallel places (Tapaal Rule B).
    if mode.allows_parallel_place_merge() {
        report.parallel_places =
            find_parallel_places(net, &report.dead_transitions, &self_loop_protected);
    }

    // Token-eliminated places (only for reachability with query-relevant reduction).
    if mode.allows_token_eliminated_place_removal() {
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

    // Token cycle merges (Tapaal Rule H): only safe for reachability.
    // Detection excludes:
    //   - cycles whose places are query-protected or self-loop protected,
    //   - cycles whose transitions are dead,
    //   - cycles whose transitions collide with transitions scheduled for
    //     other removals (agglomeration, duplicates, self-loops, dominated,
    //     sinks) — processing both rules on the same transition would
    //     double-count removals and confuse place remapping.
    if mode.allows_token_cycle_merge() {
        let cycles = find_token_cycles(net, &report.dead_transitions, &self_loop_protected);

        // Transitions already claimed by other rules.
        let mut trans_claimed = vec![false; net.num_transitions()];
        for agg in &report.pre_agglomerations {
            trans_claimed[agg.transition.0 as usize] = true;
        }
        for agg in &report.post_agglomerations {
            trans_claimed[agg.transition.0 as usize] = true;
        }
        for class in &report.duplicate_transitions {
            trans_claimed[class.canonical.0 as usize] = true;
            for dup in &class.duplicates {
                trans_claimed[dup.0 as usize] = true;
            }
        }
        for &TransitionIdx(t) in &report.self_loop_transitions {
            trans_claimed[t as usize] = true;
        }
        for &TransitionIdx(t) in &report.dominated_transitions {
            trans_claimed[t as usize] = true;
        }
        for &TransitionIdx(t) in &report.sink_transitions {
            trans_claimed[t as usize] = true;
        }

        // Places already claimed by other place-removal rules.
        let mut place_claimed = vec![false; num_places];
        for &PlaceIdx(p) in &report.source_places {
            place_claimed[p as usize] = true;
        }
        for &PlaceIdx(p) in &report.non_decreasing_places {
            place_claimed[p as usize] = true;
        }
        for &PlaceIdx(p) in &report.token_eliminated_places {
            place_claimed[p as usize] = true;
        }
        for merge in &report.parallel_places {
            place_claimed[merge.duplicate.0 as usize] = true;
        }

        // Track places absorbed by earlier cycle merges so overlapping cycles
        // don't double-absorb the same place.
        let mut place_absorbed = vec![false; num_places];

        for cycle in cycles {
            // Skip if any cycle transition is already claimed.
            if cycle
                .transitions
                .iter()
                .any(|&TransitionIdx(t)| trans_claimed[t as usize])
            {
                continue;
            }
            // Skip if any cycle place is already claimed or absorbed.
            if cycle
                .places
                .iter()
                .any(|&PlaceIdx(p)| place_claimed[p as usize] || place_absorbed[p as usize])
            {
                continue;
            }
            if place_claimed[cycle.survivor.0 as usize]
                || place_absorbed[cycle.survivor.0 as usize]
            {
                continue;
            }

            let absorbed: Vec<PlaceIdx> = cycle
                .places
                .iter()
                .copied()
                .filter(|&p| p != cycle.survivor)
                .collect();
            if absorbed.is_empty() {
                continue;
            }

            // Mark absorbed places and cycle transitions claimed so later
            // rules in this same planning pass don't re-use them.
            for &PlaceIdx(p) in &absorbed {
                place_absorbed[p as usize] = true;
            }
            for &TransitionIdx(t) in &cycle.transitions {
                trans_claimed[t as usize] = true;
            }
            // The survivor itself is now protected from other place removals —
            // it carries the aggregate cycle marking.
            place_claimed[cycle.survivor.0 as usize] = true;

            report.token_cycle_merges.push(TokenCycleMerge {
                survivor: cycle.survivor,
                absorbed,
                transitions: cycle.transitions,
            });
        }
    }

    // Tapaal Rule S + Rule R: place-centric agglomerations. Must run after
    // pre/post-agglomeration and token-cycle detection so that conflict
    // resolution can deduplicate against claimed transitions. Rule S runs
    // before Rule R (Tapaal `Reducer.cpp:2893-2896`).
    let rule_s_enabled = mode.allows_rule_s_agglomeration();
    let rule_r_enabled = mode.allows_rule_r_agglomeration();
    if rule_s_enabled || rule_r_enabled {
        // Build agglomeration protected-place mask. The mask gates two checks:
        //   1. `consumer.outputs` / `producer.inputs` writing into a protected
        //      place (would hide post-state visibility from queries).
        //   2. `p_mid` itself being removed.
        //
        // Only query/structural-visibility-relevant places belong here:
        //   - external protected,
        //   - self-loop protected (Rule K/N invariants depend on them),
        //   - parallel-place duplicates and canonicals (Rule B will merge),
        //   - token-cycle survivors and absorbed places (Rule H remaps),
        //   - pre/post-agglomeration source/sink/boundary places (those
        //     rules will modify downstream transitions to inherit or emit
        //     arcs on these places; Rule R/S must not pre-empt).
        //
        // Places already scheduled for removal by *independent* rules
        // (source/non-decreasing/token-eliminated/constant/isolated) are NOT
        // in the mask: they are going away regardless, and fusing
        // transitions that happen to write into them loses nothing.
        let mut rule_agg_protected = vec![false; num_places];
        for (p, &ext) in protected_places.iter().enumerate() {
            if ext {
                rule_agg_protected[p] = true;
            }
        }
        for (p, &slp) in self_loop_protected.iter().enumerate() {
            if slp {
                rule_agg_protected[p] = true;
            }
        }
        for cycle in &report.token_cycle_merges {
            rule_agg_protected[cycle.survivor.0 as usize] = true;
            for &PlaceIdx(p) in &cycle.absorbed {
                rule_agg_protected[p as usize] = true;
            }
        }
        for merge in &report.parallel_places {
            rule_agg_protected[merge.duplicate.0 as usize] = true;
            rule_agg_protected[merge.canonical.0 as usize] = true;
        }
        for agg in &report.pre_agglomerations {
            rule_agg_protected[agg.place.0 as usize] = true;
        }
        for agg in &report.post_agglomerations {
            rule_agg_protected[agg.place.0 as usize] = true;
        }

        // Only effective agglomerations (whose place will actually be removed,
        // i.e. not self-loop protected) conflict with Rule R/Rule S.
        let effective_pre: Vec<_> = report
            .pre_agglomerations
            .iter()
            .filter(|agg| !self_loop_protected[agg.place.0 as usize])
            .cloned()
            .collect();
        let effective_post: Vec<_> = report
            .post_agglomerations
            .iter()
            .filter(|agg| !self_loop_protected[agg.place.0 as usize])
            .cloned()
            .collect();

        let conn = build_place_connectivity(net, &report.dead_transitions);

        if rule_s_enabled {
            let s_candidates = find_rule_s_agglomerations(
                net,
                &rule_agg_protected,
                &report.dead_transitions,
                &conn,
                RULE_R_EXPLOSION_LIMITER,
            );
            report.rule_s_agglomerations =
                resolve_rule_s_conflicts(s_candidates, &effective_pre, &effective_post);
        }

        if rule_r_enabled {
            let candidates = find_rule_r_agglomerations(
                net,
                &rule_agg_protected,
                &report.dead_transitions,
                &conn,
                RULE_R_EXPLOSION_LIMITER,
            );
            report.rule_r_agglomerations = resolve_rule_r_conflicts_with_rule_s(
                candidates,
                &effective_pre,
                &effective_post,
                &report.rule_s_agglomerations,
            );
        }
    }

    // Build removal mask.
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
    for cycle in &report.token_cycle_merges {
        for &PlaceIdx(p) in &cycle.absorbed {
            place_removed[p as usize] = true;
        }
    }
    // Rule R: if remove_place, both place and all consumers are removed.
    for agg in &report.rule_r_agglomerations {
        if agg.remove_place {
            place_removed[agg.place.0 as usize] = true;
            place_agglomerated[agg.place.0 as usize] = true;
        }
    }
    // Rule S: always removes place, all producers, all consumers.
    for agg in &report.rule_s_agglomerations {
        place_removed[agg.place.0 as usize] = true;
        place_agglomerated[agg.place.0 as usize] = true;
    }

    // Extend self_loop_protected with canonical places of parallel merges.
    for merge in &report.parallel_places {
        self_loop_protected[merge.canonical.0 as usize] = true;
    }

    // Protect cycle survivors from LP-redundancy: the survivor carries the
    // aggregate cycle marking and must remain in the reduced net.
    for cycle in &report.token_cycle_merges {
        self_loop_protected[cycle.survivor.0 as usize] = true;
    }

    // LP-based redundant place detection.
    let implied = if mode.allows_redundant_place_removal() {
        find_redundant_places(
            net,
            &place_removed,
            &report.dead_transitions,
            &self_loop_protected,
        )
    } else {
        Vec::new()
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
