// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::error::PnmlError;
use crate::petri_net::{PetriNet, TransitionIdx};

use super::super::gcd_scale::apply_final_place_gcd_scaling;
use super::super::ReducedNet;
use super::prefire::apply_query_guarded_prefire;
use super::structural::{reduce_with_protected, StructuralReductionSemantics};

/// Apply query-guarded prefire and structural reduction in a fixpoint loop.
///
/// After each prefire pass, re-runs structural reduction to catch newly-dead
/// transitions, isolated places, and cascade simplifications exposed by the
/// marking changes. Repeats until neither prefire nor structural reduction
/// makes progress.
///
/// The `protected_places_for` callback receives the current [`ReducedNet`] and
/// returns a protected-places mask for prefire, or `None` to skip prefire
/// entirely (e.g., when all queries are already resolved).
///
/// Does **not** apply GCD scaling. Callers should apply
/// [`apply_final_place_gcd_scaling`](super::super::gcd_scale::apply_final_place_gcd_scaling)
/// once after this function returns.
pub(crate) fn reduce_query_guarded<F>(
    reduced: ReducedNet,
    protected_places_for: F,
) -> Result<ReducedNet, PnmlError>
where
    F: Fn(&ReducedNet) -> Option<Vec<bool>>,
{
    let mut current = reduced;
    // Prefire chains have length at most num_transitions (each transition
    // prefires at most once before its inputs are exhausted). Cycle
    // transitions can oscillate tokens indefinitely without enabling new
    // structural reductions, so we cap consecutive prefire-without-reduction
    // rounds to prevent infinite loops.
    let mut prefire_only_rounds: usize = 0;
    loop {
        let Some(protected) = protected_places_for(&current) else {
            return Ok(current);
        };

        let prefired = apply_query_guarded_prefire(&mut current, &protected)?;

        let step = reduce_iterative_structural_query_with_protected(&current.net, &protected)?;
        let reduced_more = step.report.has_reductions();

        if reduced_more {
            current = current.compose(&step)?;
            prefire_only_rounds = 0;
        }

        if !prefired && !reduced_more {
            return Ok(current);
        }

        if prefired && !reduced_more {
            prefire_only_rounds += 1;
            if prefire_only_rounds > current.net.num_transitions() {
                return Ok(current);
            }
        }
    }
}

/// Apply reductions until a full pass finds no new reducible structure.
///
/// Self-loop-touching places from earlier rounds are propagated as
/// LP-redundancy protection to prevent soundness bugs where
/// `restore_self_loops` cannot remap arcs for places removed as redundant.
///
/// **Quarantined (#1503):** unsound for GlobalProperties exams (QuasiLiveness,
/// Liveness, StableMarking) — agglomeration suppresses real firing behavior.
/// Retained for re-enablement once a sound reduction contract is validated.
#[allow(dead_code)]
pub(crate) fn reduce_iterative_structural(net: &PetriNet) -> Result<ReducedNet, PnmlError> {
    reduce_iterative_structural_with_protected(net, &[])
}

#[allow(dead_code)]
pub(crate) fn reduce_iterative_structural_with_protected(
    net: &PetriNet,
    base_protected: &[bool],
) -> Result<ReducedNet, PnmlError> {
    reduce_iterative_structural_with_semantics(
        net,
        base_protected,
        StructuralReductionSemantics::ExactMarking,
    )
}

/// Structural reduction that keeps only rules sound for OneSafe.
///
/// Source-place elimination, agglomeration, and non-decreasing place removal
/// can hide original-net token magnitudes, so this lane keeps the
/// deadlock-safe enabling contract while excluding those magnitude-changing
/// rules.
pub(crate) fn reduce_iterative_structural_one_safe(
    net: &PetriNet,
) -> Result<ReducedNet, PnmlError> {
    reduce_iterative_structural_with_semantics(net, &[], StructuralReductionSemantics::OneSafe)
}

pub(crate) fn reduce_iterative_structural_query_with_protected(
    net: &PetriNet,
    base_protected: &[bool],
) -> Result<ReducedNet, PnmlError> {
    reduce_iterative_structural_with_semantics(
        net,
        base_protected,
        StructuralReductionSemantics::QueryRelevantOnly,
    )
}

/// Deadlock-safe structural reduction with query-protected places.
///
/// Skips Rule K (self-loop arc removal) and Rule N (never-disabling arcs)
/// which change transition enabling conditions. Used in tests to verify
/// that CTL/LTL wrong answers come from structural reduction (not slicing).
#[cfg(test)]
pub(crate) fn reduce_iterative_structural_deadlock_safe_with_protected(
    net: &PetriNet,
    base_protected: &[bool],
) -> Result<ReducedNet, PnmlError> {
    reduce_iterative_structural_with_semantics(
        net,
        base_protected,
        StructuralReductionSemantics::DeadlockSafe,
    )
}

/// Test-only dead/constant/isolated structural reduction candidate.
///
/// Keep this lane quarantined while production CTL/LTL stays on
/// `ReducedNet::identity(net)`. IBM5964 parity coverage protects against the
/// candidate silently widening again, but that benchmark alone is not a proof
/// of general CTL/LTL safety.
#[cfg(test)]
pub(crate) fn reduce_iterative_temporal_projection_candidate(
    net: &PetriNet,
) -> Result<ReducedNet, PnmlError> {
    reduce_iterative_structural_with_semantics(
        net,
        &[],
        StructuralReductionSemantics::TemporalProjectionCandidate,
    )
}

fn reduce_iterative_structural_with_semantics(
    net: &PetriNet,
    base_protected: &[bool],
    semantics: StructuralReductionSemantics,
) -> Result<ReducedNet, PnmlError> {
    assert!(
        base_protected.is_empty() || base_protected.len() == net.num_places(),
        "protected place mask must match net place count"
    );

    let mut current = net.clone();
    let mut combined = ReducedNet::identity(net);

    loop {
        let np_current = current.num_places();
        let mut round_protected = vec![false; np_current];
        for (orig_place, &protected) in base_protected.iter().enumerate() {
            if !protected {
                continue;
            }
            if let Some(current_place) = combined.place_map[orig_place] {
                round_protected[current_place.0 as usize] = true;
            }
        }

        // Map accumulated self-loop places to current-net coordinates.
        // After round N, combined.report.self_loop_transitions contains
        // all self-loops from rounds 1..N in original-net indices.
        // We map their arc places through combined.place_map to get
        // current-net indices, then pass them as extra protection.
        for &TransitionIdx(t) in &combined.report.self_loop_transitions {
            let orig_trans = &net.transitions[t as usize];
            for arc in orig_trans.inputs.iter().chain(orig_trans.outputs.iter()) {
                if let Some(cur_p) = combined.place_map[arc.place.0 as usize] {
                    round_protected[cur_p.0 as usize] = true;
                }
            }
        }

        let step = reduce_with_protected(&current, &round_protected, semantics);
        if !step.report.has_reductions() {
            return Ok(combined);
        }

        current = step.net.clone();
        combined = combined.compose(&step)?;
    }
}

/// Apply structural reductions and then normalize surviving place scales once.
#[allow(dead_code)]
pub(crate) fn reduce_iterative(net: &PetriNet) -> Result<ReducedNet, PnmlError> {
    let mut combined = reduce_iterative_structural(net)?;
    apply_final_place_gcd_scaling(&mut combined)?;
    Ok(combined)
}

/// Deadlock-safe reduction: skips Rule K (self-loop arcs) and Rule N
/// (never-disabling arcs). Removing self-loop input arcs makes transitions
/// easier to fire, potentially eliminating deadlocks. Removing never-disabling
/// output arcs can starve downstream transitions, also affecting deadlocks.
///
/// **Quarantined (#1506):** currently unsound for deadlock analysis on nets
/// like IOTPpurchase-PT (agglomeration/source-place elimination introduces
/// spurious deadlocks). Retained as infrastructure for future deadlock-safe
/// reduction contract validation.
#[allow(dead_code)]
pub(crate) fn reduce_iterative_deadlock_safe(net: &PetriNet) -> Result<ReducedNet, PnmlError> {
    let mut combined = reduce_iterative_structural_with_semantics(
        net,
        &[],
        StructuralReductionSemantics::DeadlockSafe,
    )?;
    apply_final_place_gcd_scaling(&mut combined)?;
    Ok(combined)
}
