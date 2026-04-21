// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod materialize;
mod planning;

use crate::petri_net::PetriNet;

use super::super::model::identity_reduction;
use super::super::ReducedNet;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum StructuralReductionSemantics {
    ExactMarking,
    QueryRelevantOnly,
    /// Deadlock-safe: skip Rule K (self-loop arc removal) because removing
    /// input arcs makes transitions easier to fire, potentially eliminating
    /// deadlocks that exist in the original net.
    DeadlockSafe,
    /// OneSafe-safe: skip source-place elimination, agglomeration, and
    /// non-decreasing place removal because those rules can hide intermediate
    /// token magnitudes that matter to 1-safety. Parallel-place and
    /// LP-redundant removals remain allowed because their original-net
    /// magnitudes stay bounded by a surviving canonical place or a
    /// reconstruction inequality that the caller checks explicitly.
    OneSafe,
    /// Test-only candidate: only dead transitions, constant places, and
    /// isolated places. All other reductions (agglomerations, source places,
    /// LP-redundant, self-loop arcs, parallel places, etc.) are skipped.
    ///
    /// This shrinks the explored state vector, but it does NOT preserve the
    /// CTL/LTL computation graph. Expanded markings can recover atomic formula
    /// labels; they cannot recover the original successor relation once the
    /// reduced graph changes it.
    #[cfg(test)]
    TemporalProjectionCandidate,
}

#[cfg(test)]
fn uses_temporal_projection_candidate(semantics: StructuralReductionSemantics) -> bool {
    semantics == StructuralReductionSemantics::TemporalProjectionCandidate
}

#[cfg(not(test))]
fn uses_temporal_projection_candidate(_semantics: StructuralReductionSemantics) -> bool {
    false
}

/// Apply all safe reductions and produce a smaller net.
///
/// The returned [`ReducedNet`] contains the reduced net and all mappings
/// needed to translate property formulas and interpret results in terms
/// of the original net. Handles constant/isolated place removal, dead
/// transition removal, and pre/post agglomeration.
#[cfg(test)]
#[must_use]
pub(crate) fn reduce(net: &PetriNet) -> ReducedNet {
    reduce_with_protected(net, &[], StructuralReductionSemantics::ExactMarking)
}

/// Apply reductions with protected places excluded from query-sensitive
/// source-place removal and LP redundancy.
///
/// Places marked `true` in `protected_places` remain in the net even if they
/// become pure accumulators. The same mask is also fed into the LP-redundancy
/// guard so query-visible places are never reconstructed via a weaker contract
/// than the caller asked for.
pub(super) fn reduce_with_protected(
    net: &PetriNet,
    protected_places: &[bool],
    semantics: StructuralReductionSemantics,
) -> ReducedNet {
    match planning::build_structural_plan(net, protected_places, semantics) {
        Some(plan) => materialize::build_reduced_net(net, plan),
        None => identity_reduction(net),
    }
}
