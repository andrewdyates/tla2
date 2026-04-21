// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::petri_net::{PlaceIdx, TransitionIdx};

/// Reconstruction equation for a redundant place removed via P-invariant analysis.
///
/// `m(place) = (constant - sum(weight_i * m(term_i))) / divisor`
///
/// All place indices refer to the **original** (pre-reduction) net.
/// Division is exact for all reachable markings (guaranteed by the
/// P-invariant property y^T · m = constant).
#[derive(Debug, Clone)]
pub(crate) struct PlaceReconstruction {
    /// Original index of the reconstructed place.
    pub place: PlaceIdx,
    /// Conserved quantity (y^T · m₀).
    pub constant: u64,
    /// Invariant weight of the reconstructed place (always > 0).
    pub divisor: u64,
    /// (original_place_index, invariant_weight) for each kept place in the support.
    pub terms: Vec<(PlaceIdx, u64)>,
}

/// Pre-agglomeration: source transition t has exactly one output place p,
/// p has exactly one input transition (t), p has zero initial tokens,
/// and every successor of p reads exactly one token from p.
/// Effect: merge t's inputs into each successor, remove t and p.
#[derive(Debug, Clone)]
pub(crate) struct PreAgglomeration {
    /// The source transition to be removed.
    pub transition: TransitionIdx,
    /// The intermediate place to be removed (t's sole output).
    pub place: PlaceIdx,
    /// Successors that consume from place (will be modified to include t's inputs).
    pub successors: Vec<TransitionIdx>,
}

/// Post-agglomeration: sink transition t has exactly one input place p,
/// p has exactly one output transition (t), p has zero initial tokens,
/// and every predecessor of p produces exactly one token into p.
/// Effect: merge t's outputs into each predecessor, remove t and p.
#[derive(Debug, Clone)]
pub(crate) struct PostAgglomeration {
    /// The sink transition to be removed.
    pub transition: TransitionIdx,
    /// The intermediate place to be removed (t's sole input).
    pub place: PlaceIdx,
    /// Predecessors that produce into place (will be modified to include t's outputs).
    pub predecessors: Vec<TransitionIdx>,
}

/// A self-loop arc pair on a non-self-loop transition: the transition both
/// consumes from and produces to the same place with equal weight, so the net
/// effect on that place is zero. Removing the pair simplifies the transition
/// without changing the marking (Tapaal Rule K).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SelfLoopArc {
    pub transition: TransitionIdx,
    pub place: PlaceIdx,
    pub weight: u64,
}

/// Proof that an input place always carries at least a fixed token lower bound.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NeverDisablingProof {
    /// A P-invariant plus structural upper bounds on the other support places
    /// proves this place can never drop below `lower_bound`.
    PInvariant {
        invariant_idx: usize,
        lower_bound: u64,
    },
}

impl NeverDisablingProof {
    #[must_use]
    pub(crate) fn lower_bound(&self) -> u64 {
        match self {
            Self::PInvariant { lower_bound, .. } => *lower_bound,
        }
    }
}

/// An input arc that can be removed because the place always has enough tokens.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NeverDisablingArc {
    pub transition: TransitionIdx,
    pub place: PlaceIdx,
    pub weight: u64,
    pub proof: NeverDisablingProof,
}

/// Two places with identical connectivity and initial marking (Tapaal Rule B).
/// The duplicate is removed; property references are rewritten to canonical.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ParallelPlaceMerge {
    pub canonical: PlaceIdx,
    pub duplicate: PlaceIdx,
}

/// Structurally identical live transitions that can be merged into one survivor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DuplicateTransitionClass {
    /// Original index of the surviving transition.
    pub canonical: TransitionIdx,
    /// Original indices of removed duplicates that alias to the canonical survivor.
    pub duplicates: Vec<TransitionIdx>,
}

/// Result of structural analysis: which places and transitions can be removed.
#[derive(Debug, Clone, Default)]
pub(crate) struct ReductionReport {
    /// Places whose token count never changes under any firing sequence.
    pub constant_places: Vec<PlaceIdx>,
    /// Producer-only places removed as unobservable accumulators (Tapaal Rule C).
    pub source_places: Vec<PlaceIdx>,
    /// Transitions that can never fire from any reachable marking.
    pub dead_transitions: Vec<TransitionIdx>,
    /// Places with no connected arcs at all.
    pub isolated_places: Vec<PlaceIdx>,
    /// Pre-agglomerations: source transitions merged into their successors.
    pub pre_agglomerations: Vec<PreAgglomeration>,
    /// Post-agglomerations: sink transitions merged into their predecessors.
    pub post_agglomerations: Vec<PostAgglomeration>,
    /// Structurally duplicate live transitions collapsed into one survivor.
    pub duplicate_transitions: Vec<DuplicateTransitionClass>,
    /// Transitions with zero net effect on every place (firing is a no-op).
    pub self_loop_transitions: Vec<TransitionIdx>,
    /// Transitions dominated by another with identical net effect but weaker
    /// precondition (Tapaal Rule L). The dominator is strictly easier to enable.
    pub dominated_transitions: Vec<TransitionIdx>,
    /// Self-loop arc pairs to strip from transitions (Tapaal Rule K).
    /// Each entry identifies one input+output arc pair with equal weight
    /// on a non-self-loop transition. The transition survives with fewer arcs.
    pub self_loop_arcs: Vec<SelfLoopArc>,
    /// Input arcs that never constrain their transitions because the place
    /// has a proven structural token lower bound (Tapaal Rule N).
    pub never_disabling_arcs: Vec<NeverDisablingArc>,
    /// Query-unobserved places removed because every live consumer arc already
    /// has a Rule N proof, so their exact token values are semantically irrelevant.
    pub token_eliminated_places: Vec<PlaceIdx>,
    /// LP-redundant places whose values are reconstructable from P-invariants.
    pub redundant_places: Vec<PlaceIdx>,
    /// Parallel places merged into a canonical representative (Tapaal Rule B).
    pub parallel_places: Vec<ParallelPlaceMerge>,
    /// Non-decreasing places removed as monotonic accumulators (Tapaal Rule F).
    pub non_decreasing_places: Vec<PlaceIdx>,
}

impl ReductionReport {
    /// Total number of places that will be removed from the state vector.
    #[must_use]
    #[cfg_attr(not(test), allow(dead_code))]
    pub fn places_removed(&self) -> usize {
        // Constant, isolated, and agglomerated places may overlap. Deduplicate.
        let mut removed = vec![false; self.max_place_idx() + 1];
        for &PlaceIdx(p) in &self.constant_places {
            removed[p as usize] = true;
        }
        for &PlaceIdx(p) in &self.source_places {
            removed[p as usize] = true;
        }
        for &PlaceIdx(p) in &self.isolated_places {
            removed[p as usize] = true;
        }
        for agg in &self.pre_agglomerations {
            removed[agg.place.0 as usize] = true;
        }
        for agg in &self.post_agglomerations {
            removed[agg.place.0 as usize] = true;
        }
        for &PlaceIdx(p) in &self.redundant_places {
            removed[p as usize] = true;
        }
        for &PlaceIdx(p) in &self.token_eliminated_places {
            removed[p as usize] = true;
        }
        for merge in &self.parallel_places {
            removed[merge.duplicate.0 as usize] = true;
        }
        for &PlaceIdx(p) in &self.non_decreasing_places {
            removed[p as usize] = true;
        }
        removed.iter().filter(|&&r| r).count()
    }

    /// Total number of transitions removed (dead + agglomerated + duplicates).
    #[must_use]
    #[cfg_attr(not(test), allow(dead_code))]
    pub fn transitions_removed(&self) -> usize {
        let mut removed = vec![false; self.max_transition_idx() + 1];
        for &TransitionIdx(t) in &self.dead_transitions {
            removed[t as usize] = true;
        }
        for agg in &self.pre_agglomerations {
            removed[agg.transition.0 as usize] = true;
        }
        for agg in &self.post_agglomerations {
            removed[agg.transition.0 as usize] = true;
        }
        for class in &self.duplicate_transitions {
            for duplicate in &class.duplicates {
                removed[duplicate.0 as usize] = true;
            }
        }
        for &TransitionIdx(t) in &self.self_loop_transitions {
            removed[t as usize] = true;
        }
        for &TransitionIdx(t) in &self.dominated_transitions {
            removed[t as usize] = true;
        }
        removed.iter().filter(|&&r| r).count()
    }

    /// Whether any reductions were found.
    #[must_use]
    pub fn has_reductions(&self) -> bool {
        !self.constant_places.is_empty()
            || !self.source_places.is_empty()
            || !self.dead_transitions.is_empty()
            || !self.isolated_places.is_empty()
            || !self.pre_agglomerations.is_empty()
            || !self.post_agglomerations.is_empty()
            || !self.duplicate_transitions.is_empty()
            || !self.self_loop_transitions.is_empty()
            || !self.dominated_transitions.is_empty()
            || !self.self_loop_arcs.is_empty()
            || !self.never_disabling_arcs.is_empty()
            || !self.token_eliminated_places.is_empty()
            || !self.redundant_places.is_empty()
            || !self.parallel_places.is_empty()
            || !self.non_decreasing_places.is_empty()
    }

    #[cfg_attr(not(test), allow(dead_code))]
    fn max_place_idx(&self) -> usize {
        let max_const = self.constant_places.iter().map(|p| p.0 as usize).max();
        let max_source = self.source_places.iter().map(|p| p.0 as usize).max();
        let max_iso = self.isolated_places.iter().map(|p| p.0 as usize).max();
        let max_pre = self
            .pre_agglomerations
            .iter()
            .map(|a| a.place.0 as usize)
            .max();
        let max_post = self
            .post_agglomerations
            .iter()
            .map(|a| a.place.0 as usize)
            .max();
        let max_redundant = self.redundant_places.iter().map(|p| p.0 as usize).max();
        let max_token_eliminated = self
            .token_eliminated_places
            .iter()
            .map(|p| p.0 as usize)
            .max();
        let max_parallel = self
            .parallel_places
            .iter()
            .flat_map(|m| [m.canonical.0 as usize, m.duplicate.0 as usize])
            .max();
        let max_non_dec = self
            .non_decreasing_places
            .iter()
            .map(|p| p.0 as usize)
            .max();
        max_const
            .into_iter()
            .chain(max_source)
            .chain(max_iso)
            .chain(max_pre)
            .chain(max_post)
            .chain(max_redundant)
            .chain(max_token_eliminated)
            .chain(max_parallel)
            .chain(max_non_dec)
            .max()
            .unwrap_or(0)
    }

    #[cfg_attr(not(test), allow(dead_code))]
    fn max_transition_idx(&self) -> usize {
        let max_dead = self.dead_transitions.iter().map(|t| t.0 as usize).max();
        let max_pre = self
            .pre_agglomerations
            .iter()
            .map(|a| a.transition.0 as usize)
            .max();
        let max_post = self
            .post_agglomerations
            .iter()
            .map(|a| a.transition.0 as usize)
            .max();
        let max_duplicate = self
            .duplicate_transitions
            .iter()
            .flat_map(|class| {
                std::iter::once(class.canonical.0 as usize).chain(
                    class
                        .duplicates
                        .iter()
                        .map(|transition| transition.0 as usize),
                )
            })
            .max();
        let max_self_loop = self
            .self_loop_transitions
            .iter()
            .map(|t| t.0 as usize)
            .max();
        let max_dominated = self
            .dominated_transitions
            .iter()
            .map(|t| t.0 as usize)
            .max();
        max_dead
            .into_iter()
            .chain(max_pre)
            .chain(max_post)
            .chain(max_duplicate)
            .chain(max_self_loop)
            .chain(max_dominated)
            .max()
            .unwrap_or(0)
    }
}
