// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reduction, slicing, and reduced-net exploration helpers for reachability.

use crate::circulation_loop::reduce_query_local_circulation_loops_fixpoint;
use crate::error::PnmlError;
use crate::explorer::{
    explore_checkpointable_observer, explore_observer, CheckpointableObserver, ExplorationConfig,
    ExplorationResult, ParallelExplorationObserver,
};
use crate::petri_net::PetriNet;
use crate::query_slice::{build_query_local_slice, QuerySlice};
use crate::reduction::{
    apply_final_place_gcd_scaling, reduce_irrelevant,
    reduce_iterative_structural_query_with_protected, reduce_query_guarded,
    ParallelExpandingObserver, ReducedNet,
};
use crate::resolved_predicate::{predicate_reduction_safe, remap_predicate};

use super::observer::ReachabilityObserver;
use super::types::PropertyTracker;

use crate::examinations::query_support::{
    reachability_support, relevance_cone_on_reduced_net, QuerySupport,
};
use crate::examinations::reachability_por::reachability_por_config;

#[derive(Debug, thiserror::Error)]
pub(in crate::examinations) enum ReachabilityExploreError {
    #[error(transparent)]
    Pnml(#[from] PnmlError),
    #[error("checkpoint error: {0}")]
    Checkpoint(#[from] std::io::Error),
}

fn explore_with_optional_checkpoint<O>(
    net: &PetriNet,
    config: &ExplorationConfig,
    observer: &mut O,
) -> Result<ExplorationResult, std::io::Error>
where
    O: ParallelExplorationObserver + CheckpointableObserver + Send,
{
    if config.checkpoint().is_some() {
        explore_checkpointable_observer(net, config, observer)
    } else {
        Ok(explore_observer(net, config, observer))
    }
}

pub(in crate::examinations) fn reduce_reachability_queries(
    net: &PetriNet,
    trackers: &[PropertyTracker],
) -> Result<ReducedNet, PnmlError> {
    let initial_protected = reachability_support(&ReducedNet::identity(net), trackers)
        .map(|support| protected_places_for_prefire(net, &support))
        .unwrap_or_else(|| vec![true; net.num_places()]);
    let reduced = reduce_iterative_structural_query_with_protected(net, &initial_protected)?;
    let mut reduced = reduce_query_guarded(reduced, |r| {
        let support = reachability_support(r, trackers)?;
        Some(protected_places_for_prefire(&r.net, &support))
    })?;

    // Rule I: remove places and transitions provably irrelevant to
    // the query. The closure of the query support identifies the
    // connected component(s) needed; everything else is pruned.
    if let Some(support) = reachability_support(&reduced, trackers) {
        let closure =
            crate::examinations::query_support::closure_on_reduced_net(&reduced.net, support);
        if let Some(step) = reduce_irrelevant(&reduced.net, &closure) {
            let before = reduced.net.num_places() + reduced.net.num_transitions();
            reduced = reduced.compose(&step)?;
            let after = reduced.net.num_places() + reduced.net.num_transitions();
            if after < before {
                eprintln!(
                    "Rule I pruned {} places+transitions ({} → {})",
                    before - after,
                    before,
                    after,
                );
            }
        }
    }

    apply_final_place_gcd_scaling(&mut reduced)?;
    Ok(reduced)
}

pub(in crate::examinations) fn build_reachability_slice(
    reduced: &ReducedNet,
    trackers: &[PropertyTracker],
) -> Option<(QuerySlice, Vec<PropertyTracker>)> {
    let support = reachability_support(reduced, trackers)?;
    let has_transition_support = support.transitions.iter().any(|&t| t);
    let protected_seed_places = support.places.clone();
    let cone = relevance_cone_on_reduced_net(&reduced.net, support);
    let slice = build_query_local_slice(&reduced.net, &cone)?;
    // Rule H: contract circulation loops inside the query-local slice.
    // Only for place-based queries (no fireability transition references).
    let slice = if !has_transition_support {
        reduce_query_local_circulation_loops_fixpoint(slice.clone(), &protected_seed_places)
            .unwrap_or(slice)
    } else {
        slice
    };
    let place_map = slice.compose_place_map(&reduced.place_map);
    let trans_map = slice.compose_transition_map(&reduced.transition_map);

    let remapped_trackers = trackers
        .iter()
        .cloned()
        .map(|mut tracker| {
            if tracker.verdict.is_none() {
                tracker.predicate = remap_predicate(&tracker.predicate, &place_map, &trans_map)?;
            }
            Some(tracker)
        })
        .collect::<Option<Vec<_>>>()?;

    Some((slice, remapped_trackers))
}

pub(crate) fn protected_places_for_prefire(net: &PetriNet, support: &QuerySupport) -> Vec<bool> {
    let mut protected = support.places.clone();
    for (idx, targeted) in support.transitions.iter().enumerate() {
        if !*targeted {
            continue;
        }
        for arc in net.transitions[idx]
            .inputs
            .iter()
            .chain(net.transitions[idx].outputs.iter())
        {
            protected[arc.place.0 as usize] = true;
        }
    }
    protected
}

pub(in crate::examinations) fn explore_reachability_on_reduced_net(
    net: &PetriNet,
    reduced: &ReducedNet,
    trackers: Vec<PropertyTracker>,
    config: &ExplorationConfig,
) -> Result<(ExplorationResult, Vec<PropertyTracker>), ReachabilityExploreError> {
    let por_config = reachability_por_config(reduced, &trackers, config);
    let mut observer = ReachabilityObserver::from_trackers(net, trackers);
    let result = {
        let mut expanding = ParallelExpandingObserver::new(reduced, &mut observer);
        let result = explore_with_optional_checkpoint(&reduced.net, &por_config, &mut expanding)?;
        if let Some(error) = expanding.take_error() {
            return Err(error.into());
        }
        result
    };
    Ok((result, observer.into_trackers()))
}

pub(in crate::examinations) fn explore_reachability_on_slice(
    slice: &QuerySlice,
    trackers: Vec<PropertyTracker>,
    config: &ExplorationConfig,
) -> Result<(ExplorationResult, Vec<PropertyTracker>), ReachabilityExploreError> {
    let reduced = ReducedNet::identity(&slice.net);
    let por_config = reachability_por_config(&reduced, &trackers, config);
    let mut observer = ReachabilityObserver::from_trackers(&slice.net, trackers);
    let result = explore_with_optional_checkpoint(&slice.net, &por_config, &mut observer)?;
    Ok((result, observer.into_trackers()))
}

/// Check if all predicates are safe after reduction (referenced entities survived).
pub(in crate::examinations) fn all_predicates_reduction_safe(
    net: &PetriNet,
    reduced: &ReducedNet,
    trackers: &[PropertyTracker],
) -> bool {
    trackers.iter().all(|tracker| {
        tracker.verdict.is_some()
            || predicate_reduction_safe(&tracker.predicate, net, &reduced.transition_map)
    })
}
