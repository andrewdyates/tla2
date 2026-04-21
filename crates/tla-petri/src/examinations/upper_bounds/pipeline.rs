// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! UpperBounds execution pipeline: reduction, slicing, and exploration orchestration.

use crate::circulation_loop::reduce_query_local_circulation_loops_fixpoint;
use crate::error::PnmlError;
use crate::explorer::{explore_observer, ExplorationConfig};
use crate::model::PropertyAliases;
use crate::petri_net::{PetriNet, PlaceIdx};
use crate::property_xml::Property;
use crate::query_slice::{build_query_local_slice, QuerySlice};
#[cfg(test)]
use crate::reduction::apply_query_guarded_prefire;
use crate::reduction::{
    apply_final_place_gcd_scaling, reduce_iterative_structural_query_with_protected,
    reduce_query_guarded, ParallelExpandingObserver, ReducedNet,
};
use crate::stubborn::PorStrategy;

use super::model::{
    assemble_upper_bounds_results, prepare_upper_bounds_properties_with_aliases,
    structural_query_bound, BoundTracker, PreparedUpperBoundProperty,
};
use super::observer::UpperBoundsObserver;

use crate::examinations::query_support::{
    relevance_cone_on_reduced_net, upper_bounds_support, visible_transitions_for_support,
};

/// Build an `ExplorationConfig` with POR for UpperBounds.
///
/// Visible transitions = transitions whose input or output arcs touch any
/// query place (after reduction mapping). When query places span the entire
/// net, `compute_stubborn_set` detects all-visible and returns `None`,
/// so the overhead is a single boolean scan per state.
fn upper_bounds_por_config(
    reduced: &ReducedNet,
    trackers: &[BoundTracker],
    config: &ExplorationConfig,
) -> ExplorationConfig {
    let base = config.clone();

    let unresolved_place_sets: Vec<Vec<PlaceIdx>> = trackers
        .iter()
        .filter(|tracker| !tracker.is_structurally_resolved())
        .map(|tracker| tracker.place_indices.clone())
        .collect();

    match upper_bounds_support(reduced, &unresolved_place_sets)
        .and_then(|support| visible_transitions_for_support(&reduced.net, &support))
    {
        Some(visible) => base.with_por(PorStrategy::SafetyPreserving { visible }),
        None => base,
    }
}

#[cfg(test)]
pub(super) fn apply_upper_bounds_prefire(
    reduced: &mut ReducedNet,
    trackers: &[BoundTracker],
) -> Result<bool, PnmlError> {
    let unresolved_place_sets: Vec<Vec<PlaceIdx>> = trackers
        .iter()
        .filter(|tracker| !tracker.is_structurally_resolved())
        .map(|tracker| tracker.place_indices.clone())
        .collect();
    if unresolved_place_sets.is_empty() {
        return Ok(false);
    }

    match upper_bounds_support(reduced, &unresolved_place_sets) {
        Some(support) => apply_query_guarded_prefire(reduced, &support.places),
        None => Ok(false),
    }
}

pub(super) fn build_upper_bounds_slice(
    reduced: &ReducedNet,
    trackers: &[BoundTracker],
) -> Option<(QuerySlice, Vec<usize>, Vec<BoundTracker>)> {
    let unresolved_slots: Vec<usize> = trackers
        .iter()
        .enumerate()
        .filter_map(|(slot, tracker)| (!tracker.is_structurally_resolved()).then_some(slot))
        .collect();
    if unresolved_slots.is_empty() {
        return None;
    }

    let unresolved_place_sets: Vec<Vec<PlaceIdx>> = unresolved_slots
        .iter()
        .map(|&slot| trackers[slot].place_indices.clone())
        .collect();
    let support = upper_bounds_support(reduced, &unresolved_place_sets)?;
    let protected_seed_places = support.places.clone();
    let cone = relevance_cone_on_reduced_net(&reduced.net, support);
    let slice = build_query_local_slice(&reduced.net, &cone)?;
    // Rule H: contract circulation loops inside the query-local slice.
    // UpperBounds is place-only, so this is always safe.
    let slice =
        reduce_query_local_circulation_loops_fixpoint(slice.clone(), &protected_seed_places)
            .unwrap_or(slice);
    let original_to_slice = slice.compose_place_map(&reduced.place_map);

    let remapped_trackers = unresolved_slots
        .iter()
        .map(|&slot| {
            let mut tracker = trackers[slot].clone();
            tracker.place_indices = tracker
                .place_indices
                .iter()
                .map(|place| original_to_slice[place.0 as usize])
                .collect::<Option<Vec<_>>>()?;
            Some(tracker)
        })
        .collect::<Option<Vec<_>>>()?;

    Some((slice, unresolved_slots, remapped_trackers))
}

pub(super) fn explore_upper_bounds_on_reduced_net(
    reduced: &ReducedNet,
    trackers: Vec<BoundTracker>,
    config: &ExplorationConfig,
) -> Result<(crate::explorer::ExplorationResult, Vec<BoundTracker>), PnmlError> {
    let por_config = upper_bounds_por_config(reduced, &trackers, config);
    let mut observer = UpperBoundsObserver::new(trackers);
    let result = {
        let mut expanding = ParallelExpandingObserver::new(reduced, &mut observer);
        let result = explore_observer(&reduced.net, &por_config, &mut expanding);
        if let Some(error) = expanding.take_error() {
            return Err(error);
        }
        result
    };
    Ok((result, observer.into_trackers()))
}

fn explore_upper_bounds_on_slice(
    slice: &QuerySlice,
    trackers: Vec<BoundTracker>,
    config: &ExplorationConfig,
) -> (crate::explorer::ExplorationResult, Vec<BoundTracker>) {
    let reduced = ReducedNet::identity(&slice.net);
    let por_config = upper_bounds_por_config(&reduced, &trackers, config);
    let mut observer = UpperBoundsObserver::new(trackers);
    let result = explore_observer(&slice.net, &por_config, &mut observer);
    (result, observer.into_trackers())
}

/// Check UpperBounds properties with fail-closed unresolved-place handling.
///
/// Returns `Some(bound)` for valid properties after completed exploration and
/// `None` for invalid properties or incomplete exploration.
#[cfg(test)]
pub(crate) fn check_upper_bounds_properties(
    net: &PetriNet,
    properties: &[Property],
    config: &ExplorationConfig,
) -> Vec<(String, Option<u64>)> {
    let aliases = PropertyAliases::identity(net);
    check_upper_bounds_properties_with_aliases(net, properties, &aliases, config)
}

pub(crate) fn check_upper_bounds_properties_with_aliases(
    net: &PetriNet,
    properties: &[Property],
    aliases: &PropertyAliases,
    config: &ExplorationConfig,
) -> Vec<(String, Option<u64>)> {
    let cannot_compute_results = |error: &PnmlError| {
        eprintln!("UpperBounds: CANNOT_COMPUTE ({error})");
        properties
            .iter()
            .map(|property| (property.id.clone(), None))
            .collect()
    };

    let (prepared, mut trackers) =
        prepare_upper_bounds_properties_with_aliases(properties, aliases);
    if trackers.is_empty() {
        return prepared
            .into_iter()
            .map(|property| match property {
                PreparedUpperBoundProperty::Invalid { id } => (id, None),
                PreparedUpperBoundProperty::Valid { .. } => unreachable!(),
            })
            .collect();
    }

    // Compute P-invariant structural bounds on the original net.
    let invariants = crate::invariant::compute_p_invariants(net);
    let mut structural_count = 0usize;
    for tracker in &mut trackers {
        tracker.structural_bound = structural_query_bound(&invariants, &tracker.place_indices);
        // Seed max_bound with the initial marking sum.
        let initial_sum: u64 = tracker
            .place_indices
            .iter()
            .map(|p| net.initial_marking[p.0 as usize])
            .sum();
        tracker.max_bound = initial_sum;
        if tracker.is_structurally_resolved() {
            structural_count += 1;
        }
    }

    // Tighten bounds via LP state equation relaxation. LP bounds are at
    // least as tight as P-invariant bounds (P-invariants are the LP dual).
    let mut lp_count = 0usize;
    for tracker in &mut trackers {
        if tracker.is_structurally_resolved() {
            continue;
        }
        if let Some(bound) = crate::lp_state_equation::lp_upper_bound(net, &tracker.place_indices) {
            tracker.lp_bound = Some(bound);
            lp_count += 1;
            if tracker.is_structurally_resolved() {
                structural_count += 1;
            }
        }
    }
    if lp_count > 0 {
        eprintln!(
            "UpperBounds: LP tightened bounds on {lp_count}/{} properties",
            trackers.len(),
        );
    }

    // If all properties are resolved by structural bounds alone, skip BFS.
    if structural_count == trackers.len() {
        eprintln!(
            "UpperBounds: all {} properties resolved structurally",
            trackers.len(),
        );
        return assemble_upper_bounds_results(&prepared, &trackers, true);
    }

    if structural_count > 0 {
        eprintln!(
            "UpperBounds: {structural_count}/{} properties resolved structurally, \
             exploring state space for remaining",
            trackers.len(),
        );
    }

    // Explore the reduced net with an expanding observer so that the
    // UpperBoundsObserver receives expanded (original-index) markings.
    // Constant/isolated places get their fixed values in the expanded
    // marking, so bounds are correctly computed over the full net.
    let unresolved_place_sets: Vec<Vec<PlaceIdx>> = trackers
        .iter()
        .filter(|tracker| !tracker.is_structurally_resolved())
        .map(|tracker| tracker.place_indices.clone())
        .collect();
    let initial_protected = if unresolved_place_sets.is_empty() {
        vec![false; net.num_places()]
    } else {
        upper_bounds_support(&ReducedNet::identity(net), &unresolved_place_sets)
            .map(|support| support.places)
            .unwrap_or_else(|| vec![true; net.num_places()])
    };
    let reduced = match reduce_iterative_structural_query_with_protected(net, &initial_protected) {
        Ok(reduced) => reduced,
        Err(error) => return cannot_compute_results(&error),
    };
    let mut reduced = match reduce_query_guarded(reduced, |r| {
        let unresolved_place_sets: Vec<Vec<PlaceIdx>> = trackers
            .iter()
            .filter(|tracker| !tracker.is_structurally_resolved())
            .map(|tracker| tracker.place_indices.clone())
            .collect();
        if unresolved_place_sets.is_empty() {
            return None;
        }
        let support = upper_bounds_support(r, &unresolved_place_sets)?;
        Some(support.places)
    }) {
        Ok(reduced) => reduced,
        Err(error) => return cannot_compute_results(&error),
    };
    if let Err(error) = apply_final_place_gcd_scaling(&mut reduced) {
        return cannot_compute_results(&error);
    }
    let config = config.refitted_for_net(&reduced.net);
    let (completed, trackers) = if let Some((slice, unresolved_slots, slice_trackers)) =
        build_upper_bounds_slice(&reduced, &trackers)
    {
        let (result, slice_trackers) =
            explore_upper_bounds_on_slice(&slice, slice_trackers, &config);
        for (slot, tracker) in unresolved_slots.into_iter().zip(slice_trackers) {
            trackers[slot].max_bound = tracker.max_bound;
        }
        (result.completed, trackers)
    } else {
        match explore_upper_bounds_on_reduced_net(&reduced, trackers, &config) {
            Ok((result, trackers)) => (result.completed, trackers),
            Err(error) => return cannot_compute_results(&error),
        }
    };

    // Safety net: if BFS completed on the reduced net but some trackers have
    // max_bound < lp_bound, the reduction may have pruned reachable markings
    // needed to achieve the true maximum. Fall back to identity-net BFS for
    // these formulas. (#1501: IBM5964 UpperBounds-14 returns 2 instead of 3
    // because structural reduction removes a producer transition.)
    if completed {
        let has_lp_gap = trackers.iter().any(|t| {
            t.lp_bound
                .is_some_and(|lp| t.max_bound < lp && !t.is_structurally_resolved())
        });
        if has_lp_gap {
            let identity_config = config.refitted_for_net(net);
            let identity = ReducedNet::identity(net);
            match explore_upper_bounds_on_reduced_net(&identity, trackers.clone(), &identity_config)
            {
                Ok((identity_result, identity_trackers)) => {
                    eprintln!(
                        "UpperBounds: LP-gap fallback on identity net (completed={})",
                        identity_result.completed,
                    );
                    return assemble_upper_bounds_results(
                        &prepared,
                        &identity_trackers,
                        identity_result.completed,
                    );
                }
                Err(error) => {
                    eprintln!(
                        "UpperBounds: LP-gap fallback failed ({error}), \
                         using reduced-net results",
                    );
                }
            }
        }
    }

    assemble_upper_bounds_results(&prepared, &trackers, completed)
}
