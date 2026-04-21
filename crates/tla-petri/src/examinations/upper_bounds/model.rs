// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! UpperBounds data model: bound trackers, property preparation, result assembly.

use std::collections::HashMap;

use crate::model::PropertyAliases;
#[allow(unused_imports)]
use crate::petri_net::{PetriNet, PlaceIdx};
use crate::property_xml::{Formula, Property};
use crate::resolved_predicate::{count_unresolved_place_bound, resolve_place_bound};

/// Structural upper bound for an UpperBounds query, preserving repeated places.
///
/// MCC `place-bound(...)` formulas are represented as a list of places, not a set.
/// If a place appears multiple times, the query counts that place's tokens with
/// multiplicity. To certify exactness soundly, the structural cap must therefore
/// bound the weighted sum over the query multiset rather than the deduplicated set.
pub(super) fn structural_query_bound(
    invariants: &[crate::invariant::PInvariant],
    place_indices: &[PlaceIdx],
) -> Option<u64> {
    if place_indices.is_empty() {
        return Some(0);
    }

    let mut multiplicities: HashMap<usize, u64> = HashMap::new();
    for place in place_indices {
        *multiplicities.entry(place.0 as usize).or_insert(0) += 1;
    }

    if multiplicities.len() == place_indices.len() {
        let places: Vec<usize> = place_indices.iter().map(|place| place.0 as usize).collect();
        return crate::invariant::structural_set_bound(invariants, &places);
    }

    invariants
        .iter()
        .filter_map(|inv| {
            let mut bound = 0u128;
            for (&place, &coefficient) in &multiplicities {
                let weight = inv.weights[place];
                if weight == 0 {
                    return None;
                }
                let place_bound =
                    (inv.token_count as u128) * (coefficient as u128) / (weight as u128);
                bound = bound.max(place_bound);
            }
            u64::try_from(bound).ok()
        })
        .min()
}

/// Per-property tracking state during BFS.
#[derive(Clone)]
pub(super) struct BoundTracker {
    /// Property identifier for MCC output.
    pub(super) id: String,
    /// Indices of places to sum.
    pub(super) place_indices: Vec<PlaceIdx>,
    /// Maximum token sum observed so far.
    pub(super) max_bound: u64,
    /// Structural upper bound from P-invariants (`None` if uncovered).
    pub(super) structural_bound: Option<u64>,
    /// LP state-equation upper bound (`None` if unbounded or too large).
    pub(super) lp_bound: Option<u64>,
}

impl BoundTracker {
    /// Effective upper bound: minimum of all available cap sources.
    pub(super) fn effective_bound(&self) -> Option<u64> {
        match (self.structural_bound, self.lp_bound) {
            (Some(s), Some(l)) => Some(s.min(l)),
            (Some(s), None) => Some(s),
            (None, Some(l)) => Some(l),
            (None, None) => None,
        }
    }

    /// Whether the observed bound has reached the effective upper bound,
    /// confirming it is the exact maximum.
    pub(super) fn is_structurally_resolved(&self) -> bool {
        self.effective_bound()
            .is_some_and(|eb| self.max_bound >= eb)
    }
}

/// Prepared UpperBounds property classified before BFS starts.
pub(super) enum PreparedUpperBoundProperty {
    /// Property has unresolved place IDs and must fail-closed.
    Invalid { id: String },
    /// Property is valid and participates in BFS at observer slot `slot`.
    Valid { slot: usize },
}

/// Prepare UpperBounds properties for fail-closed evaluation.
pub(super) fn prepare_upper_bounds_properties_with_aliases(
    properties: &[Property],
    aliases: &PropertyAliases,
) -> (Vec<PreparedUpperBoundProperty>, Vec<BoundTracker>) {
    let mut trackers = Vec::new();
    let prepared = properties
        .iter()
        .filter_map(|prop| {
            let Formula::PlaceBound(place_names) = &prop.formula else {
                return None;
            };
            let (total, unresolved) = count_unresolved_place_bound(place_names, aliases);
            if unresolved > 0 {
                eprintln!(
                    "UpperBounds resolution guard: {} has {unresolved}/{total} \
                     unresolved names → CANNOT_COMPUTE",
                    prop.id
                );
                Some(PreparedUpperBoundProperty::Invalid {
                    id: prop.id.clone(),
                })
            } else {
                let slot = trackers.len();
                let place_indices = resolve_place_bound(place_names, aliases);
                trackers.push(BoundTracker {
                    id: prop.id.clone(),
                    place_indices,
                    max_bound: 0,
                    structural_bound: None,
                    lp_bound: None,
                });
                Some(PreparedUpperBoundProperty::Valid { slot })
            }
        })
        .collect();

    (prepared, trackers)
}

#[cfg(test)]
pub(super) fn prepare_upper_bounds_properties(
    net: &PetriNet,
    properties: &[Property],
) -> (Vec<PreparedUpperBoundProperty>, Vec<BoundTracker>) {
    let aliases = PropertyAliases::identity(net);
    prepare_upper_bounds_properties_with_aliases(properties, &aliases)
}

/// Assemble final results from prepared properties and trackers.
pub(super) fn assemble_upper_bounds_results(
    prepared: &[PreparedUpperBoundProperty],
    trackers: &[BoundTracker],
    completed: bool,
) -> Vec<(String, Option<u64>)> {
    prepared
        .iter()
        .map(|property| match property {
            PreparedUpperBoundProperty::Invalid { id } => (id.clone(), None),
            PreparedUpperBoundProperty::Valid { slot } => {
                let tracker = &trackers[*slot];
                if completed || tracker.is_structurally_resolved() {
                    (tracker.id.clone(), Some(tracker.max_bound))
                } else {
                    (tracker.id.clone(), None)
                }
            }
        })
        .collect()
}
