// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Heuristic weight extraction and distance scoring.
//!
//! Extracts target token thresholds from resolved predicates and computes
//! heuristic distances from markings to those targets. Used by the search
//! loop to guide best-first exploration toward witness states.

use crate::petri_net::PetriNet;
use crate::property_xml::PathQuantifier;
use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};

use super::super::reachability::PropertyTracker;

/// Heuristic weights for guiding search toward a specific property's target.
///
/// For each place, `deficit_weight[p]` is the token deficit weight: how many
/// additional tokens at place `p` bring us closer to satisfying the predicate.
/// Derived from the LP state-equation relaxation.
pub(super) struct HeuristicWeights {
    /// Per-place weight contribution. Higher weight = more tokens needed here.
    pub(super) place_targets: Vec<(usize, u64)>,
}

/// Compute heuristic weights for a single property tracker.
///
/// Extracts target token thresholds from the predicate. For EF(φ), the
/// heuristic estimates distance to a φ-satisfying state. For AG(φ), the
/// heuristic estimates distance to a ¬φ-satisfying state (counterexample).
pub(super) fn compute_heuristic_weights(
    net: &PetriNet,
    tracker: &PropertyTracker,
) -> HeuristicWeights {
    let pred = match tracker.quantifier {
        PathQuantifier::EF => &tracker.predicate,
        // For AG(φ), we want counterexamples — states where ¬φ holds.
        // Extracting targets from ¬φ is complex; fall back to trivial weights
        // unless the predicate has a simple structure we can negate.
        PathQuantifier::AG => {
            return extract_ag_weights(net, &tracker.predicate);
        }
    };
    extract_ef_weights(net, pred)
}

/// Extract heuristic weights for EF(φ): find states where φ holds.
fn extract_ef_weights(net: &PetriNet, pred: &ResolvedPredicate) -> HeuristicWeights {
    let mut targets = Vec::new();
    collect_token_targets(pred, &mut targets);
    // Filter out targets already satisfied by initial marking.
    targets.retain(|&(pidx, threshold)| {
        pidx < net.initial_marking.len() && net.initial_marking[pidx] < threshold
    });
    HeuristicWeights {
        place_targets: targets,
    }
}

/// Extract heuristic weights for AG(φ): find counterexamples where ¬φ holds.
///
/// For AG(φ), a counterexample is a state where φ is FALSE. For simple
/// predicates like `tokens(p) >= k` (i.e., IntLe(k, tokens(p))), the
/// negation is `tokens(p) < k`, which means we want states with LOW tokens
/// at place p. We cannot easily express "low tokens" as a positive heuristic
/// target, so AG properties get trivial weights (no guidance). The search
/// still explores but without heuristic bias.
fn extract_ag_weights(_net: &PetriNet, _pred: &ResolvedPredicate) -> HeuristicWeights {
    HeuristicWeights {
        place_targets: Vec::new(),
    }
}

/// Recursively collect `(place_index, threshold)` pairs from IntLe atoms.
///
/// Handles: `IntLe(Constant(k), TokensCount([p]))` → target tokens(p) >= k
fn collect_token_targets(pred: &ResolvedPredicate, targets: &mut Vec<(usize, u64)>) {
    match pred {
        ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(k),
            ResolvedIntExpr::TokensCount(places),
        ) => {
            // tokens(places) >= k — want each place to contribute
            // For multi-place TokensCount, distribute threshold equally (approximation).
            if places.len() == 1 {
                targets.push((places[0].0 as usize, *k));
            }
        }
        ResolvedPredicate::And(children) => {
            for child in children {
                collect_token_targets(child, targets);
            }
        }
        ResolvedPredicate::Or(children) => {
            // For OR, we pick the first branch as an approximation.
            if let Some(first) = children.first() {
                collect_token_targets(first, targets);
            }
        }
        ResolvedPredicate::Not(inner) => {
            // Negation flips semantics — don't extract targets from negated predicates.
            let _ = inner;
        }
        _ => {}
    }
}

/// Compute combined heuristic distance across all unresolved properties.
///
/// Returns the minimum distance across all unresolved properties, so the
/// search is guided toward whichever property is closest to being satisfied.
pub(super) fn combined_heuristic(
    marking: &[u64],
    trackers: &[PropertyTracker],
    weights: &[Option<HeuristicWeights>],
) -> u64 {
    let mut min_dist = u64::MAX;
    for (tracker, w) in trackers.iter().zip(weights.iter()) {
        if tracker.verdict.is_some() {
            continue;
        }
        if let Some(w) = w {
            let d = heuristic_distance(marking, w);
            min_dist = min_dist.min(d);
        }
    }
    if min_dist == u64::MAX {
        0 // All resolved or no weights — no preference.
    } else {
        min_dist
    }
}

/// Compute heuristic distance from a marking to the target.
///
/// Sum of token deficits: for each target (place, threshold), if
/// `marking[place] < threshold`, add the deficit `threshold - marking[place]`.
pub(super) fn heuristic_distance(marking: &[u64], weights: &HeuristicWeights) -> u64 {
    let mut dist: u64 = 0;
    for &(pidx, threshold) in &weights.place_targets {
        if pidx < marking.len() {
            let tokens = marking[pidx];
            if tokens < threshold {
                dist = dist.saturating_add(threshold - tokens);
            }
        }
    }
    dist
}
