// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Colored pre-unfolding reductions for HLPNML nets.
//!
//! Applied between HLPNML parsing and P/T unfolding to shrink the colored
//! net *before* the combinatorial blowup of unfolding. This can reduce
//! unfolded net size by 10-100x for symmetric models.
//!
//! # Supported reductions
//!
//! - **Constant place collapsing** — when all arcs touching a colored place
//!   use `<all>` inscriptions (depositing/withdrawing uniformly across all
//!   colors) and the initial marking is uniform, the place's sort is replaced
//!   with `Dot`. This causes unfolding to produce 1 P/T place instead of N.

use std::collections::{HashMap, HashSet};

use crate::hlpnml::{ColorExpr, ColorSort, ColorTerm, ColoredNet};

/// Report of colored reductions applied before unfolding.
#[derive(Debug, Default)]
pub(crate) struct ColorReductionReport {
    /// Places whose sort was collapsed to Dot: (place_id, original_sort_size).
    pub collapsed_places: Vec<(String, usize)>,
}

impl ColorReductionReport {
    /// Total place instances saved (sum of sort_size - 1 for each collapsed place).
    #[must_use]
    pub fn places_saved(&self) -> usize {
        self.collapsed_places
            .iter()
            .map(|(_, orig)| orig.saturating_sub(1))
            .sum()
    }
}

/// Apply query-independent colored reductions to a [`ColoredNet`] in place.
///
/// Re-enabled (#1418): the strengthened soundness criterion (all arcs of every
/// touching transition must be uniform AND no guards) prevents collapsing on
/// models like NeoElection-COL-2 where mixed-inscription transitions would
/// unfold to N competing P/T transitions. The old criterion only checked the
/// candidate place's own arcs, which was insufficient.
pub(crate) fn reduce_colored(net: &mut ColoredNet) -> ColorReductionReport {
    let mut report = ColorReductionReport::default();
    collapse_constant_places(net, &mut report);
    report
}

/// A candidate place eligible for collapsing, with its analysis result.
struct CollapseCandidate {
    index: usize,
    place_id: String,
    original_cardinality: usize,
}

/// Collapse places where all touching arcs use uniform (`All`) inscriptions.
///
/// A place is collapsible when:
/// 1. Its sort has cardinality > 1 (Dot places are already minimal).
/// 2. Every arc connecting to/from the place has an `All` inscription
///    (or `NumberOf { color: DotConstant, .. }` which is the Dot equivalent).
/// 3. The initial marking is uniform across all colors (or absent).
///
/// When collapsed, the place's `sort_id` is rewritten to the net's Dot sort
/// (creating one if needed), and its initial marking is adjusted to the
/// per-color token count (since Dot unfolds to a single place).
pub(crate) fn collapse_constant_places(net: &mut ColoredNet, report: &mut ColorReductionReport) {
    // Phase 1: Analysis (immutable borrows only). Collect owned data.
    let sort_cards: HashMap<String, usize> = net
        .sorts
        .iter()
        .filter_map(|s| match s {
            ColorSort::Dot { id, .. } => Some((id.clone(), 1)),
            ColorSort::CyclicEnum { id, constants, .. } => Some((id.clone(), constants.len())),
            ColorSort::Product { .. } => None,
        })
        .collect();

    // Collect place IDs that have at least one arc (isolated places have no
    // optimization value and collapsing them changes the unfolded place index
    // mapping, which can break alias-based predicate resolution).
    let places_with_arcs: HashSet<&str> = net
        .arcs
        .iter()
        .flat_map(|a| [a.source.as_str(), a.target.as_str()])
        .collect();

    // Find candidate places (sort cardinality > 1, at least one arc).
    let candidate_ids: HashSet<String> = net
        .places
        .iter()
        .filter(|p| sort_cards.get(&p.sort_id).copied().unwrap_or(1) > 1)
        .filter(|p| places_with_arcs.contains(p.id.as_str()))
        .map(|p| p.id.clone())
        .collect();

    if candidate_ids.is_empty() {
        return;
    }

    // Check arc inscriptions: for each candidate place, all arcs must be uniform.
    let mut disqualified: HashSet<String> = HashSet::new();

    for arc in &net.arcs {
        if !is_uniform_inscription(&arc.inscription) {
            // Disqualify ALL candidate places touched by this non-uniform arc.
            // An arc between two candidate places must disqualify both.
            if candidate_ids.contains(&arc.source) {
                disqualified.insert(arc.source.clone());
            }
            if candidate_ids.contains(&arc.target) {
                disqualified.insert(arc.target.clone());
            }
        }
    }

    // Check initial markings: must be uniform or absent.
    for place in &net.places {
        if !candidate_ids.contains(&place.id) || disqualified.contains(&place.id) {
            continue;
        }
        if let Some(ref marking) = place.initial_marking {
            if !is_uniform_marking(marking) {
                disqualified.insert(place.id.clone());
            }
        }
    }

    // Soundness guard: disqualify a candidate place P if any transition T
    // touching P has non-uniform arcs to OTHER places or a non-trivial guard.
    //
    // Rationale (#1418): when T has an `All` arc to collapsed place P but a
    // variable-binding arc to non-collapsed place Q, unfolding produces N P/T
    // transitions (one per color binding) that ALL compete for the single
    // collapsed Dot place. In the uncollapsed net, each color variant had its
    // own P_ci place with independent tokens — no contention. Collapsing is
    // only sound when every transition touching P is fully "color-blind" (all
    // arcs uniform, no guard), guaranteeing it unfolds to exactly one P/T
    // transition.
    let transition_ids: HashSet<&str> = net.transitions.iter().map(|t| t.id.as_str()).collect();
    let remaining_candidates: Vec<String> = candidate_ids
        .iter()
        .filter(|id| !disqualified.contains(*id))
        .cloned()
        .collect();
    for place_id in &remaining_candidates {
        // Find all transitions connected to this place via arcs.
        let touching_transitions: HashSet<&str> = net
            .arcs
            .iter()
            .filter(|a| a.source == *place_id || a.target == *place_id)
            .filter_map(|a| {
                let other = if a.source == *place_id {
                    a.target.as_str()
                } else {
                    a.source.as_str()
                };
                if transition_ids.contains(other) {
                    Some(other)
                } else {
                    None
                }
            })
            .collect();

        let mut safe = true;
        for tid in &touching_transitions {
            // Check ALL arcs of this transition (not just arcs to our candidate).
            let all_arcs_uniform = net
                .arcs
                .iter()
                .filter(|a| a.source == *tid || a.target == *tid)
                .all(|a| is_uniform_inscription(&a.inscription));
            if !all_arcs_uniform {
                safe = false;
                break;
            }

            // A guard implies variable-dependent behavior, which means unfolding
            // produces multiple P/T transitions per color binding.
            if let Some(t) = net.transitions.iter().find(|t| t.id == *tid) {
                if t.guard.is_some() {
                    safe = false;
                    break;
                }
            }
        }

        if !safe {
            disqualified.insert(place_id.clone());
        }
    }

    // Sibling consistency guard (#1418): disqualify a candidate place P if any
    // transition T touching P also touches a non-collapsible place Q (a place
    // with cardinality > 1 that is NOT in the collapsible set).
    //
    // Rationale: when a collapsed place (Dot, 1 P/T place) shares a transition
    // with a non-collapsed place (sort S, |S| P/T places), the unfolded P/T
    // transition has asymmetric inputs: 1 arc to the collapsed place vs |S|
    // arcs to the non-collapsed place. This changes enablement conditions and
    // produces spurious reachable states. All-or-nothing collapsing per
    // transition cluster prevents this structural asymmetry.
    let surviving: HashSet<&str> = candidate_ids
        .iter()
        .filter(|id| !disqualified.contains(*id))
        .map(|s| s.as_str())
        .collect();

    let mut sibling_disqualified: HashSet<String> = HashSet::new();
    for place_id in &surviving {
        let touching_transitions: HashSet<&str> = net
            .arcs
            .iter()
            .filter(|a| a.source == *place_id || a.target == *place_id)
            .filter_map(|a| {
                let other = if a.source == *place_id {
                    a.target.as_str()
                } else {
                    a.source.as_str()
                };
                if transition_ids.contains(other) {
                    Some(other)
                } else {
                    None
                }
            })
            .collect();

        for tid in &touching_transitions {
            // Find all places touched by this transition.
            let sibling_places: Vec<&str> = net
                .arcs
                .iter()
                .filter(|a| a.source == *tid || a.target == *tid)
                .filter_map(|a| {
                    let other = if a.source == *tid {
                        a.target.as_str()
                    } else {
                        a.source.as_str()
                    };
                    if !transition_ids.contains(other) {
                        Some(other)
                    } else {
                        None
                    }
                })
                .collect();

            for sib in sibling_places {
                let sib_card = net
                    .places
                    .iter()
                    .find(|p| p.id == sib)
                    .and_then(|p| sort_cards.get(&p.sort_id).copied())
                    .unwrap_or(1);
                // If a sibling has cardinality > 1 and is NOT collapsible,
                // then our place is unsafe to collapse.
                if sib_card > 1 && !surviving.contains(sib) {
                    sibling_disqualified.insert(place_id.to_string());
                    break;
                }
            }
            if sibling_disqualified.contains(*place_id) {
                break;
            }
        }
    }

    for id in &sibling_disqualified {
        disqualified.insert(id.clone());
    }

    // Build the final list of places to collapse.
    let to_collapse: Vec<CollapseCandidate> = net
        .places
        .iter()
        .enumerate()
        .filter(|(_, p)| candidate_ids.contains(&p.id) && !disqualified.contains(&p.id))
        .map(|(i, p)| CollapseCandidate {
            index: i,
            place_id: p.id.clone(),
            original_cardinality: sort_cards.get(&p.sort_id).copied().unwrap_or(1),
        })
        .collect();

    if to_collapse.is_empty() {
        return;
    }

    // Phase 2: Mutation. No more borrows from net needed.
    let dot_sort_id = ensure_dot_sort(net);
    let collapsible_ids: HashSet<&str> = to_collapse.iter().map(|c| c.place_id.as_str()).collect();

    for candidate in &to_collapse {
        // Rewrite sort to Dot.
        net.places[candidate.index].sort_id = dot_sort_id.clone();

        // Adjust initial marking to per-color value.
        if let Some(ref marking) = net.places[candidate.index].initial_marking {
            let per_color = per_color_count(marking);
            net.places[candidate.index].initial_marking = if per_color == 0 {
                None
            } else {
                Some(ColorExpr::NumberOf {
                    count: per_color,
                    color: Box::new(ColorTerm::DotConstant),
                })
            };
        }

        report
            .collapsed_places
            .push((candidate.place_id.clone(), candidate.original_cardinality));
    }

    // Rewrite arc inscriptions touching collapsed places.
    for arc in &mut net.arcs {
        if collapsible_ids.contains(arc.source.as_str())
            || collapsible_ids.contains(arc.target.as_str())
        {
            rewrite_all_to_dot(&mut arc.inscription);
        }
    }
}

/// Check if a color expression is uniform across all colors of a sort.
///
/// Uniform means `All { .. }` or `NumberOf { color: DotConstant, .. }`.
fn is_uniform_inscription(expr: &ColorExpr) -> bool {
    match expr {
        ColorExpr::All { .. } => true,
        ColorExpr::NumberOf { color, .. } => matches!(color.as_ref(), ColorTerm::DotConstant),
        ColorExpr::Add(children) => children.iter().all(is_uniform_inscription),
    }
}

/// Check if a marking expression produces uniform tokens per color.
fn is_uniform_marking(expr: &ColorExpr) -> bool {
    match expr {
        ColorExpr::All { .. } => true,
        ColorExpr::NumberOf { color, .. } => matches!(color.as_ref(), ColorTerm::DotConstant),
        ColorExpr::Add(children) => children.iter().all(is_uniform_marking),
    }
}

/// Extract the per-color token count from a uniform marking expression.
fn per_color_count(expr: &ColorExpr) -> u64 {
    match expr {
        ColorExpr::All { .. } => 1,
        ColorExpr::NumberOf { count, .. } => *count,
        ColorExpr::Add(children) => children.iter().map(per_color_count).sum(),
    }
}

/// Ensure the net has a Dot sort and return its ID.
fn ensure_dot_sort(net: &mut ColoredNet) -> String {
    for sort in &net.sorts {
        if let ColorSort::Dot { id, .. } = sort {
            return id.clone();
        }
    }
    let id = "dot_synthetic".to_string();
    net.sorts.push(ColorSort::Dot {
        id: id.clone(),
        name: "dot".to_string(),
    });
    id
}

/// Rewrite `All { sort_id }` inscriptions to `NumberOf { 1, DotConstant }`.
fn rewrite_all_to_dot(expr: &mut ColorExpr) {
    match expr {
        ColorExpr::All { .. } => {
            *expr = ColorExpr::NumberOf {
                count: 1,
                color: Box::new(ColorTerm::DotConstant),
            };
        }
        ColorExpr::Add(children) => {
            for child in children {
                rewrite_all_to_dot(child);
            }
        }
        ColorExpr::NumberOf { .. } => {} // Already Dot-compatible.
    }
}

#[cfg(test)]
#[path = "colored_reduce_tests.rs"]
mod tests;
