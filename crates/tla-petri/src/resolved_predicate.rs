// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared resolved predicate types and evaluation for MCC property checking.
//!
//! This module provides name-to-index resolved representations of MCC
//! state predicates and integer expressions.  The same resolve/eval logic
//! is used by the reachability, CTL, and LTL/Buchi engines — deduplicating
//! what was previously three parallel implementations.

#[cfg(test)]
use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::model::PropertyAliases;
use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};
use crate::property_xml::{IntExpr, StatePredicate};

/// Resolved integer expression with place indices instead of names.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum ResolvedIntExpr {
    Constant(u64),
    TokensCount(Vec<PlaceIdx>),
}

/// Resolved state predicate with place/transition indices instead of names.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum ResolvedPredicate {
    And(Vec<ResolvedPredicate>),
    Or(Vec<ResolvedPredicate>),
    Not(Box<ResolvedPredicate>),
    IntLe(ResolvedIntExpr, ResolvedIntExpr),
    IsFireable(Vec<TransitionIdx>),
    True,
    False,
}

/// Resolve a [`StatePredicate`] from string names to integer indices.
pub(crate) fn resolve_predicate_with_aliases(
    pred: &StatePredicate,
    aliases: &PropertyAliases,
) -> ResolvedPredicate {
    match pred {
        StatePredicate::And(children) => ResolvedPredicate::And(
            children
                .iter()
                .map(|c| resolve_predicate_with_aliases(c, aliases))
                .collect(),
        ),
        StatePredicate::Or(children) => ResolvedPredicate::Or(
            children
                .iter()
                .map(|c| resolve_predicate_with_aliases(c, aliases))
                .collect(),
        ),
        StatePredicate::Not(inner) => {
            ResolvedPredicate::Not(Box::new(resolve_predicate_with_aliases(inner, aliases)))
        }
        StatePredicate::IntLe(left, right) => ResolvedPredicate::IntLe(
            resolve_int_expr_with_aliases(left, aliases),
            resolve_int_expr_with_aliases(right, aliases),
        ),
        StatePredicate::IsFireable(transitions) => {
            let indices: Vec<TransitionIdx> = transitions
                .iter()
                .flat_map(|name| {
                    aliases
                        .resolve_transitions(name)
                        .into_iter()
                        .flat_map(|resolved| resolved.iter().copied())
                })
                .collect();
            if indices.is_empty() {
                ResolvedPredicate::False
            } else {
                ResolvedPredicate::IsFireable(indices)
            }
        }
        StatePredicate::True => ResolvedPredicate::True,
        StatePredicate::False => ResolvedPredicate::False,
    }
}

/// Resolve an [`IntExpr`] from string place names to integer indices.
pub(crate) fn resolve_int_expr_with_aliases(
    expr: &IntExpr,
    aliases: &PropertyAliases,
) -> ResolvedIntExpr {
    match expr {
        IntExpr::Constant(v) => ResolvedIntExpr::Constant(*v),
        IntExpr::TokensCount(places) => {
            ResolvedIntExpr::TokensCount(resolve_place_bound(places, aliases))
        }
    }
}

pub(crate) fn resolve_place_bound(
    place_names: &[String],
    aliases: &PropertyAliases,
) -> Vec<PlaceIdx> {
    place_names
        .iter()
        .flat_map(|name| {
            aliases
                .resolve_places(name)
                .into_iter()
                .flat_map(|resolved| resolved.iter().copied())
        })
        .collect()
}

pub(crate) fn remap_int_expr(
    expr: &ResolvedIntExpr,
    place_map: &[Option<PlaceIdx>],
) -> Option<ResolvedIntExpr> {
    match expr {
        ResolvedIntExpr::Constant(value) => Some(ResolvedIntExpr::Constant(*value)),
        ResolvedIntExpr::TokensCount(places) => {
            let remapped = places
                .iter()
                .map(|place| place_map[place.0 as usize])
                .collect::<Option<Vec<_>>>()?;
            Some(ResolvedIntExpr::TokensCount(remapped))
        }
    }
}

/// Check whether all transitions in `IsFireable` predicates survived reduction.
///
/// Returns `true` if every transition index referenced by `IsFireable` nodes
/// in the predicate has a mapping in `trans_map`. If any transition was
/// eliminated (`trans_map[idx] == None`), returns `false`.
#[cfg(test)]
pub(crate) fn predicate_transitions_survived(
    pred: &ResolvedPredicate,
    trans_map: &[Option<TransitionIdx>],
) -> bool {
    match pred {
        ResolvedPredicate::And(children) | ResolvedPredicate::Or(children) => children
            .iter()
            .all(|child| predicate_transitions_survived(child, trans_map)),
        ResolvedPredicate::Not(inner) => predicate_transitions_survived(inner, trans_map),
        ResolvedPredicate::IsFireable(transitions) => transitions
            .iter()
            .all(|t| trans_map[t.0 as usize].is_some()),
        ResolvedPredicate::IntLe(..) | ResolvedPredicate::True | ResolvedPredicate::False => true,
    }
}

/// Check whether the reduction preserves all transitions relevant to a predicate.
///
/// Extends [`predicate_transitions_survived`] to also cover `TokensCount`:
/// for each place referenced by `TokensCount`, verifies that ALL transitions
/// in the original `net` with arcs to/from that place survived the reduction.
/// If any such transition was eliminated, the reduced net's state space may be
/// incomplete for the monitored places, causing unsound AG=TRUE verdicts.
pub(crate) fn predicate_reduction_safe(
    pred: &ResolvedPredicate,
    net: &PetriNet,
    trans_map: &[Option<TransitionIdx>],
) -> bool {
    match pred {
        ResolvedPredicate::And(children) | ResolvedPredicate::Or(children) => children
            .iter()
            .all(|child| predicate_reduction_safe(child, net, trans_map)),
        ResolvedPredicate::Not(inner) => predicate_reduction_safe(inner, net, trans_map),
        ResolvedPredicate::IsFireable(transitions) => transitions
            .iter()
            .all(|t| trans_map[t.0 as usize].is_some()),
        ResolvedPredicate::IntLe(left, right) => {
            int_expr_place_transitions_survived(left, net, trans_map)
                && int_expr_place_transitions_survived(right, net, trans_map)
        }
        ResolvedPredicate::True | ResolvedPredicate::False => true,
    }
}

fn int_expr_place_transitions_survived(
    expr: &ResolvedIntExpr,
    net: &PetriNet,
    trans_map: &[Option<TransitionIdx>],
) -> bool {
    match expr {
        ResolvedIntExpr::Constant(_) => true,
        ResolvedIntExpr::TokensCount(places) => {
            for place in places {
                for (tidx, trans) in net.transitions.iter().enumerate() {
                    let touches = trans.inputs.iter().any(|arc| arc.place == *place)
                        || trans.outputs.iter().any(|arc| arc.place == *place);
                    if touches && trans_map[tidx].is_none() {
                        return false;
                    }
                }
            }
            true
        }
    }
}

pub(crate) fn remap_predicate(
    pred: &ResolvedPredicate,
    place_map: &[Option<PlaceIdx>],
    trans_map: &[Option<TransitionIdx>],
) -> Option<ResolvedPredicate> {
    match pred {
        ResolvedPredicate::And(children) => Some(ResolvedPredicate::And(
            children
                .iter()
                .map(|child| remap_predicate(child, place_map, trans_map))
                .collect::<Option<Vec<_>>>()?,
        )),
        ResolvedPredicate::Or(children) => Some(ResolvedPredicate::Or(
            children
                .iter()
                .map(|child| remap_predicate(child, place_map, trans_map))
                .collect::<Option<Vec<_>>>()?,
        )),
        ResolvedPredicate::Not(inner) => Some(ResolvedPredicate::Not(Box::new(remap_predicate(
            inner, place_map, trans_map,
        )?))),
        ResolvedPredicate::IntLe(left, right) => Some(ResolvedPredicate::IntLe(
            remap_int_expr(left, place_map)?,
            remap_int_expr(right, place_map)?,
        )),
        ResolvedPredicate::IsFireable(transitions) => Some(ResolvedPredicate::IsFireable(
            transitions
                .iter()
                .map(|transition| trans_map[transition.0 as usize])
                .collect::<Option<Vec<_>>>()?,
        )),
        ResolvedPredicate::True => Some(ResolvedPredicate::True),
        ResolvedPredicate::False => Some(ResolvedPredicate::False),
    }
}

/// Count unresolved names in a predicate resolution.
///
/// Compares the original formula's name counts against the resolved index counts.
/// Returns (total_names, unresolved_count) — if unresolved_count > 0, the formula
/// has names that didn't match the model's place/transition IDs.
pub(crate) fn count_unresolved_with_aliases(
    pred: &StatePredicate,
    aliases: &PropertyAliases,
) -> (usize, usize) {
    match pred {
        StatePredicate::And(children) | StatePredicate::Or(children) => {
            children.iter().fold((0, 0), |(t, u), c| {
                let (ct, cu) = count_unresolved_with_aliases(c, aliases);
                (t + ct, u + cu)
            })
        }
        StatePredicate::Not(inner) => count_unresolved_with_aliases(inner, aliases),
        StatePredicate::IntLe(left, right) => {
            let (lt, lu) = count_unresolved_int_with_aliases(left, aliases);
            let (rt, ru) = count_unresolved_int_with_aliases(right, aliases);
            (lt + rt, lu + ru)
        }
        StatePredicate::IsFireable(transitions) => {
            let unresolved = transitions
                .iter()
                .filter(|name| aliases.resolve_transitions(name).is_none())
                .count();
            (transitions.len(), unresolved)
        }
        StatePredicate::True | StatePredicate::False => (0, 0),
    }
}

fn count_unresolved_int_with_aliases(expr: &IntExpr, aliases: &PropertyAliases) -> (usize, usize) {
    match expr {
        IntExpr::Constant(_) => (0, 0),
        IntExpr::TokensCount(places) => count_unresolved_place_bound(places, aliases),
    }
}

pub(crate) fn count_unresolved_place_bound(
    place_names: &[String],
    aliases: &PropertyAliases,
) -> (usize, usize) {
    let unresolved = place_names
        .iter()
        .filter(|name| aliases.resolve_places(name).is_none())
        .count();
    (place_names.len(), unresolved)
}

#[cfg(test)]
fn aliases_from_maps(
    place_map: &HashMap<&str, PlaceIdx>,
    trans_map: &HashMap<&str, TransitionIdx>,
) -> PropertyAliases {
    PropertyAliases {
        place_aliases: place_map
            .iter()
            .map(|(name, idx)| ((*name).to_string(), vec![*idx]))
            .collect(),
        transition_aliases: trans_map
            .iter()
            .map(|(name, idx)| ((*name).to_string(), vec![*idx]))
            .collect(),
    }
}

#[cfg(test)]
pub(crate) fn resolve_predicate(
    pred: &StatePredicate,
    place_map: &HashMap<&str, PlaceIdx>,
    trans_map: &HashMap<&str, TransitionIdx>,
) -> ResolvedPredicate {
    let aliases = aliases_from_maps(place_map, trans_map);
    resolve_predicate_with_aliases(pred, &aliases)
}

#[cfg(test)]
pub(crate) fn resolve_int_expr(
    expr: &IntExpr,
    place_map: &HashMap<&str, PlaceIdx>,
) -> ResolvedIntExpr {
    let aliases = PropertyAliases {
        place_aliases: place_map
            .iter()
            .map(|(name, idx)| ((*name).to_string(), vec![*idx]))
            .collect(),
        transition_aliases: HashMap::new(),
    };
    resolve_int_expr_with_aliases(expr, &aliases)
}

#[cfg(test)]
pub(crate) fn count_unresolved(
    pred: &StatePredicate,
    place_map: &HashMap<&str, PlaceIdx>,
    trans_map: &HashMap<&str, TransitionIdx>,
) -> (usize, usize) {
    let aliases = aliases_from_maps(place_map, trans_map);
    count_unresolved_with_aliases(pred, &aliases)
}

/// Evaluate a resolved predicate against a marking.
pub(crate) fn eval_predicate(pred: &ResolvedPredicate, marking: &[u64], net: &PetriNet) -> bool {
    match pred {
        ResolvedPredicate::And(children) => {
            children.iter().all(|c| eval_predicate(c, marking, net))
        }
        ResolvedPredicate::Or(children) => children.iter().any(|c| eval_predicate(c, marking, net)),
        ResolvedPredicate::Not(inner) => !eval_predicate(inner, marking, net),
        ResolvedPredicate::IntLe(left, right) => {
            eval_int_expr(left, marking) <= eval_int_expr(right, marking)
        }
        ResolvedPredicate::IsFireable(transitions) => {
            transitions.iter().any(|&t| net.is_enabled(marking, t))
        }
        ResolvedPredicate::True => true,
        ResolvedPredicate::False => false,
    }
}

/// Evaluate a resolved integer expression against a marking.
pub(crate) fn eval_int_expr(expr: &ResolvedIntExpr, marking: &[u64]) -> u64 {
    match expr {
        ResolvedIntExpr::Constant(v) => *v,
        ResolvedIntExpr::TokensCount(indices) => {
            indices.iter().map(|idx| marking[idx.0 as usize]).sum()
        }
    }
}

#[cfg(test)]
#[path = "resolved_predicate_tests.rs"]
mod resolved_predicate_tests;
