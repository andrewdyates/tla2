// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LTL partial-order reduction helpers.
//!
//! Computes the set of "visible" transitions for an LTL formula: transitions
//! whose firing can change the truth value of an atom in the formula.
//! Stubborn set POR restricts successor generation to a subset that preserves
//! all stutter-equivalent traces (Peled 1996), which is sound for
//! stutter-insensitive LTL (formulas without the X operator).

use rustc_hash::FxHashSet;

use crate::buchi::LtlNnf;
use crate::petri_net::{PlaceIdx, TransitionIdx};
use crate::reduction::ReducedNet;
use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};

/// Check whether an LTL formula (in NNF) contains the Next operator.
///
/// The X operator is stutter-sensitive, so POR must be disabled when present.
pub(crate) fn formula_contains_next(formula: &LtlNnf) -> bool {
    match formula {
        LtlNnf::Next(_) => true,
        LtlNnf::And(children) | LtlNnf::Or(children) => children.iter().any(formula_contains_next),
        LtlNnf::Until(a, b) | LtlNnf::Release(a, b) => {
            formula_contains_next(a) || formula_contains_next(b)
        }
        LtlNnf::Atom(_) | LtlNnf::NegAtom(_) | LtlNnf::True | LtlNnf::False => false,
    }
}

/// Compute the set of reduced-net transitions visible to an LTL formula.
///
/// A transition is visible if firing it can change the truth value of any
/// atom referenced by the formula. Invisible transitions can be pruned
/// by stubborn set POR without affecting the model checking result.
///
/// Returns the visible transitions in **reduced-net** index space, suitable
/// for passing directly to [`crate::stubborn::compute_stubborn_set`].
pub(crate) fn ltl_visible_reduced_transitions(
    atoms: &[ResolvedPredicate],
    reduced: &ReducedNet,
) -> Vec<TransitionIdx> {
    // Collect all original-net places and transitions referenced by atoms.
    let mut orig_places: FxHashSet<PlaceIdx> = FxHashSet::default();
    let mut orig_transitions: FxHashSet<TransitionIdx> = FxHashSet::default();
    for atom in atoms {
        collect_atom_references(atom, &mut orig_places, &mut orig_transitions);
    }

    // Map original places to reduced-net space.
    let mut reduced_places: FxHashSet<PlaceIdx> = FxHashSet::default();
    for &orig_p in &orig_places {
        if let Some(reduced_p) = reduced.place_map.get(orig_p.0 as usize).copied().flatten() {
            reduced_places.insert(reduced_p);
        }
        // If the place was removed as constant/isolated, its token count
        // never changes — no transitions are visible through it.
    }

    // Handle P-invariant reconstructions: if an original place was removed
    // but its value is reconstructed from kept places, those kept places
    // are effectively referenced by the atom.
    for recon in &reduced.reconstructions {
        if orig_places.contains(&recon.place) {
            for &(term_place, _) in &recon.terms {
                if let Some(reduced_p) = reduced
                    .place_map
                    .get(term_place.0 as usize)
                    .copied()
                    .flatten()
                {
                    reduced_places.insert(reduced_p);
                }
            }
        }
    }

    // Map original transitions to reduced-net space (for IsFireable atoms).
    let mut reduced_fireability: FxHashSet<TransitionIdx> = FxHashSet::default();
    for &orig_t in &orig_transitions {
        if let Some(reduced_t) = reduced
            .transition_map
            .get(orig_t.0 as usize)
            .copied()
            .flatten()
        {
            reduced_fireability.insert(reduced_t);
        }
    }

    // Collect the input places of IsFireable-referenced reduced transitions.
    // Any transition that touches these places can change the fireability atom.
    let mut fireability_input_places: FxHashSet<PlaceIdx> = FxHashSet::default();
    for &ft in &reduced_fireability {
        for arc in &reduced.net.transitions[ft.0 as usize].inputs {
            fireability_input_places.insert(arc.place);
        }
        for arc in &reduced.net.transitions[ft.0 as usize].outputs {
            fireability_input_places.insert(arc.place);
        }
    }

    // A reduced-net transition is visible if it:
    // 1. Touches (input/output) any place referenced by a cardinality atom, OR
    // 2. IS a fireability-referenced transition, OR
    // 3. Touches a place shared with a fireability-referenced transition.
    let mut visible: Vec<TransitionIdx> = Vec::new();
    for (tidx, t) in reduced.net.transitions.iter().enumerate() {
        let ti = TransitionIdx(tidx as u32);
        let touches_cardinality = t.inputs.iter().any(|a| reduced_places.contains(&a.place))
            || t.outputs.iter().any(|a| reduced_places.contains(&a.place));
        let is_fireability = reduced_fireability.contains(&ti);
        let touches_fireability_place = t
            .inputs
            .iter()
            .any(|a| fireability_input_places.contains(&a.place))
            || t.outputs
                .iter()
                .any(|a| fireability_input_places.contains(&a.place));

        if touches_cardinality || is_fireability || touches_fireability_place {
            visible.push(ti);
        }
    }

    visible
}

/// Recursively collect original-net place and transition indices from a resolved atom.
fn collect_atom_references(
    pred: &ResolvedPredicate,
    places: &mut FxHashSet<PlaceIdx>,
    transitions: &mut FxHashSet<TransitionIdx>,
) {
    match pred {
        ResolvedPredicate::And(children) | ResolvedPredicate::Or(children) => {
            for child in children {
                collect_atom_references(child, places, transitions);
            }
        }
        ResolvedPredicate::Not(inner) => collect_atom_references(inner, places, transitions),
        ResolvedPredicate::IntLe(left, right) => {
            collect_int_expr_places(left, places);
            collect_int_expr_places(right, places);
        }
        ResolvedPredicate::IsFireable(trans) => {
            for &t in trans {
                transitions.insert(t);
            }
        }
        ResolvedPredicate::True | ResolvedPredicate::False => {}
    }
}

/// Collect place indices from a resolved integer expression.
fn collect_int_expr_places(expr: &ResolvedIntExpr, places: &mut FxHashSet<PlaceIdx>) {
    match expr {
        ResolvedIntExpr::Constant(_) => {}
        ResolvedIntExpr::TokensCount(indices) => {
            for &p in indices {
                places.insert(p);
            }
        }
    }
}

#[cfg(test)]
#[path = "ltl_por_tests.rs"]
mod tests;
