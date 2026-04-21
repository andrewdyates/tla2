// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-net structural facts used by the formula simplifier.
//!
//! Computed once before simplification and shared across all properties
//! of a given examination.

use crate::invariant::{compute_p_invariants, structural_place_bound};
use crate::petri_net::PetriNet;
use crate::structural::structural_deadlock_free;

/// A two-place P-invariant relation: `lhs_weight * p_lhs + rhs_weight * p_rhs = constant`.
///
/// Used for cheap pairwise implication rewrites inside `And`/`Or` nodes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BinaryInvariant {
    pub lhs_place: usize,
    pub lhs_weight: u64,
    pub rhs_place: usize,
    pub rhs_weight: u64,
    pub constant: u64,
}

/// Bundle of structural facts about a Petri net, computed once and
/// reused across all property simplifications.
#[derive(Clone)]
pub(crate) struct SimplificationFacts {
    /// `Some(true)` if the net is provably deadlock-free, `Some(false)` if a
    /// deadlock is structurally guaranteed, `None` if inconclusive.
    pub deadlock_free: Option<bool>,

    /// `true` for transitions that can never fire because some input arc
    /// requires more tokens than the P-invariant upper bound for that place.
    pub structurally_disabled: Vec<bool>,

    /// Two-place P-invariant relations for pairwise implication rewrites.
    pub binary_invariants: Vec<BinaryInvariant>,
}

/// Compute structural simplification facts from a Petri net.
pub(crate) fn compute_facts(net: &PetriNet) -> SimplificationFacts {
    let deadlock_free = structural_deadlock_free(net);

    let invariants = compute_p_invariants(net);
    let place_bounds: Vec<Option<u64>> = (0..net.num_places())
        .map(|p| structural_place_bound(&invariants, p))
        .collect();

    let structurally_disabled: Vec<bool> = net
        .transitions
        .iter()
        .map(|t| {
            t.inputs.iter().any(|arc| {
                if let Some(bound) = place_bounds[arc.place.0 as usize] {
                    bound < arc.weight
                } else {
                    false
                }
            })
        })
        .collect();

    let binary_invariants = extract_binary_invariants(&invariants);

    SimplificationFacts {
        deadlock_free,
        structurally_disabled,
        binary_invariants,
    }
}

/// Extract two-place P-invariant relations from the full invariant set.
///
/// For each invariant whose support has exactly two places, emit the
/// relation in canonical form (lower place index first).
fn extract_binary_invariants(invariants: &[crate::invariant::PInvariant]) -> Vec<BinaryInvariant> {
    let mut result = Vec::new();
    for inv in invariants {
        let support: Vec<(usize, u64)> = inv
            .weights
            .iter()
            .enumerate()
            .filter(|(_, &w)| w > 0)
            .map(|(i, &w)| (i, w))
            .collect();
        if support.len() == 2 {
            let (p0, w0) = support[0];
            let (p1, w1) = support[1];
            result.push(BinaryInvariant {
                lhs_place: p0,
                lhs_weight: w0,
                rhs_place: p1,
                rhs_weight: w1,
                constant: inv.token_count,
            });
        }
    }
    result
}
