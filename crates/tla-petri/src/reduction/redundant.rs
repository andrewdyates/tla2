// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LP-based redundant place detection for structural reduction.
//!
//! A place `p` is **redundant** (also called "structurally implicit") if:
//! 1. Its marking is determined by other places via a P-invariant (reconstructable).
//! 2. It never constrains any transition (LP-verified).
//!
//! Both conditions are needed: (1) enables value reconstruction for property
//! evaluation, (2) ensures the enabled-transition set is preserved.
//!
//! The LP check for condition (2): for each transition `t` consuming from `p`,
//! minimize `M(p)` subject to the state equation and all other preconditions
//! of `t` being satisfied. If the minimum `>= W^-(p,t)`, then `p` never
//! blocks `t`. If this holds for all such transitions, `p` is redundant.
//!
//! Reference: Colom & Silva (1991), "Improving the linearly based
//! characterization of P/T nets." LNCS 483.

use minilp::{ComparisonOp, OptimizationDirection, Problem};

use crate::invariant::{compute_p_invariants, ImpliedPlace, ImpliedPlaceReconstruction};
use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};

/// Check whether place `p` is LP-redundant: never constrains any alive transition.
fn is_lp_redundant(net: &PetriNet, place_idx: usize, dead_set: &[bool]) -> bool {
    let place = PlaceIdx(place_idx as u32);
    for (tidx, trans) in net.transitions.iter().enumerate() {
        if dead_set[tidx] {
            continue;
        }
        for arc in &trans.inputs {
            if arc.place == place
                && !place_never_constrains_transition(
                    net,
                    place,
                    TransitionIdx(tidx as u32),
                    arc.weight,
                )
            {
                return false;
            }
        }
    }
    true
}

/// Maximum LP variables before skipping redundancy check.
const MAX_LP_VARIABLES: usize = 50_000;

/// Check whether place `p` never constrains transition `t` via LP.
///
/// Returns `true` if the minimum marking of `p` (under the state equation
/// with all other preconditions of `t` satisfied) is >= the input weight.
fn place_never_constrains_transition(
    net: &PetriNet,
    place: PlaceIdx,
    transition: TransitionIdx,
    input_weight: u64,
) -> bool {
    let np = net.num_places();
    let nt = net.num_transitions();
    let p = place.0 as usize;
    let t = transition.0 as usize;

    let mut problem = Problem::new(OptimizationDirection::Minimize);

    // Firing count variables x[t] >= 0.
    let x_vars: Vec<_> = (0..nt)
        .map(|_| problem.add_var(0.0, (0.0, f64::INFINITY)))
        .collect();

    // Marking variables M[p] >= 0. Objective: minimize M[place].
    let m_vars: Vec<_> = (0..np)
        .map(|i| {
            let obj = if i == p { 1.0 } else { 0.0 };
            problem.add_var(obj, (0.0, f64::INFINITY))
        })
        .collect();

    // State equation: M[p] = M0[p] + sum_t C[p][t]*x[t] for each place.
    for pidx in 0..np {
        let mut row = vec![(m_vars[pidx], 1.0)];
        for (tidx, trans) in net.transitions.iter().enumerate() {
            let mut coeff = 0.0_f64;
            for arc in &trans.inputs {
                if arc.place.0 as usize == pidx {
                    coeff += arc.weight as f64;
                }
            }
            for arc in &trans.outputs {
                if arc.place.0 as usize == pidx {
                    coeff -= arc.weight as f64;
                }
            }
            if coeff.abs() > f64::EPSILON {
                row.push((x_vars[tidx], coeff));
            }
        }
        problem.add_constraint(&row, ComparisonOp::Eq, net.initial_marking[pidx] as f64);
    }

    // Other preconditions of transition t: M[q] >= W^-(q,t) for all q != p.
    let trans = &net.transitions[t];
    for arc in &trans.inputs {
        if arc.place == place {
            continue;
        }
        let q = arc.place.0 as usize;
        problem.add_constraint([(m_vars[q], 1.0)], ComparisonOp::Ge, arc.weight as f64);
    }

    match problem.solve() {
        Ok(solution) => solution.objective() >= (input_weight as f64) - 0.5,
        // Infeasible means the other preconditions can never be jointly satisfied,
        // so `t` can never fire regardless of p. Place `p` is trivially non-constraining.
        Err(minilp::Error::Infeasible) => true,
        Err(minilp::Error::Unbounded) => false,
    }
}

/// Find places that are both P-invariant-implied and LP-redundant.
///
/// Uses LP-first selection: for each invariant, tests LP feasibility of
/// candidates BEFORE committing to removal. This avoids the greedy pitfall
/// where `find_implied_places` selects a non-LP-redundant place first,
/// blocking an actually LP-redundant place from a later invariant.
///
/// Excludes places already marked for removal by other reduction rules.
/// Places in `protected_places` (e.g. self-loop-touching places) are
/// excluded from candidacy to preserve soundness of downstream consumers
/// that need `place_map` or `constant_value` lookups for those places.
pub(crate) fn find_redundant_places(
    net: &PetriNet,
    already_removed: &[bool],
    dead_transitions: &[TransitionIdx],
    protected_places: &[bool],
) -> Vec<ImpliedPlace> {
    let np = net.num_places();
    let nt = net.num_transitions();

    if np + nt > MAX_LP_VARIABLES {
        return Vec::new();
    }

    let dead_set: Vec<bool> = {
        let mut d = vec![false; nt];
        for &TransitionIdx(t) in dead_transitions {
            d[t as usize] = true;
        }
        d
    };

    let invariants = compute_p_invariants(net);
    if invariants.is_empty() {
        return Vec::new();
    }

    // Sort invariants by ascending support size (tighter invariants first).
    let mut sorted_indices: Vec<usize> = (0..invariants.len()).collect();
    sorted_indices.sort_by_key(|&i| invariants[i].weights.iter().filter(|&&w| w > 0).count());

    let mut removed = vec![false; np];
    let mut must_keep = vec![false; np];
    let mut result = Vec::new();

    for (p, &r) in already_removed.iter().enumerate() {
        if r {
            removed[p] = true;
        }
    }
    // Self-loop-touching places must not become LP-redundancy candidates.
    for (p, &protected) in protected_places.iter().enumerate() {
        if protected {
            must_keep[p] = true;
        }
    }

    for &inv_idx in &sorted_indices {
        let inv = &invariants[inv_idx];
        let support: Vec<usize> = inv
            .weights
            .iter()
            .enumerate()
            .filter(|(_, &w)| w > 0)
            .map(|(p, _)| p)
            .collect();

        if support.len() < 2 {
            continue;
        }

        // Collect candidates: not removed, not must_keep, all other support non-removed.
        let mut candidates: Vec<usize> = support
            .iter()
            .copied()
            .filter(|&p| !removed[p] && !must_keep[p])
            .filter(|&p| support.iter().all(|&q| q == p || !removed[q]))
            .collect();

        // Prefer weight-1 candidates (exact division), then by weight ascending.
        candidates.sort_by_key(|&p| {
            if inv.weights[p] == 1 {
                0u64
            } else {
                inv.weights[p]
            }
        });

        // LP-first selection: try each candidate, pick the first that passes LP.
        for &candidate in &candidates {
            if !is_lp_redundant(net, candidate, &dead_set) {
                continue;
            }

            let terms: Vec<(usize, u64)> = support
                .iter()
                .filter(|&&p| p != candidate)
                .map(|&p| (p, inv.weights[p]))
                .collect();

            removed[candidate] = true;
            for &p in &support {
                if p != candidate {
                    must_keep[p] = true;
                }
            }

            result.push(ImpliedPlace {
                place: candidate,
                reconstruction: ImpliedPlaceReconstruction {
                    constant: inv.token_count,
                    divisor: inv.weights[candidate],
                    terms,
                },
            });
            break;
        }
    }

    result.sort_by_key(|ip| ip.place);
    result
}
