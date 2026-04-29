// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Structural analysis for Petri nets.
//!
//! Provides verdicts without state-space exploration using siphon/trap
//! theory. A *trap* is a set of places T where every transition consuming
//! from T also produces into T: once marked, stays marked. A *siphon* is
//! the dual: once empty, stays empty.
//!
//! **Deadlock-freedom theorem:** If every minimal siphon contains a marked
//! trap, the net is deadlock-free (Murata 1989, §V-A).
//!
//! **Liveness shortcut:** On ordinary free-choice nets, the same
//! siphon/trap coverage is a strong positive signal for liveness. We use it
//! conservatively as a `TRUE` shortcut only.

use crate::petri_net::PetriNet;

/// Maximum number of minimal siphons before aborting enumeration.
/// Pathological nets can have exponentially many siphons.
const MAX_SIPHONS: usize = 10_000;

/// Check whether the net is ordinary (all arc weights are 1).
fn is_ordinary(net: &PetriNet) -> bool {
    net.transitions.iter().all(|transition| {
        transition.inputs.iter().all(|arc| arc.weight == 1)
            && transition.outputs.iter().all(|arc| arc.weight == 1)
    })
}

/// Check whether the net satisfies the ordinary free-choice condition.
///
/// For every place with multiple outgoing choices, each target transition
/// must have that place as its sole input.
fn is_ordinary_free_choice(net: &PetriNet) -> bool {
    if !is_ordinary(net) {
        return false;
    }

    let mut consumers: Vec<Vec<usize>> = vec![Vec::new(); net.num_places()];
    for (transition_idx, transition) in net.transitions.iter().enumerate() {
        for arc in &transition.inputs {
            consumers[arc.place.0 as usize].push(transition_idx);
        }
    }

    for (place_idx, place_consumers) in consumers.iter().enumerate() {
        if place_consumers.len() <= 1 {
            continue;
        }

        for &transition_idx in place_consumers {
            let transition = &net.transitions[transition_idx];
            if transition.inputs.len() != 1 || transition.inputs[0].place.0 as usize != place_idx {
                return false;
            }
        }
    }

    true
}

/// Check if a place set forms a trap in the net.
///
/// A trap T satisfies: for every transition t that consumes from T
/// (•t ∩ T ≠ ∅), t also produces into T (t• ∩ T ≠ ∅).
#[allow(dead_code)] // Used in tests; will be used by Commoner's theorem (Phase 3)
fn is_trap(net: &PetriNet, places: &[bool]) -> bool {
    for t in &net.transitions {
        let consumes_from_set = t.inputs.iter().any(|a| places[a.place.0 as usize]);
        if consumes_from_set {
            let produces_into_set = t.outputs.iter().any(|a| places[a.place.0 as usize]);
            if !produces_into_set {
                return false;
            }
        }
    }
    true
}

/// Check if a place set forms a siphon in the net.
///
/// A siphon S satisfies: for every transition t that produces into S
/// (t• ∩ S ≠ ∅), t also consumes from S (•t ∩ S ≠ ∅).
fn is_siphon(net: &PetriNet, places: &[bool]) -> bool {
    for t in &net.transitions {
        let produces_into_set = t.outputs.iter().any(|a| places[a.place.0 as usize]);
        if produces_into_set {
            let consumes_from_set = t.inputs.iter().any(|a| places[a.place.0 as usize]);
            if !consumes_from_set {
                return false;
            }
        }
    }
    true
}

/// Compute the siphon closure of an initial place set.
///
/// Start with the given places and expand: for every transition t that
/// produces into the current set but does NOT consume from it, add all
/// of t's input places to the set. Iterate until fixpoint.
fn siphon_closure(net: &PetriNet, initial: &[bool]) -> Vec<bool> {
    let num_places = net.num_places();
    let mut set = initial.to_vec();
    loop {
        let mut changed = false;
        for t in &net.transitions {
            let produces_into = t.outputs.iter().any(|a| set[a.place.0 as usize]);
            if !produces_into {
                continue;
            }
            let consumes_from = t.inputs.iter().any(|a| set[a.place.0 as usize]);
            if consumes_from {
                continue;
            }
            // t produces into set but doesn't consume from it — add t's inputs
            for a in &t.inputs {
                let p = a.place.0 as usize;
                if !set[p] {
                    set[p] = true;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    debug_assert!(is_siphon(net, &set), "siphon_closure must produce a siphon");
    // Check if it's actually a siphon (could be empty if initial was empty)
    let non_empty = set.iter().any(|&b| b);
    if !non_empty {
        return vec![false; num_places];
    }
    set
}

/// Try to minimize a siphon by removing one place at a time.
///
/// Returns a minimal siphon (no proper subset is also a siphon).
fn minimize_siphon(net: &PetriNet, siphon: &[bool]) -> Vec<bool> {
    let mut result = siphon.to_vec();
    for p in 0..result.len() {
        if !result[p] {
            continue;
        }
        result[p] = false;
        if !is_siphon(net, &result) || !result.iter().any(|&b| b) {
            result[p] = true; // must keep this place
        }
    }
    result
}

/// Enumerate minimal siphons using closure-then-minimize.
///
/// For each place, compute the siphon closure of {p}, then minimize.
/// Deduplicate results. Aborts if more than `MAX_SIPHONS` are found.
///
/// Returns `None` if enumeration was aborted (too many siphons).
fn minimal_siphons(net: &PetriNet) -> Option<Vec<Vec<bool>>> {
    let num_places = net.num_places();
    let mut siphons: Vec<Vec<bool>> = Vec::new();

    for seed_place in 0..num_places {
        let mut initial = vec![false; num_places];
        initial[seed_place] = true;
        let closure = siphon_closure(net, &initial);
        if !closure.iter().any(|&b| b) {
            continue;
        }
        let minimal = minimize_siphon(net, &closure);
        if !minimal.iter().any(|&b| b) {
            continue;
        }
        // Deduplicate
        if !siphons.iter().any(|s| s == &minimal) {
            siphons.push(minimal);
            if siphons.len() > MAX_SIPHONS {
                return None; // too many siphons, abort
            }
        }
    }
    Some(siphons)
}

/// Check if a siphon contains a marked trap (a subset that is both a trap
/// and contains at least one initially marked place).
fn contains_marked_trap(net: &PetriNet, siphon: &[bool]) -> bool {
    let num_places = net.num_places();
    // Strategy: find a marked subset of the siphon that forms a trap.
    // Start with all initially marked places within the siphon (the "marked
    // core"), then use trap closure to extend it. If the result is still
    // within the siphon and is a trap, we're done.
    //
    // Trap closure: for each transition t that produces into the current set
    // but does NOT consume from it, we must add places to make t consume
    // from the set. But that's the wrong direction for traps.
    //
    // Instead, use a simpler approach: the "maximal trap within the siphon"
    // is computable by iterative removal. Start with all siphon places,
    // remove any place p where some transition consumes from {p} but
    // doesn't produce into the remaining set. Iterate until fixpoint.
    let mut trap_candidate: Vec<bool> = siphon.to_vec();
    loop {
        let mut changed = false;
        for p in 0..num_places {
            if !trap_candidate[p] {
                continue;
            }
            // Check if removing p would still leave a trap
            // Actually: check if every transition consuming from p also
            // produces into the candidate set (trap condition for p)
            let p_ok = net.transitions.iter().all(|t| {
                let consumes_p = t.inputs.iter().any(|a| a.place.0 as usize == p);
                if !consumes_p {
                    return true; // transition doesn't touch p
                }
                // t consumes from p — must produce into trap_candidate
                t.outputs.iter().any(|a| trap_candidate[a.place.0 as usize])
            });
            if !p_ok {
                trap_candidate[p] = false;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    // The remaining trap_candidate is the maximal trap within the siphon.
    // Check if it's non-empty and marked.
    trap_candidate
        .iter()
        .enumerate()
        .any(|(p, &in_trap)| in_trap && net.initial_marking[p] > 0)
}

/// LP-based deadlock-freedom check for arbitrary Petri nets.
///
/// For each transition t, uses the LP state equation relaxation to check if
/// ALL input places always have sufficient tokens (m(p) >= w(p,t) in all
/// reachable markings). If any transition is provably always enabled, the
/// net is deadlock-free.
///
/// **Sound for ALL Petri net classes** — not limited to free-choice or
/// ordinary nets. The LP overapproximates the reachable set, so "always
/// enabled" in the LP implies always enabled in reality.
///
/// Returns:
/// - `Some(true)` if some transition is LP-proved always enabled
/// - `None` if inconclusive (no transition proved always enabled)
///
/// Does NOT return `Some(false)` — LP feasibility of disabling does not
/// prove a deadlock is actually reachable.
pub(crate) fn lp_deadlock_free(net: &PetriNet) -> Option<bool> {
    use crate::lp_state_equation::lp_strictly_greater_unreachable;
    use crate::petri_net::PlaceIdx;
    use crate::resolved_predicate::ResolvedIntExpr;

    if net.num_transitions() == 0 {
        return None;
    }

    for transition in &net.transitions {
        if transition.inputs.is_empty() {
            // Source transition (no inputs) is always enabled → deadlock-free.
            return Some(true);
        }

        let all_inputs_always_sufficient = transition.inputs.iter().all(|arc| {
            // Check: is w > m(p) LP-infeasible?
            // If yes → m(p) >= w always holds → this input is always satisfied.
            lp_strictly_greater_unreachable(
                net,
                &ResolvedIntExpr::Constant(arc.weight),
                &ResolvedIntExpr::TokensCount(vec![PlaceIdx(arc.place.0)]),
            )
        });

        if all_inputs_always_sufficient {
            return Some(true);
        }
    }

    None
}

/// LP-based dead-transition detection for arbitrary Petri nets.
///
/// For each transition t, checks if SOME input place can never have enough
/// tokens for t to fire (the LP upper bound for m(p) is strictly less than
/// the required arc weight). If any transition is LP-proved dead, the net
/// is NOT live.
///
/// **Sound for ALL Petri net classes.** The LP overapproximates reachable
/// markings: if even the LP says the place can't reach the required count,
/// it truly can't.
///
/// Returns `Some(false)` if a dead transition is found, `None` otherwise.
pub(crate) fn lp_dead_transition(net: &PetriNet) -> Option<bool> {
    use crate::lp_state_equation::lp_upper_bound;
    use crate::petri_net::PlaceIdx;

    for transition in &net.transitions {
        for arc in &transition.inputs {
            let upper = lp_upper_bound(net, &[PlaceIdx(arc.place.0)]);
            if let Some(bound) = upper {
                if bound < arc.weight {
                    // This place can never have enough tokens → transition dead.
                    return Some(false);
                }
            }
        }
    }

    None
}

fn minimal_siphons_have_marked_traps(net: &PetriNet) -> Option<bool> {
    let siphons = minimal_siphons(net)?;
    Some(
        siphons
            .iter()
            .all(|siphon| contains_marked_trap(net, siphon)),
    )
}

/// Structural deadlock-freedom analysis for ordinary free-choice nets.
///
/// Returns `Some(true)` if the net is ordinary free-choice and provably
/// deadlock-free (every minimal siphon contains a marked trap).
/// Returns `Some(false)` if the net is ordinary free-choice but a siphon
/// vulnerability exists. Returns `None` if the net is not ordinary
/// free-choice or siphon enumeration was aborted.
pub(crate) fn structural_deadlock_free(net: &PetriNet) -> Option<bool> {
    // A net with no transitions is always deadlocked — the theorem about
    // "some transition is always enabled" is vacuously false.
    if net.num_transitions() == 0 {
        return Some(false);
    }
    if !is_ordinary_free_choice(net) {
        // The siphon/trap theorem holds for ALL ordinary nets (Murata 1989),
        // but our siphon enumerator uses single-place seeds which is only
        // complete for free-choice nets. Non-free-choice nets can have
        // minimal siphons requiring multi-place seeds — missing one causes
        // false Some(true). See: wrong_answer_investigation_tests::
        // test_squaregrid_deadlock_structural_not_falsely_free
        return None;
    }
    let all_covered = minimal_siphons_have_marked_traps(net)?;
    if all_covered {
        Some(true)
    } else {
        // FALSE direction: sound for free-choice (enumerator is complete).
        Some(false)
    }
}

/// Structural liveness signal for ordinary free-choice nets.
///
/// Returns:
/// - `Some(true)` when the net is ordinary free-choice and every minimal
///   siphon contains a marked trap
/// - `Some(false)` when the net is ordinary free-choice but the coverage test
///   fails
/// - `None` when the theorem does not apply (non-free-choice / non-ordinary)
///   or siphon enumeration aborts
///
/// Callers should currently only trust `Some(true)` as a shortcut.
pub(crate) fn structural_live(net: &PetriNet) -> Option<bool> {
    if !is_ordinary_free_choice(net) {
        return None;
    }

    minimal_siphons_have_marked_traps(net)
}

/// Structural non-liveness via T-semiflow coverage.
///
/// Returns `Some(false)` if any transition is NOT covered by any T-semiflow
/// AND the net is bounded (proved via P-invariants covering all places).
/// Returns `None` if all transitions are covered or boundedness cannot be
/// proved structurally.
///
/// **Sound for ALL Petri net classes** (not just free-choice). This
/// complements `structural_live` which only handles free-choice nets.
///
/// The theorem: in a bounded net, a transition not in any T-semiflow
/// can fire at most finitely many times — contradicting L4-liveness.
pub(crate) fn structural_not_live_t_semiflows(net: &PetriNet) -> Option<bool> {
    use crate::invariant::{
        all_transitions_covered, compute_p_invariants, compute_t_semiflows, structural_place_bound,
    };

    if net.num_transitions() == 0 {
        return None;
    }

    let result = compute_t_semiflows(net);
    if all_transitions_covered(&result.semiflows, net.num_transitions()) {
        return None; // all covered — can't conclude non-liveness
    }
    // If Farkas was truncated, we may be missing semiflows that would cover
    // the transition — can't soundly conclude non-coverage.
    if !result.complete {
        return None;
    }

    // Uncovered transition found. Need boundedness for the theorem to apply.
    // Check if P-invariants structurally bound every place.
    let p_inv = compute_p_invariants(net);
    let all_bounded = (0..net.num_places()).all(|p| structural_place_bound(&p_inv, p).is_some());

    if all_bounded {
        Some(false) // bounded + uncovered transition → NOT live
    } else {
        None // can't prove boundedness
    }
}

#[cfg(test)]
#[path = "structural_tests.rs"]
mod tests;
