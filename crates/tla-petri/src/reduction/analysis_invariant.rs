// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeMap;

use crate::invariant::{compute_p_invariants, structural_place_bound, PInvariant};
use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};

use super::model::{NeverDisablingArc, NeverDisablingProof, ParallelPlaceMerge};

fn div_ceil_u64(numerator: u64, denominator: u64) -> u64 {
    let quotient = numerator / denominator;
    let remainder = numerator % denominator;
    quotient + u64::from(remainder != 0)
}

fn compute_invariant_lower_bounds(
    net: &PetriNet,
    invariants: &[PInvariant],
) -> Vec<Option<NeverDisablingProof>> {
    let upper_bounds = (0..net.num_places())
        .map(|place_idx| structural_place_bound(invariants, place_idx))
        .collect::<Vec<_>>();
    let mut proofs: Vec<Option<NeverDisablingProof>> = vec![None; net.num_places()];

    for (invariant_idx, invariant) in invariants.iter().enumerate() {
        for (place_idx, &place_weight) in invariant.weights.iter().enumerate() {
            if place_weight == 0 {
                continue;
            }

            let mut other_support_upper_sum = 0u64;
            let mut missing_bound = false;
            for (other_idx, &other_weight) in invariant.weights.iter().enumerate() {
                if other_idx == place_idx || other_weight == 0 {
                    continue;
                }
                let Some(upper_bound) = upper_bounds[other_idx] else {
                    missing_bound = true;
                    break;
                };
                let Some(term) = other_weight.checked_mul(upper_bound) else {
                    missing_bound = true;
                    break;
                };
                let Some(sum) = other_support_upper_sum.checked_add(term) else {
                    missing_bound = true;
                    break;
                };
                other_support_upper_sum = sum;
            }
            if missing_bound {
                continue;
            }

            let residual = invariant
                .token_count
                .saturating_sub(other_support_upper_sum);
            let lower_bound = div_ceil_u64(residual, place_weight);
            if lower_bound == 0 {
                continue;
            }

            let candidate = NeverDisablingProof::PInvariant {
                invariant_idx,
                lower_bound,
            };
            let should_replace = match proofs[place_idx].as_ref() {
                Some(existing) => candidate.lower_bound() > existing.lower_bound(),
                None => true,
            };
            if should_replace {
                proofs[place_idx] = Some(candidate);
            }
        }
    }

    proofs
}

/// Find input arcs whose place has a proven structural token lower bound, so
/// the arc can never disable the transition (Tapaal Rule N).
pub(crate) fn find_never_disabling_arcs(
    net: &PetriNet,
    dead_transitions: &[TransitionIdx],
    self_loop_transitions: &[TransitionIdx],
    protected_places: &[bool],
) -> Vec<NeverDisablingArc> {
    let invariants = compute_p_invariants(net);
    if invariants.is_empty() {
        return Vec::new();
    }

    let lower_bounds = compute_invariant_lower_bounds(net, &invariants);

    let mut is_dead = vec![false; net.num_transitions()];
    for &TransitionIdx(t) in dead_transitions {
        is_dead[t as usize] = true;
    }
    let mut is_self_loop = vec![false; net.num_transitions()];
    for &TransitionIdx(t) in self_loop_transitions {
        is_self_loop[t as usize] = true;
    }

    let mut results = Vec::new();
    for (tidx, transition) in net.transitions.iter().enumerate() {
        if is_dead[tidx] || is_self_loop[tidx] {
            continue;
        }

        let mut required_inputs: BTreeMap<u32, u64> = BTreeMap::new();
        for arc in &transition.inputs {
            *required_inputs.entry(arc.place.0).or_default() += arc.weight;
        }

        for (place, weight) in required_inputs {
            let place_idx = place as usize;
            if protected_places.get(place_idx).copied().unwrap_or(false) {
                continue;
            }
            let Some(proof) = lower_bounds[place_idx].clone() else {
                continue;
            };
            if proof.lower_bound() >= weight {
                results.push(NeverDisablingArc {
                    transition: TransitionIdx(tidx as u32),
                    place: PlaceIdx(place),
                    weight,
                    proof,
                });
            }
        }
    }

    results.sort_by_key(|arc| (arc.transition.0, arc.place.0));
    results
}

/// Find query-unobserved places whose every live consumer already has a Rule N
/// proof, so the place can be elided in query-relevant reductions.
pub(crate) fn find_token_eliminated_places(
    net: &PetriNet,
    dead_transitions: &[TransitionIdx],
    self_loop_transitions: &[TransitionIdx],
    protected_places: &[bool],
    parallel_places: &[ParallelPlaceMerge],
    source_places: &[PlaceIdx],
    non_decreasing_places: &[PlaceIdx],
    never_disabling_arcs: &[NeverDisablingArc],
) -> Vec<PlaceIdx> {
    let mut is_dead = vec![false; net.num_transitions()];
    for &TransitionIdx(t) in dead_transitions {
        is_dead[t as usize] = true;
    }
    let mut is_self_loop = vec![false; net.num_transitions()];
    for &TransitionIdx(t) in self_loop_transitions {
        is_self_loop[t as usize] = true;
    }
    let mut is_source = vec![false; net.num_places()];
    for &PlaceIdx(p) in source_places {
        is_source[p as usize] = true;
    }
    let mut is_non_decreasing = vec![false; net.num_places()];
    for &PlaceIdx(p) in non_decreasing_places {
        is_non_decreasing[p as usize] = true;
    }
    let mut is_parallel_participant = vec![false; net.num_places()];
    for merge in parallel_places {
        is_parallel_participant[merge.canonical.0 as usize] = true;
        is_parallel_participant[merge.duplicate.0 as usize] = true;
    }

    let proof_map: BTreeMap<(u32, u32), u64> = never_disabling_arcs
        .iter()
        .map(|arc| ((arc.transition.0, arc.place.0), arc.proof.lower_bound()))
        .collect();

    let mut result = Vec::new();
    for place_idx in 0..net.num_places() {
        if protected_places.get(place_idx).copied().unwrap_or(false) {
            continue;
        }
        if is_source[place_idx] || is_non_decreasing[place_idx] {
            continue;
        }
        // Rule B carries an exact aliasing contract for parallel places. Keep
        // query-only token elimination off both sides of a merge so the
        // canonical/duplicate mapping cannot be degraded into a placeholder or
        // dropped entirely by asymmetric lower-bound proofs.
        if is_parallel_participant[place_idx] {
            continue;
        }

        let mut has_live_consumer = false;
        let mut all_consumers_proved = true;
        for (tidx, transition) in net.transitions.iter().enumerate() {
            if is_dead[tidx] || is_self_loop[tidx] {
                continue;
            }
            let consumed: u64 = transition
                .inputs
                .iter()
                .filter(|arc| arc.place.0 as usize == place_idx)
                .map(|arc| arc.weight)
                .sum();
            if consumed == 0 {
                continue;
            }
            has_live_consumer = true;
            let proof_lower_bound = proof_map
                .get(&(tidx as u32, place_idx as u32))
                .copied()
                .unwrap_or(0);
            if proof_lower_bound < consumed {
                all_consumers_proved = false;
                break;
            }
        }

        if has_live_consumer && all_consumers_proved {
            result.push(PlaceIdx(place_idx as u32));
        }
    }

    result
}

/// Find non-decreasing places that never constrain any transition (Tapaal Rule F).
///
/// A place `p` qualifies when:
/// 1. Every alive transition has net effect >= 0 on `p` (non-decreasing).
/// 2. The initial marking covers the maximum consumption from any single transition.
/// 3. `p` is not query-protected.
/// 4. `p` has at least one consumer (otherwise it is a source place, not Rule F).
/// 5. `p` is not already identified as a source place.
pub(crate) fn find_non_decreasing_places(
    net: &PetriNet,
    dead_transitions: &[TransitionIdx],
    protected_places: &[bool],
    source_places: &[PlaceIdx],
) -> Vec<PlaceIdx> {
    let mut is_dead = vec![false; net.num_transitions()];
    for &TransitionIdx(t) in dead_transitions {
        is_dead[t as usize] = true;
    }
    let mut is_source = vec![false; net.num_places()];
    for &PlaceIdx(p) in source_places {
        is_source[p as usize] = true;
    }

    let mut result = Vec::new();

    for place_idx in 0..net.num_places() {
        if protected_places.get(place_idx).copied().unwrap_or(false) {
            continue;
        }
        if is_source[place_idx] {
            continue;
        }

        let mut has_consumer = false;
        let mut non_decreasing = true;
        let mut max_consume: u64 = 0;

        for (tidx, t) in net.transitions.iter().enumerate() {
            if is_dead[tidx] {
                continue;
            }
            let consumes: u64 = t
                .inputs
                .iter()
                .filter(|arc| arc.place.0 as usize == place_idx)
                .map(|arc| arc.weight)
                .sum();
            let produces: u64 = t
                .outputs
                .iter()
                .filter(|arc| arc.place.0 as usize == place_idx)
                .map(|arc| arc.weight)
                .sum();

            if consumes > 0 {
                has_consumer = true;
                max_consume = max_consume.max(consumes);
            }
            if consumes > produces {
                non_decreasing = false;
                break;
            }
        }

        if non_decreasing && has_consumer && net.initial_marking[place_idx] >= max_consume {
            result.push(PlaceIdx(place_idx as u32));
        }
    }

    result
}

/// Find parallel places with identical connectivity and initial marking (Tapaal Rule B).
///
/// Two places are parallel (k=1 strict case) when they have identical
/// input/output arc patterns to all alive transitions and identical initial markings.
/// The duplicate can be removed since its marking always equals the canonical's.
pub(crate) fn find_parallel_places(
    net: &PetriNet,
    dead_transitions: &[TransitionIdx],
    protected_places: &[bool],
) -> Vec<ParallelPlaceMerge> {
    let mut is_dead = vec![false; net.num_transitions()];
    for &TransitionIdx(t) in dead_transitions {
        is_dead[t as usize] = true;
    }

    // Compute a signature for each place: sorted (transition_idx, direction_tag, weight).
    // direction_tag: 0 = input (place consumed by transition), 1 = output (produced by transition).
    let mut signatures: BTreeMap<Vec<(u32, u8, u64)>, Vec<usize>> = BTreeMap::new();

    for place_idx in 0..net.num_places() {
        if protected_places.get(place_idx).copied().unwrap_or(false) {
            continue;
        }

        let mut sig: Vec<(u32, u8, u64)> = Vec::new();
        let mut connected = false;

        for (tidx, t) in net.transitions.iter().enumerate() {
            if is_dead[tidx] {
                continue;
            }
            let consumes: u64 = t
                .inputs
                .iter()
                .filter(|arc| arc.place.0 as usize == place_idx)
                .map(|arc| arc.weight)
                .sum();
            let produces: u64 = t
                .outputs
                .iter()
                .filter(|arc| arc.place.0 as usize == place_idx)
                .map(|arc| arc.weight)
                .sum();

            if consumes > 0 {
                sig.push((tidx as u32, 0, consumes));
                connected = true;
            }
            if produces > 0 {
                sig.push((tidx as u32, 1, produces));
                connected = true;
            }
        }

        if !connected {
            continue; // isolated places handled elsewhere
        }

        signatures.entry(sig).or_default().push(place_idx);
    }

    let mut result = Vec::new();

    for places in signatures.values() {
        if places.len() < 2 {
            continue;
        }

        // Group by initial marking for strict k=1 match.
        let mut by_marking: BTreeMap<u64, Vec<usize>> = BTreeMap::new();
        for &p in places {
            by_marking
                .entry(net.initial_marking[p])
                .or_default()
                .push(p);
        }

        for group in by_marking.values() {
            if group.len() < 2 {
                continue;
            }
            let canonical = PlaceIdx(group[0] as u32);
            for &duplicate_idx in &group[1..] {
                result.push(ParallelPlaceMerge {
                    canonical,
                    duplicate: PlaceIdx(duplicate_idx as u32),
                });
            }
        }
    }

    result.sort_by_key(|m| m.duplicate.0);
    result
}
