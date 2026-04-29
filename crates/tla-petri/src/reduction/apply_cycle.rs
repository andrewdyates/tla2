// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tapaal Rule H transform pass: token cycle compression.
//!
//! Given a set of [`TokenCycle`]s (produced by [`find_token_cycles`]), this
//! module rewrites the [`PetriNet`] in place by:
//!
//! 1. Collapsing every non-survivor place in each cycle into the cycle's
//!    `survivor` place (summing initial markings, redirecting all external
//!    arcs that referenced the removed place to the survivor).
//! 2. Deleting the cycle transitions: after place-merging, each cycle
//!    transition consumes 1 from `survivor` and produces 1 into `survivor`,
//!    i.e. it is a self-loop with zero net effect. Removing such transitions
//!    preserves reachable markings.
//! 3. Compacting the place and transition vectors so surviving indices are
//!    dense.
//!
//! # Soundness
//!
//! Rule H is safe for **reachability** and any property class that does not
//! observe individual positions around a token cycle. Because cycle
//! transitions have a single unit-weight input and a single unit-weight
//! output (a "simple" transition), their only effect is to shuffle a token
//! from one cycle place to the next. The aggregate token count over all
//! cycle places is preserved by every firing. Folding the cycle places into
//! one preserves:
//!
//! - The total number of tokens initially on the cycle (`sum(initial_marking)`).
//! - The enabling of any external transition that reads from or writes to a
//!   cycle place (the arc is redirected to the survivor; weights sum when
//!   multiple cycle places connected to the same external transition).
//! - The net effect of firing any external transition on cycle places.
//!
//! The cycle transitions themselves disappear, which is sound because their
//! net effect on the merged place is zero (consume 1, produce 1 on the same
//! place), i.e. they are indistinguishable from stuttering.
//!
//! # Query protection
//!
//! The detection pass ([`find_token_cycles`]) already excludes cycles whose
//! places appear in the query mask. This transform does **not** re-check
//! protection — callers must supply cycles from a query-aware detection run.
//!
//! # Not wired to the full fixpoint
//!
//! This function operates on a raw [`PetriNet`], not a [`ReducedNet`]. It is
//! exposed for unit testing and for a future integration slice that extends
//! [`ReductionReport`] with a Rule H record and threads place/transition
//! remappings through `materialize::build_reduced_net`. See the #4236 follow-up.
//!
//! [`find_token_cycles`]: super::analysis_cycle::find_token_cycles
//! [`ReducedNet`]: super::ReducedNet
//! [`ReductionReport`]: super::model::ReductionReport

use std::collections::BTreeMap;

use crate::petri_net::{Arc, PetriNet, PlaceIdx, TransitionIdx};

use super::analysis_cycle::TokenCycle;

/// Apply Rule H token cycle compression to `net`.
///
/// Each [`TokenCycle`] in `cycles` is collapsed into its `survivor` place:
/// non-survivor cycle places are merged into the survivor, their arcs
/// redirected, their initial markings summed. The cycle transitions are then
/// removed as they reduce to self-loops with zero net effect.
///
/// After processing, the net's place and transition vectors are compacted so
/// surviving indices are dense.
///
/// Returns the number of (places_removed, transitions_removed).
///
/// # Invariants (not re-checked — supply cycles from [`find_token_cycles`])
///
/// - Every transition in `cycle.transitions` must be a simple transition
///   (one input arc, one output arc, both weight 1, input place != output place).
/// - Consecutive cycle transitions must form a connected cycle:
///   `output(transitions[i]) == input(transitions[(i+1) % k])`.
/// - No cycle place may be query-protected (caller responsibility).
///
/// # Overlapping cycles
///
/// If two cycles share places (e.g. two cycles meeting at a common survivor),
/// the transform processes them in order. The first cycle's merge may remove
/// places referenced by a later cycle; those stale references are detected and
/// the later cycle is skipped. This is a conservative safety net; callers who
/// want maximum compression should re-run detection + transform as a fixpoint.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn apply_token_cycles(net: &mut PetriNet, cycles: &[TokenCycle]) -> (usize, usize) {
    if cycles.is_empty() {
        return (0, 0);
    }

    let num_places = net.num_places();
    let num_transitions = net.num_transitions();

    // For each original place, record which surviving place it maps to
    // (a place is "absorbed" if it is a non-survivor cycle place).
    let mut place_redirect: Vec<PlaceIdx> = (0..num_places).map(|p| PlaceIdx(p as u32)).collect();

    // Whether each place is removed (absorbed into another).
    let mut place_removed = vec![false; num_places];

    // Whether each transition is removed (cycle transition).
    let mut trans_removed = vec![false; num_transitions];

    // Process cycles one at a time. A later cycle may reference places that
    // were already merged; resolve through `place_redirect` (union-find style
    // with path compression).
    for cycle in cycles {
        // Resolve each cycle place through the redirect chain.
        let resolved_places: Vec<PlaceIdx> = cycle
            .places
            .iter()
            .map(|&p| resolve_redirect(&mut place_redirect, p))
            .collect();
        let survivor = resolve_redirect(&mut place_redirect, cycle.survivor);

        // If resolution collapsed the cycle (e.g. an overlapping earlier
        // cycle already merged everything), nothing to do.
        if resolved_places.iter().all(|&p| p == survivor) {
            // Still remove the cycle transitions (they are now self-loops on
            // survivor, semantically no-ops).
            for &TransitionIdx(t) in &cycle.transitions {
                if (t as usize) < num_transitions {
                    trans_removed[t as usize] = true;
                }
            }
            continue;
        }

        // Merge each non-survivor cycle place into survivor.
        for &place in &resolved_places {
            if place == survivor {
                continue;
            }
            let pidx = place.0 as usize;
            if place_removed[pidx] {
                continue;
            }
            place_redirect[pidx] = survivor;
            place_removed[pidx] = true;
        }

        // Remove the cycle transitions.
        for &TransitionIdx(t) in &cycle.transitions {
            if (t as usize) < num_transitions {
                trans_removed[t as usize] = true;
            }
        }
    }

    // Path-compress all redirects to point at final survivors.
    for p in 0..num_places {
        let _ = resolve_redirect(&mut place_redirect, PlaceIdx(p as u32));
    }

    // Sum initial markings into survivors.
    let mut new_initial = vec![0u64; num_places];
    for (p, &tokens) in net.initial_marking.iter().enumerate() {
        let survivor = place_redirect[p];
        new_initial[survivor.0 as usize] += tokens;
    }

    // Rewrite every surviving transition's arcs through `place_redirect`,
    // combining duplicates and dropping zero-weight arcs.
    for (tidx, transition) in net.transitions.iter_mut().enumerate() {
        if trans_removed[tidx] {
            continue;
        }
        transition.inputs = redirect_and_combine(&transition.inputs, &place_redirect);
        transition.outputs = redirect_and_combine(&transition.outputs, &place_redirect);
    }

    // Compact: remove absorbed places and cycle transitions, re-number indices.
    let (new_place_index, places_removed) = compact_places(net, &place_removed, &mut new_initial);
    let transitions_removed = compact_transitions(net, &trans_removed, &new_place_index);

    net.initial_marking = new_initial;

    (places_removed, transitions_removed)
}

/// Resolve a place through the redirect array with path compression.
fn resolve_redirect(place_redirect: &mut [PlaceIdx], place: PlaceIdx) -> PlaceIdx {
    let mut current = place;
    loop {
        let next = place_redirect[current.0 as usize];
        if next == current {
            break;
        }
        current = next;
    }
    // Path compression: point `place` directly at the resolved root.
    let root = current;
    let mut walker = place;
    while place_redirect[walker.0 as usize] != root {
        let next = place_redirect[walker.0 as usize];
        place_redirect[walker.0 as usize] = root;
        walker = next;
    }
    root
}

/// Redirect arcs through `place_redirect`, summing weights on duplicate
/// destinations and dropping zero-weight arcs.
fn redirect_and_combine(arcs: &[Arc], place_redirect: &[PlaceIdx]) -> Vec<Arc> {
    let mut combined: BTreeMap<u32, u64> = BTreeMap::new();
    for arc in arcs {
        let new_place = place_redirect[arc.place.0 as usize];
        *combined.entry(new_place.0).or_default() += arc.weight;
    }
    combined
        .into_iter()
        .filter(|(_, w)| *w > 0)
        .map(|(p, weight)| Arc {
            place: PlaceIdx(p),
            weight,
        })
        .collect()
}

/// Compact the places vector, dropping `place_removed[i] == true` entries.
///
/// Updates `new_initial` in place (shrinks to dense indexing).
/// Returns a map from old place idx to new place idx (None = removed), and the
/// number of removed places.
fn compact_places(
    net: &mut PetriNet,
    place_removed: &[bool],
    new_initial: &mut Vec<u64>,
) -> (Vec<Option<PlaceIdx>>, usize) {
    let num_places = net.num_places();
    let mut new_place_index: Vec<Option<PlaceIdx>> = vec![None; num_places];
    let mut next_idx: u32 = 0;
    let mut compacted_initial = Vec::with_capacity(num_places);
    let mut compacted_places = Vec::with_capacity(num_places);

    for (p, &removed) in place_removed.iter().enumerate() {
        if !removed {
            new_place_index[p] = Some(PlaceIdx(next_idx));
            compacted_initial.push(new_initial[p]);
            compacted_places.push(net.places[p].clone());
            next_idx += 1;
        }
    }

    let removed_count = num_places - (next_idx as usize);
    *new_initial = compacted_initial;
    net.places = compacted_places;

    (new_place_index, removed_count)
}

/// Compact the transitions vector, dropping removed entries and rewriting arcs
/// through `new_place_index`.
fn compact_transitions(
    net: &mut PetriNet,
    trans_removed: &[bool],
    new_place_index: &[Option<PlaceIdx>],
) -> usize {
    let num_transitions = net.num_transitions();
    let mut kept = Vec::with_capacity(num_transitions);
    let mut removed_count = 0;

    for (tidx, transition) in net.transitions.drain(..).enumerate() {
        if trans_removed[tidx] {
            removed_count += 1;
            continue;
        }
        let mut t = transition;
        t.inputs = remap_arcs(&t.inputs, new_place_index);
        t.outputs = remap_arcs(&t.outputs, new_place_index);
        kept.push(t);
    }

    net.transitions = kept;
    removed_count
}

/// Remap arc places through `new_place_index`, dropping arcs whose place was
/// removed (should not happen if transforms are consistent, but guarded
/// defensively).
fn remap_arcs(arcs: &[Arc], new_place_index: &[Option<PlaceIdx>]) -> Vec<Arc> {
    arcs.iter()
        .filter_map(|arc| {
            new_place_index[arc.place.0 as usize].map(|new_place| Arc {
                place: new_place,
                weight: arc.weight,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::petri_net::{Arc, PlaceInfo, TransitionInfo};

    use super::super::analysis_cycle::find_token_cycles;
    use super::*;

    fn place(id: &str) -> PlaceInfo {
        PlaceInfo {
            id: id.to_string(),
            name: Some(id.to_string()),
        }
    }

    fn arc(place: u32, weight: u64) -> Arc {
        Arc {
            place: PlaceIdx(place),
            weight,
        }
    }

    fn trans(id: &str, inputs: Vec<Arc>, outputs: Vec<Arc>) -> TransitionInfo {
        TransitionInfo {
            id: id.to_string(),
            name: Some(id.to_string()),
            inputs,
            outputs,
        }
    }

    /// Simple 2-place cycle: one token rotating between p0 and p1.
    /// Expected result: single place with the token, no transitions.
    #[test]
    fn test_two_cycle_merges_to_one_place_no_transitions() {
        let mut net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![
                trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 0],
        };

        let cycles = find_token_cycles(&net, &[], &[false, false]);
        assert_eq!(cycles.len(), 1);

        let (places_removed, trans_removed) = apply_token_cycles(&mut net, &cycles);
        assert_eq!(places_removed, 1);
        assert_eq!(trans_removed, 2);
        assert_eq!(net.num_places(), 1);
        assert_eq!(net.num_transitions(), 0);
        // Single surviving place holds the single cycle token.
        assert_eq!(net.initial_marking, vec![1]);
    }

    /// 3-place cycle: three tokens distributed around, should collapse to one
    /// place holding 3 tokens total.
    #[test]
    fn test_three_cycle_sums_initial_markings() {
        let mut net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1"), place("p2")],
            transitions: vec![
                trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
                trans("t2", vec![arc(2, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 1, 1],
        };

        let cycles = find_token_cycles(&net, &[], &[false, false, false]);
        let (places_removed, trans_removed) = apply_token_cycles(&mut net, &cycles);

        assert_eq!(places_removed, 2);
        assert_eq!(trans_removed, 3);
        assert_eq!(net.num_places(), 1);
        assert_eq!(net.num_transitions(), 0);
        assert_eq!(net.initial_marking, vec![3]);
    }

    /// External transition that reads from a cycle place: after merge, it
    /// should read from the survivor.
    #[test]
    fn test_external_consumer_redirected_to_survivor() {
        let mut net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1"), place("sink")],
            transitions: vec![
                trans("t_cycle_0", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t_cycle_1", vec![arc(1, 1)], vec![arc(0, 1)]),
                // External transition consuming from p1 (the non-survivor).
                trans("t_ext", vec![arc(1, 1)], vec![arc(2, 1)]),
            ],
            initial_marking: vec![1, 0, 0],
        };

        // The external consumer makes t_cycle_1's input place p1 have two
        // consumers (t_cycle_0 in the cycle DFS path + t_ext). That's fine —
        // detection only requires each cycle transition be simple.
        let cycles = find_token_cycles(&net, &[], &[false, false, false]);
        assert_eq!(cycles.len(), 1);

        apply_token_cycles(&mut net, &cycles);

        // One place removed (p1 absorbed into p0), two transitions removed
        // (cycle transitions), one surviving external transition.
        assert_eq!(net.num_places(), 2);
        assert_eq!(net.num_transitions(), 1);
        // External transition now reads from the survivor (new index 0).
        let t_ext = &net.transitions[0];
        assert_eq!(t_ext.inputs.len(), 1);
        assert_eq!(t_ext.inputs[0].place, PlaceIdx(0));
        assert_eq!(t_ext.inputs[0].weight, 1);
        // Marking: survivor has 1 (was on p0 originally).
        assert_eq!(net.initial_marking, vec![1, 0]);
    }

    /// External transition that produces into a cycle place: after merge, it
    /// should produce into the survivor.
    #[test]
    fn test_external_producer_redirected_to_survivor() {
        let mut net = PetriNet {
            name: None,
            places: vec![place("source"), place("p0"), place("p1")],
            transitions: vec![
                // External producer into p1 (non-survivor of cycle {p0, p1}).
                trans("t_ext", vec![arc(0, 1)], vec![arc(2, 1)]),
                trans("t_cycle_0", vec![arc(1, 1)], vec![arc(2, 1)]),
                trans("t_cycle_1", vec![arc(2, 1)], vec![arc(1, 1)]),
            ],
            initial_marking: vec![2, 1, 0],
        };

        let cycles = find_token_cycles(&net, &[], &[false, false, false]);
        assert_eq!(cycles.len(), 1);

        apply_token_cycles(&mut net, &cycles);

        assert_eq!(net.num_places(), 2);
        assert_eq!(net.num_transitions(), 1);
        // t_ext's output points at the survivor (place 1 in the compacted
        // net, which is the cycle's survivor p0 at original idx 1).
        let t_ext = &net.transitions[0];
        assert_eq!(t_ext.outputs.len(), 1);
        assert_eq!(t_ext.outputs[0].place, PlaceIdx(1));
        assert_eq!(t_ext.outputs[0].weight, 1);
    }

    /// External transition touching both cycle places: after merge, its two
    /// arcs collapse to one with the summed weight.
    #[test]
    fn test_arc_weights_sum_on_merge() {
        let mut net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1"), place("sink")],
            transitions: vec![
                trans("t_cycle_0", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t_cycle_1", vec![arc(1, 1)], vec![arc(0, 1)]),
                // External: consumes from BOTH cycle places into sink.
                trans("t_ext", vec![arc(0, 2), arc(1, 3)], vec![arc(2, 1)]),
            ],
            initial_marking: vec![5, 0, 0],
        };

        let cycles = find_token_cycles(&net, &[], &[false, false, false]);
        assert_eq!(cycles.len(), 1);

        apply_token_cycles(&mut net, &cycles);

        // External transition's two cycle-place inputs (p0 weight 2, p1
        // weight 3) must collapse to one input on the survivor with
        // weight 5.
        let t_ext = &net.transitions[0];
        assert_eq!(t_ext.inputs.len(), 1);
        assert_eq!(t_ext.inputs[0].place, PlaceIdx(0));
        assert_eq!(t_ext.inputs[0].weight, 5);
    }

    /// No cycles detected → no changes.
    #[test]
    fn test_empty_cycles_is_noop() {
        let mut net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
            initial_marking: vec![1, 0],
        };
        let clone = net.clone();
        let (removed_p, removed_t) = apply_token_cycles(&mut net, &[]);

        assert_eq!(removed_p, 0);
        assert_eq!(removed_t, 0);
        assert_eq!(net.num_places(), clone.num_places());
        assert_eq!(net.num_transitions(), clone.num_transitions());
        assert_eq!(net.initial_marking, clone.initial_marking);
    }

    /// Query-protected cycle: detection skips, so apply is a no-op.
    #[test]
    fn test_protected_cycle_preserves_net() {
        let mut net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![
                trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 0],
        };

        // Mark p0 as query-protected.
        let cycles = find_token_cycles(&net, &[], &[true, false]);
        assert!(cycles.is_empty());

        apply_token_cycles(&mut net, &cycles);
        assert_eq!(net.num_places(), 2);
        assert_eq!(net.num_transitions(), 2);
    }

    /// Two disjoint cycles: both compressed independently.
    #[test]
    fn test_two_disjoint_cycles_compressed_independently() {
        let mut net = PetriNet {
            name: None,
            // Cycle A: p0 <-> p1 via t0, t1
            // Cycle B: p2 <-> p3 via t2, t3
            places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
            transitions: vec![
                trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
                trans("t2", vec![arc(2, 1)], vec![arc(3, 1)]),
                trans("t3", vec![arc(3, 1)], vec![arc(2, 1)]),
            ],
            initial_marking: vec![1, 0, 0, 1],
        };

        let cycles = find_token_cycles(&net, &[], &[false, false, false, false]);
        assert_eq!(cycles.len(), 2);

        let (places_removed, trans_removed) = apply_token_cycles(&mut net, &cycles);
        assert_eq!(places_removed, 2);
        assert_eq!(trans_removed, 4);
        assert_eq!(net.num_places(), 2);
        assert_eq!(net.num_transitions(), 0);
        // Each surviving place holds the cycle's token (1 each).
        let sum: u64 = net.initial_marking.iter().sum();
        assert_eq!(sum, 2);
    }

    /// External transition that has an arc on a cycle place ALREADY pointing
    /// to the survivor, plus a separate arc on a non-survivor: must merge to
    /// one combined arc on the survivor (this stresses BTreeMap weight summing
    /// when the destination place already exists).
    #[test]
    fn test_external_with_existing_survivor_arc_merges() {
        let mut net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1"), place("source")],
            transitions: vec![
                trans("t_cycle_0", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t_cycle_1", vec![arc(1, 1)], vec![arc(0, 1)]),
                // External produces 4 into p0 (survivor) AND 2 into p1.
                trans("t_ext", vec![arc(2, 1)], vec![arc(0, 4), arc(1, 2)]),
            ],
            initial_marking: vec![0, 0, 5],
        };

        let cycles = find_token_cycles(&net, &[], &[false, false, false]);
        assert_eq!(cycles.len(), 1);

        apply_token_cycles(&mut net, &cycles);

        let t_ext = &net.transitions[0];
        // Single output: survivor with weight 4+2 = 6.
        assert_eq!(t_ext.outputs.len(), 1);
        assert_eq!(t_ext.outputs[0].weight, 6);
    }

    /// Sanity: after transform, net.initial_marking length matches
    /// net.num_places() (crucial for downstream evaluators).
    #[test]
    fn test_invariant_marking_length_equals_place_count() {
        let mut net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
            transitions: vec![
                trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
                trans("t2", vec![arc(2, 1)], vec![arc(3, 1)]),
                trans("t3", vec![arc(3, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![2, 0, 0, 0],
        };

        let cycles = find_token_cycles(&net, &[], &[false, false, false, false]);
        apply_token_cycles(&mut net, &cycles);

        assert_eq!(net.initial_marking.len(), net.num_places());
        let surviving_tokens: u64 = net.initial_marking.iter().sum();
        assert_eq!(surviving_tokens, 2);
    }
}
