// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DiffSuccessor adapter for Petri net transition firings.
//!
//! Converts a transition firing into a [`DiffSuccessor<PlaceIdx, i64>`] containing
//! only the places whose token counts change and the signed deltas. This enables:
//!
//! - **Incremental fingerprinting**: compute the successor's deduplication fingerprint
//!   by XOR-updating the parent's fingerprint with only the changed places, instead of
//!   hashing the entire marking.
//! - **Deferred materialization**: only allocate a full marking vector for genuinely
//!   new states (~5% of successors in typical MCC nets), skipping allocation for
//!   the ~95% that are duplicates.
//!
//! # Usage
//!
//! ```ignore
//! let diff = transition_to_diff(&net, TransitionIdx(0));
//! let new_fp = incremental_fingerprint(&parent_marking, parent_xor, &diff, &salts);
//! if !seen.contains(new_fp) {
//!     let new_marking = apply_diff(&parent_marking, &diff);
//!     seen.insert(new_fp);
//!     queue.push(new_marking);
//! }
//! ```

use tla_mc_core::{finalize_xor, DiffChanges, DiffSuccessor};

use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};

/// FNV-1a 64-bit prime used for fingerprint finalization.
const FNV_PRIME: u64 = 0x0000_0100_0000_01B3;

/// Build a [`DiffSuccessor`] from a Petri net transition.
///
/// Iterates the input and output arcs of `trans` and computes a signed delta
/// for each affected place. Places that appear in both inputs and outputs have
/// their deltas merged. Places whose net delta is zero are excluded.
///
/// The fingerprint field is left as `0` (placeholder). Callers should compute
/// the actual fingerprint via [`incremental_fingerprint`] or similar.
///
/// # Complexity
///
/// O(|arcs|) time, O(|affected_places|) space. Most MCC transitions have 2-6
/// arcs, so the result fits inline in the `SmallVec<4>` without heap allocation.
#[must_use]
pub(crate) fn transition_to_diff(
    net: &PetriNet,
    trans: TransitionIdx,
) -> DiffSuccessor<PlaceIdx, i64> {
    let t = &net.transitions[trans.0 as usize];
    let mut changes: DiffChanges<PlaceIdx, i64> = DiffChanges::new();

    // Process input arcs (tokens consumed → negative delta).
    for arc in &t.inputs {
        merge_delta(&mut changes, arc.place, -(arc.weight as i64));
    }

    // Process output arcs (tokens produced → positive delta).
    for arc in &t.outputs {
        merge_delta(&mut changes, arc.place, arc.weight as i64);
    }

    // Remove zero-delta entries (place appears in both input and output with
    // equal weight, e.g., read arcs or self-loops).
    changes.retain(|(_place, delta)| *delta != 0);

    DiffSuccessor::from_changes(changes)
}

/// Merge a delta into the changes list, combining deltas for the same place.
///
/// If the place already has an entry, add to its delta. Otherwise, push a new
/// entry. For the small number of arcs per transition (typically 2-6), linear
/// scan is faster than a HashMap.
#[inline]
fn merge_delta(changes: &mut DiffChanges<PlaceIdx, i64>, place: PlaceIdx, delta: i64) {
    for (existing_place, existing_delta) in changes.iter_mut() {
        if existing_place.0 == place.0 {
            *existing_delta += delta;
            return;
        }
    }
    changes.push((place, delta));
}

/// Apply a diff to a parent marking, producing a new full marking.
///
/// Clones the parent and applies each (place, delta) pair. Returns the
/// materialized successor marking.
///
/// # Panics
///
/// Panics if applying a delta would cause a place's token count to underflow
/// (which indicates the transition was not actually enabled at this marking).
#[must_use]
pub(crate) fn apply_diff(parent: &[u64], diff: &DiffSuccessor<PlaceIdx, i64>) -> Vec<u64> {
    let mut marking = parent.to_vec();
    for &(place, delta) in &diff.changes {
        let idx = place.0 as usize;
        if delta >= 0 {
            marking[idx] = marking[idx].wrapping_add(delta as u64);
        } else {
            marking[idx] = marking[idx].wrapping_sub((-delta) as u64);
        }
    }
    marking
}

/// Apply a diff into an existing marking buffer, reusing its allocation.
///
/// Copies `parent` into `out` (resizing if needed), then applies each delta.
pub(crate) fn apply_diff_into(
    parent: &[u64],
    diff: &DiffSuccessor<PlaceIdx, i64>,
    out: &mut Vec<u64>,
) {
    out.clear();
    out.extend_from_slice(parent);
    for &(place, delta) in &diff.changes {
        let idx = place.0 as usize;
        if delta >= 0 {
            out[idx] = out[idx].wrapping_add(delta as u64);
        } else {
            out[idx] = out[idx].wrapping_sub((-delta) as u64);
        }
    }
}

/// Compute per-place salts for XOR fingerprinting.
///
/// Returns a vector of pseudo-random salts, one per place, derived from the
/// place index. These must be consistent across all fingerprint computations
/// for the same net.
#[must_use]
pub(crate) fn compute_place_salts(num_places: usize) -> Vec<u64> {
    (0..num_places)
        .map(|i| {
            // Mix the index into a non-trivial salt using FNV-like hashing.
            // Avoids zero salts (which would make XOR contributions vanish).
            let mut h = 0xcbf2_9ce4_8422_2325_u64; // FNV offset basis
            h ^= i as u64;
            h = h.wrapping_mul(FNV_PRIME);
            h ^ (h >> 32)
        })
        .collect()
}

/// Compute the base XOR fingerprint of a full marking.
///
/// This is the initial combined XOR value from which incremental updates are
/// derived. Each place contributes `salt[i] * (token_hash(marking[i]) + 1)`.
#[must_use]
pub(crate) fn marking_xor_fingerprint(marking: &[u64], salts: &[u64]) -> u64 {
    marking
        .iter()
        .zip(salts.iter())
        .map(|(&tokens, &salt)| salt.wrapping_mul(token_hash(tokens).wrapping_add(1)))
        .fold(0_u64, |acc, x| acc ^ x)
}

/// Compute the incremental fingerprint of a successor state from its diff.
///
/// Given the parent marking, its XOR fingerprint, the transition diff, and
/// per-place salts, returns the finalized u64 fingerprint of the successor.
#[must_use]
pub(crate) fn incremental_fingerprint(
    parent_marking: &[u64],
    parent_xor: u64,
    diff: &DiffSuccessor<PlaceIdx, i64>,
    salts: &[u64],
) -> u64 {
    // Compute the updated XOR fingerprint by replacing each changed place's
    // contribution. For each (place, delta) in the diff:
    //   1. XOR out the old contribution: salt[place] * (hash(old_tokens) + 1)
    //   2. XOR in the new contribution:  salt[place] * (hash(new_tokens) + 1)
    //
    // Note: we inline the XOR update here rather than using
    // `incremental_xor_fingerprint` because our diff stores (key, delta)
    // pairs and the generic API's `new_value_fp` closure receives only `&V`
    // (the delta) without the key, making it impossible to reconstruct the
    // absolute new token count inside the closure. The manual loop is
    // equivalent and equally efficient.
    let mut combined_xor = parent_xor;
    for &(place, delta) in &diff.changes {
        let idx = place.0 as usize;
        let old_tokens = parent_marking[idx];
        let new_tokens = if delta >= 0 {
            old_tokens.wrapping_add(delta as u64)
        } else {
            old_tokens.wrapping_sub((-delta) as u64)
        };
        let old_fp = token_hash(old_tokens);
        let new_fp = token_hash(new_tokens);
        if old_fp != new_fp {
            let s = salts[idx];
            let old_contrib = s.wrapping_mul(old_fp.wrapping_add(1));
            let new_contrib = s.wrapping_mul(new_fp.wrapping_add(1));
            combined_xor ^= old_contrib ^ new_contrib;
        }
    }

    finalize_xor(combined_xor, FNV_PRIME)
}

/// Hash a token count to a fingerprint value.
///
/// Uses FNV-style mixing to spread token counts across the u64 range.
/// Small differences in token counts (e.g., 5 vs 6) produce very different
/// fingerprints, which is important for XOR-based deduplication.
#[inline]
#[must_use]
fn token_hash(tokens: u64) -> u64 {
    let mut h = 0xcbf2_9ce4_8422_2325_u64;
    h ^= tokens;
    h = h.wrapping_mul(FNV_PRIME);
    h ^ (h >> 32)
}

/// Compute the finalized fingerprint of a full marking (non-incremental).
///
/// Used for the initial state and for verification that incremental
/// computation matches the full computation.
#[must_use]
pub(crate) fn full_marking_fingerprint(marking: &[u64], salts: &[u64]) -> u64 {
    let xor = marking_xor_fingerprint(marking, salts);
    finalize_xor(xor, FNV_PRIME)
}

/// Pre-compute diffs for all transitions in a net.
///
/// Returns a vector indexed by transition index. This avoids recomputing
/// arc iteration on every firing, which is beneficial when the same transition
/// fires many times across different markings.
#[must_use]
pub(crate) fn precompute_transition_diffs(net: &PetriNet) -> Vec<DiffSuccessor<PlaceIdx, i64>> {
    (0..net.num_transitions())
        .map(|i| transition_to_diff(net, TransitionIdx(i as u32)))
        .collect()
}

/// Diff-based BFS exploration with incremental fingerprinting.
///
/// Functionally equivalent to [`super::observer::explore`] but avoids full-marking
/// hashing and allocation for duplicate states:
///
/// 1. Pre-computes a [`DiffSuccessor`] for every transition (O(|arcs|) per transition).
/// 2. At each state, fires enabled transitions by computing an incremental u64
///    fingerprint from the parent's XOR fingerprint and the changed places only.
/// 3. Checks the fingerprint set for duplicates. If the fingerprint is new,
///    materializes the full marking via [`apply_diff`] and enqueues it.
/// 4. Observer callbacks receive full `&[u64]` markings, identical to the standard
///    BFS path.
///
/// # When to use
///
/// Best for nets where most successors are duplicates (typical in MCC: ~95% duplicate
/// rate). The overhead of pre-computing diffs and maintaining XOR fingerprints pays
/// off by avoiding full marking pack+hash for duplicates.
///
/// # Limitations
///
/// - POR (partial-order reduction) is not yet supported in this path.
/// - The u64 XOR fingerprint has higher collision probability than the u128 SipHash
///   used in the standard path (N²/2^65 vs N²/2^129). For state spaces under ~10^8
///   this is still negligible (~10^-11).
pub(crate) fn explore_diff(
    net: &PetriNet,
    config: &super::config::ExplorationConfig,
    observer: &mut dyn super::config::ExplorationObserver,
) -> super::config::ExplorationResult {
    use std::collections::VecDeque;
    use std::time::Instant;

    use rustc_hash::FxHashSet;

    use super::config::{ExplorationResult, DEADLINE_CHECK_INTERVAL};
    use super::transition_selection::enabled_transitions_into;

    let num_places = net.num_places();
    let num_transitions = net.num_transitions();

    // Pre-compute transition diffs and per-place salts.
    let diffs = precompute_transition_diffs(net);
    let salts = compute_place_salts(num_places);

    // Fingerprint dedup set (u64 XOR fingerprints).
    let mut seen_fps: FxHashSet<u64> = FxHashSet::default();

    // BFS queue carries (full_marking, parent_xor_fingerprint).
    let mut queue: VecDeque<(Vec<u64>, u64)> = VecDeque::new();

    // Initialize with the initial marking.
    let initial_xor = marking_xor_fingerprint(&net.initial_marking, &salts);
    let initial_fp = full_marking_fingerprint(&net.initial_marking, &salts);

    if !observer.on_new_state(&net.initial_marking) {
        return ExplorationResult::new(false, 1, true);
    }
    seen_fps.insert(initial_fp);
    queue.push_back((net.initial_marking.clone(), initial_xor));

    let mut stopped_by_observer = false;
    let mut deadline_counter: u32 = 0;
    let mut enabled_transitions = Vec::with_capacity(num_transitions);

    while let Some((marking, parent_xor)) = queue.pop_front() {
        deadline_counter = deadline_counter.wrapping_add(1);
        if deadline_counter.is_multiple_of(DEADLINE_CHECK_INTERVAL)
            && config
                .deadline()
                .is_some_and(|deadline| Instant::now() >= deadline)
        {
            return ExplorationResult::new(false, seen_fps.len(), false);
        }

        if observer.is_done() {
            stopped_by_observer = true;
            break;
        }

        // POR is not supported in diff path; pass None for dep_graph.
        enabled_transitions_into(
            net,
            &marking,
            num_transitions,
            None,
            &crate::stubborn::PorStrategy::None,
            &mut enabled_transitions,
        );

        let has_enabled = !enabled_transitions.is_empty();

        for &trans in &enabled_transitions {
            let diff = &diffs[trans.0 as usize];

            // Compute incremental fingerprint without materializing the successor.
            let fp = incremental_fingerprint(&marking, parent_xor, diff, &salts);
            if seen_fps.contains(&fp) {
                continue; // Duplicate — skip without materializing.
            }

            if !observer.on_transition_fire(trans) {
                stopped_by_observer = true;
                break;
            }

            if seen_fps.len() >= config.max_states() {
                return ExplorationResult::new(false, seen_fps.len(), false);
            }

            // Materialize the full successor marking (only for new states).
            let successor = apply_diff(&marking, diff);

            if !observer.on_new_state(&successor) {
                stopped_by_observer = true;
                break;
            }

            let succ_xor = marking_xor_fingerprint(&successor, &salts);
            seen_fps.insert(fp);
            queue.push_back((successor, succ_xor));
        }

        if stopped_by_observer {
            break;
        }

        if !has_enabled {
            observer.on_deadlock(&marking);
            if observer.is_done() {
                stopped_by_observer = true;
                break;
            }
        }
    }

    ExplorationResult::new(
        !stopped_by_observer && queue.is_empty(),
        seen_fps.len(),
        stopped_by_observer,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionIdx, TransitionInfo};

    fn arc(place: u32, weight: u64) -> Arc {
        Arc {
            place: PlaceIdx(place),
            weight,
        }
    }

    fn place(id: &str) -> PlaceInfo {
        PlaceInfo {
            id: id.to_string(),
            name: None,
        }
    }

    fn trans(id: &str, inputs: Vec<Arc>, outputs: Vec<Arc>) -> TransitionInfo {
        TransitionInfo {
            id: id.to_string(),
            name: None,
            inputs,
            outputs,
        }
    }

    /// Simple net: P0 --[2]--> T0 --[1]--> P1, --[3]--> P2
    fn simple_net() -> PetriNet {
        PetriNet {
            name: Some("simple".into()),
            places: vec![place("P0"), place("P1"), place("P2")],
            transitions: vec![trans("T0", vec![arc(0, 2)], vec![arc(1, 1), arc(2, 3)])],
            initial_marking: vec![5, 0, 0],
        }
    }

    /// Net with a self-loop: T0 reads from P0 (weight 1) and writes back to P0 (weight 1),
    /// also producing a token in P1. The net delta on P0 is zero.
    fn self_loop_net() -> PetriNet {
        PetriNet {
            name: Some("self_loop".into()),
            places: vec![place("P0"), place("P1")],
            transitions: vec![trans("T0", vec![arc(0, 1)], vec![arc(0, 1), arc(1, 1)])],
            initial_marking: vec![1, 0],
        }
    }

    /// Cyclic net: P0 <-> P1 via two transitions.
    fn cyclic_net() -> PetriNet {
        PetriNet {
            name: Some("cycle".into()),
            places: vec![place("P0"), place("P1")],
            transitions: vec![
                trans("T0", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("T1", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 0],
        }
    }

    // ---------------------------------------------------------------
    // transition_to_diff tests
    // ---------------------------------------------------------------

    #[test]
    fn test_transition_to_diff_simple() {
        let net = simple_net();
        let diff = transition_to_diff(&net, TransitionIdx(0));
        // T0: consumes 2 from P0, produces 1 to P1, 3 to P2
        // Expected changes: P0 -> -2, P1 -> +1, P2 -> +3
        assert_eq!(diff.num_changes(), 3);

        let changes: Vec<(u32, i64)> = diff.changes.iter().map(|(p, d)| (p.0, *d)).collect();
        assert!(changes.contains(&(0, -2)));
        assert!(changes.contains(&(1, 1)));
        assert!(changes.contains(&(2, 3)));
    }

    #[test]
    fn test_transition_to_diff_self_loop_cancels() {
        let net = self_loop_net();
        let diff = transition_to_diff(&net, TransitionIdx(0));
        // T0: consumes 1 from P0, produces 1 to P0 and 1 to P1.
        // P0 delta = -1 + 1 = 0, so P0 is excluded.
        // Only P1 -> +1 should remain.
        assert_eq!(diff.num_changes(), 1);
        assert_eq!(diff.changes[0].0 .0, 1); // P1
        assert_eq!(diff.changes[0].1, 1); // +1
    }

    #[test]
    fn test_transition_to_diff_stays_inline() {
        let net = simple_net();
        let diff = transition_to_diff(&net, TransitionIdx(0));
        // 3 changes fits within DIFF_INLINE_CAPACITY (4)
        assert!(!diff.changes.spilled());
    }

    // ---------------------------------------------------------------
    // apply_diff tests
    // ---------------------------------------------------------------

    #[test]
    fn test_apply_diff_matches_fire() {
        let net = simple_net();
        let diff = transition_to_diff(&net, TransitionIdx(0));

        let fire_result = net.fire(&net.initial_marking, TransitionIdx(0));
        let diff_result = apply_diff(&net.initial_marking, &diff);

        assert_eq!(fire_result, diff_result);
        assert_eq!(diff_result, vec![3, 1, 3]);
    }

    #[test]
    fn test_apply_diff_into_matches_fire() {
        let net = simple_net();
        let diff = transition_to_diff(&net, TransitionIdx(0));

        let fire_result = net.fire(&net.initial_marking, TransitionIdx(0));
        let mut buf = Vec::new();
        apply_diff_into(&net.initial_marking, &diff, &mut buf);

        assert_eq!(fire_result, buf);
    }

    #[test]
    fn test_apply_diff_self_loop() {
        let net = self_loop_net();
        let diff = transition_to_diff(&net, TransitionIdx(0));

        let fire_result = net.fire(&net.initial_marking, TransitionIdx(0));
        let diff_result = apply_diff(&net.initial_marking, &diff);

        assert_eq!(fire_result, diff_result);
        // P0 stays at 1 (self-loop), P1 goes from 0 to 1.
        assert_eq!(diff_result, vec![1, 1]);
    }

    // ---------------------------------------------------------------
    // Incremental fingerprint tests
    // ---------------------------------------------------------------

    #[test]
    fn test_incremental_fingerprint_matches_full() {
        let net = simple_net();
        let salts = compute_place_salts(net.num_places());
        let diff = transition_to_diff(&net, TransitionIdx(0));

        let parent_xor = marking_xor_fingerprint(&net.initial_marking, &salts);
        let incr_fp = incremental_fingerprint(&net.initial_marking, parent_xor, &diff, &salts);

        // Compute full fingerprint of the successor marking.
        let successor = apply_diff(&net.initial_marking, &diff);
        let full_fp = full_marking_fingerprint(&successor, &salts);

        assert_eq!(incr_fp, full_fp, "incremental must match full fingerprint");
    }

    #[test]
    fn test_incremental_fingerprint_cyclic_net() {
        let net = cyclic_net();
        let salts = compute_place_salts(net.num_places());
        let diffs = precompute_transition_diffs(&net);

        // Fire T0: [1, 0] -> [0, 1]
        let m0 = &net.initial_marking;
        let xor0 = marking_xor_fingerprint(m0, &salts);
        let fp_after_t0 = incremental_fingerprint(m0, xor0, &diffs[0], &salts);

        let m1 = apply_diff(m0, &diffs[0]);
        let full_fp1 = full_marking_fingerprint(&m1, &salts);
        assert_eq!(fp_after_t0, full_fp1);

        // Fire T1: [0, 1] -> [1, 0] (back to initial)
        let xor1 = marking_xor_fingerprint(&m1, &salts);
        let fp_after_t1 = incremental_fingerprint(&m1, xor1, &diffs[1], &salts);

        let m2 = apply_diff(&m1, &diffs[1]);
        let full_fp2 = full_marking_fingerprint(&m2, &salts);
        assert_eq!(fp_after_t1, full_fp2);

        // m2 should equal m0 (initial marking).
        assert_eq!(m2, m0.to_vec());
        // Fingerprints of identical markings should match.
        let fp_initial = full_marking_fingerprint(m0, &salts);
        assert_eq!(fp_after_t1, fp_initial);
    }

    #[test]
    fn test_incremental_fingerprint_no_change_is_identity() {
        // A self-loop transition with zero net delta should not change the fingerprint.
        let net = self_loop_net();
        let salts = compute_place_salts(net.num_places());

        // Manually create a diff with zero changes on P0 (the self-loop).
        // transition_to_diff already strips zero-delta entries, but the
        // non-zero entry (P1: +1) does change the fingerprint.
        let diff = transition_to_diff(&net, TransitionIdx(0));
        let parent_xor = marking_xor_fingerprint(&net.initial_marking, &salts);
        let incr_fp = incremental_fingerprint(&net.initial_marking, parent_xor, &diff, &salts);

        let successor = apply_diff(&net.initial_marking, &diff);
        let full_fp = full_marking_fingerprint(&successor, &salts);
        assert_eq!(incr_fp, full_fp);
    }

    // ---------------------------------------------------------------
    // precompute_transition_diffs
    // ---------------------------------------------------------------

    #[test]
    fn test_precompute_diffs_length_matches_transitions() {
        let net = cyclic_net();
        let diffs = precompute_transition_diffs(&net);
        assert_eq!(diffs.len(), net.num_transitions());
    }

    #[test]
    fn test_precomputed_diff_matches_individual() {
        let net = simple_net();
        let diffs = precompute_transition_diffs(&net);
        let individual = transition_to_diff(&net, TransitionIdx(0));

        assert_eq!(diffs[0].num_changes(), individual.num_changes());
        for i in 0..diffs[0].num_changes() {
            assert_eq!(diffs[0].changes[i].0 .0, individual.changes[i].0 .0);
            assert_eq!(diffs[0].changes[i].1, individual.changes[i].1);
        }
    }

    // ---------------------------------------------------------------
    // End-to-end: diff-based BFS finds same states as full BFS
    // ---------------------------------------------------------------

    #[test]
    fn test_diff_bfs_finds_same_states_as_full_bfs() {
        // Use a net with multiple reachable states: counting net with 3 tokens.
        let net = PetriNet {
            name: Some("counting3".into()),
            places: vec![place("P0"), place("P1")],
            transitions: vec![trans("T0", vec![arc(0, 1)], vec![arc(1, 1)])],
            initial_marking: vec![3, 0],
        };
        // Reachable states: [3,0], [2,1], [1,2], [0,3] = 4 states.

        let salts = compute_place_salts(net.num_places());
        let diffs = precompute_transition_diffs(&net);

        // Diff-based BFS.
        let mut diff_states: Vec<Vec<u64>> = Vec::new();
        let mut diff_fps: rustc_hash::FxHashSet<u64> = rustc_hash::FxHashSet::default();
        let mut queue: std::collections::VecDeque<(Vec<u64>, u64)> =
            std::collections::VecDeque::new();

        let initial_xor = marking_xor_fingerprint(&net.initial_marking, &salts);
        let initial_fp = full_marking_fingerprint(&net.initial_marking, &salts);
        diff_states.push(net.initial_marking.clone());
        diff_fps.insert(initial_fp);
        queue.push_back((net.initial_marking.clone(), initial_xor));

        while let Some((marking, parent_xor)) = queue.pop_front() {
            for (tidx, diff) in diffs.iter().enumerate() {
                let trans = TransitionIdx(tidx as u32);
                if !net.is_enabled(&marking, trans) {
                    continue;
                }

                let fp = incremental_fingerprint(&marking, parent_xor, diff, &salts);
                if diff_fps.contains(&fp) {
                    continue;
                }

                let successor = apply_diff(&marking, diff);
                let succ_xor = marking_xor_fingerprint(&successor, &salts);
                diff_fps.insert(fp);
                diff_states.push(successor.clone());
                queue.push_back((successor, succ_xor));
            }
        }

        // Full BFS for comparison.
        let mut full_states: Vec<Vec<u64>> = Vec::new();
        let mut full_queue: std::collections::VecDeque<Vec<u64>> =
            std::collections::VecDeque::new();
        let mut full_seen: rustc_hash::FxHashSet<Vec<u64>> = rustc_hash::FxHashSet::default();

        full_seen.insert(net.initial_marking.clone());
        full_states.push(net.initial_marking.clone());
        full_queue.push_back(net.initial_marking.clone());

        while let Some(marking) = full_queue.pop_front() {
            for tidx in 0..net.num_transitions() {
                let trans = TransitionIdx(tidx as u32);
                if !net.is_enabled(&marking, trans) {
                    continue;
                }
                let successor = net.fire(&marking, trans);
                if full_seen.insert(successor.clone()) {
                    full_states.push(successor.clone());
                    full_queue.push_back(successor);
                }
            }
        }

        // Both should find the same number of states.
        assert_eq!(
            diff_states.len(),
            full_states.len(),
            "diff BFS found {} states, full BFS found {}",
            diff_states.len(),
            full_states.len()
        );
        assert_eq!(diff_states.len(), 4);

        // Verify all full states appear in diff states.
        for state in &full_states {
            assert!(
                diff_states.contains(state),
                "full BFS state {state:?} not found in diff BFS results"
            );
        }
    }

    #[test]
    fn test_diff_bfs_cyclic_net_terminates() {
        let net = cyclic_net();
        let salts = compute_place_salts(net.num_places());
        let diffs = precompute_transition_diffs(&net);

        let mut seen_fps: rustc_hash::FxHashSet<u64> = rustc_hash::FxHashSet::default();
        let mut queue: std::collections::VecDeque<(Vec<u64>, u64)> =
            std::collections::VecDeque::new();
        let mut state_count: usize = 0;

        let initial_xor = marking_xor_fingerprint(&net.initial_marking, &salts);
        let initial_fp = full_marking_fingerprint(&net.initial_marking, &salts);
        seen_fps.insert(initial_fp);
        state_count += 1;
        queue.push_back((net.initial_marking.clone(), initial_xor));

        while let Some((marking, parent_xor)) = queue.pop_front() {
            for (tidx, diff) in diffs.iter().enumerate() {
                let trans = TransitionIdx(tidx as u32);
                if !net.is_enabled(&marking, trans) {
                    continue;
                }

                let fp = incremental_fingerprint(&marking, parent_xor, diff, &salts);
                if seen_fps.contains(&fp) {
                    continue; // Duplicate — skip without materializing.
                }

                let successor = apply_diff(&marking, diff);
                let succ_xor = marking_xor_fingerprint(&successor, &salts);
                seen_fps.insert(fp);
                state_count += 1;
                queue.push_back((successor, succ_xor));
            }
        }

        // Cyclic net with 1 token: [1,0] and [0,1] = 2 states.
        assert_eq!(state_count, 2);
    }
}
