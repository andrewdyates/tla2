// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Search loop and tracker progression for heuristic best-first search.
//!
//! Contains the parameterized search entrypoint that drives the priority
//! queue expansion, bloom filter deduplication, and tracker checking.

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::rc::Rc;
use std::time::Instant;

use crate::examinations::reachability_witness::{
    apply_validated_witnesses, candidates_for_marking, WitnessSeedSource, WitnessValidationContext,
};
use crate::petri_net::{PetriNet, TransitionIdx};

use super::super::reachability::PropertyTracker;
use super::frontier::{BloomFilter, ScoredNode, TraceNode};
use super::heuristic::{combined_heuristic, compute_heuristic_weights};

/// Parameterized version for testing.
pub(crate) fn run_heuristic_seeding_params(
    net: &PetriNet,
    trackers: &mut [PropertyTracker],
    validation: &WitnessValidationContext<'_>,
    deadline: Option<Instant>,
    max_expansions: u64,
    bloom_capacity: usize,
    max_queue_size: usize,
) {
    if net.num_places() == 0 || all_walkable_resolved(trackers) {
        return;
    }

    // Check initial marking first.
    let candidates = candidates_for_marking(
        trackers,
        &net.initial_marking,
        net,
        WitnessSeedSource::Heuristic,
        &[],
    );
    apply_validated_witnesses(validation, trackers, candidates);
    if all_walkable_resolved(trackers) {
        return;
    }

    // Compute heuristic weights for each unresolved property.
    let weights: Vec<_> = trackers
        .iter()
        .map(|t| {
            if t.verdict.is_some() {
                None
            } else {
                Some(compute_heuristic_weights(net, t))
            }
        })
        .collect();

    // If all weights are trivial (no guidance) AND no transitions, skip.
    // Even with trivial weights, the search explores breadth-first and can
    // still find AG counterexamples that random walk missed.
    if net.num_transitions() == 0 {
        return;
    }

    let mut bloom = BloomFilter::new(bloom_capacity);
    let mut queue: BinaryHeap<Reverse<ScoredNode>> = BinaryHeap::new();

    // Seed with initial marking.
    let h0 = combined_heuristic(&net.initial_marking, trackers, &weights);
    bloom.insert(&net.initial_marking);
    queue.push(Reverse(ScoredNode {
        score: h0,
        marking: net.initial_marking.clone(),
        trace: None,
    }));

    let mut expansions: u64 = 0;
    let mut enabled = Vec::with_capacity(net.num_transitions());
    let mut successor = vec![0u64; net.num_places()];

    while let Some(Reverse(entry)) = queue.pop() {
        // Deadline check every 1024 expansions.
        if expansions & 0x3FF == 0 {
            if let Some(dl) = deadline {
                if Instant::now() >= dl {
                    break;
                }
            }
            if all_walkable_resolved(trackers) {
                break;
            }
        }

        expansions += 1;
        if expansions > max_expansions {
            break;
        }

        let candidates = candidates_for_marking(
            trackers,
            &entry.marking,
            net,
            WitnessSeedSource::Heuristic,
            &reconstruct_trace(entry.trace.as_ref()),
        );
        apply_validated_witnesses(validation, trackers, candidates);
        if all_walkable_resolved(trackers) {
            break;
        }

        // Collect enabled transitions.
        enabled.clear();
        for t in 0..net.num_transitions() {
            let tidx = TransitionIdx(t as u32);
            if net.is_enabled(&entry.marking, tidx) {
                enabled.push(tidx);
            }
        }

        // Expand successors.
        for &tidx in &enabled {
            successor.copy_from_slice(&entry.marking);
            net.apply_delta(&mut successor, tidx);

            if !bloom.probably_contains(&successor) {
                bloom.insert(&successor);
                let h = combined_heuristic(&successor, trackers, &weights);
                queue.push(Reverse(ScoredNode {
                    score: h,
                    marking: successor.clone(),
                    trace: Some(Rc::new(TraceNode {
                        parent: entry.trace.clone(),
                        via: tidx,
                    })),
                }));
            }
        }

        // Memory bound: truncate queue if too large. Keep better (lower score) half.
        // `into_sorted_vec()` sorts by `Reverse<ScoredNode>`, which means
        // the lowest heuristic scores are at the end of the vector. Reverse
        // the iterator so truncation preserves the most promising frontier.
        if queue.len() > max_queue_size {
            let keep = max_queue_size / 2;
            let sorted = queue.into_sorted_vec();
            queue = sorted.into_iter().rev().take(keep).collect();
        }
    }
}

/// Check if all trackers have been resolved.
fn all_walkable_resolved(trackers: &[PropertyTracker]) -> bool {
    trackers.iter().all(|t| t.verdict.is_some())
}

fn reconstruct_trace(tail: Option<&Rc<TraceNode>>) -> Vec<TransitionIdx> {
    let mut trace = Vec::new();
    let mut cursor = tail.cloned();
    while let Some(node) = cursor {
        trace.push(node.via);
        cursor = node.parent.clone();
    }
    trace.reverse();
    trace
}
