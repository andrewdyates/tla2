// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::VecDeque;

use super::config::ExplorationConfig;
use super::fingerprint::fingerprint_marking;
use super::seen::{InsertOutcome, LocalSeenSet};
use super::setup::ExplorationSetup;
use super::transition_selection::enabled_transitions_into;
use crate::marking::{pack_marking_config, unpack_marking_config};
use crate::petri_net::PetriNet;
use crate::stubborn::{DependencyGraph, PorStrategy};

pub(crate) const PARALLEL_THRESHOLD: usize = 20_000;
pub(crate) const MEDIUM_SPEC_THRESHOLD: usize = 200_000;
pub(crate) const LARGE_SPEC_THRESHOLD: usize = 1_000_000;
pub(crate) const PILOT_SAMPLE_SIZE: usize = 50;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Strategy {
    Sequential,
    Parallel(usize),
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct PilotAnalysis {
    pub(crate) sampled_states: usize,
    pub(crate) avg_branching_factor: f64,
    pub(crate) estimated_states: usize,
    pub(crate) strategy: Strategy,
}

#[must_use]
pub(crate) fn estimate_state_space(sampled_states: usize, avg_branching_factor: f64) -> usize {
    if avg_branching_factor < 0.5 {
        return sampled_states.saturating_mul(10);
    }

    if avg_branching_factor < 1.5 {
        return sampled_states.saturating_mul(50_000);
    }

    let depth_estimate = 8.0;
    let growth = avg_branching_factor.powf(depth_estimate);
    let estimate = sampled_states as f64 * growth;
    estimate.min(1e9) as usize
}

#[must_use]
pub(crate) fn select_strategy(estimated_states: usize, worker_cap: usize) -> Strategy {
    if worker_cap <= 1 || estimated_states < PARALLEL_THRESHOLD {
        Strategy::Sequential
    } else if estimated_states < MEDIUM_SPEC_THRESHOLD {
        Strategy::Parallel(2.min(worker_cap))
    } else if estimated_states < LARGE_SPEC_THRESHOLD {
        Strategy::Parallel(4.min(worker_cap))
    } else {
        Strategy::Parallel(worker_cap)
    }
}

#[must_use]
pub(crate) fn analyze_observer_parallelism(
    net: &PetriNet,
    config: &ExplorationConfig,
) -> PilotAnalysis {
    let ExplorationSetup {
        marking_config,
        pack_capacity,
        num_places,
        num_transitions,
        initial_packed,
    } = ExplorationSetup::analyze(net);

    let dep_graph = match &config.por_strategy {
        PorStrategy::None => None,
        _ => Some(DependencyGraph::build(net)),
    };

    let mut visited = LocalSeenSet::new();
    let mut queue: VecDeque<Box<[u8]>> = VecDeque::new();
    visited.insert_checked(fingerprint_marking(&initial_packed));
    queue.push_back(initial_packed);

    let pilot_limit = PILOT_SAMPLE_SIZE.min(config.max_states());
    let mut sampled_states = 0usize;
    let mut total_successors = 0usize;
    let mut current_tokens = Vec::with_capacity(num_places);
    let mut pack_buf = Vec::with_capacity(pack_capacity);
    let mut enabled_transitions = Vec::with_capacity(num_transitions);

    while sampled_states < pilot_limit {
        let Some(current_packed) = queue.pop_front() else {
            break;
        };

        sampled_states += 1;
        unpack_marking_config(&current_packed, &marking_config, &mut current_tokens);

        enabled_transitions_into(
            net,
            &current_tokens,
            num_transitions,
            dep_graph.as_ref(),
            &config.por_strategy,
            &mut enabled_transitions,
        );
        total_successors += enabled_transitions.len();

        for &trans in &enabled_transitions {
            net.apply_delta(&mut current_tokens, trans);
            pack_marking_config(&current_tokens, &marking_config, &mut pack_buf);
            let fp = fingerprint_marking(&pack_buf);
            if visited.insert_checked(fp) == InsertOutcome::Inserted {
                queue.push_back(pack_buf.as_slice().into());
            }
            net.undo_delta(&mut current_tokens, trans);
        }
    }

    let avg_branching_factor = if sampled_states == 0 {
        0.0
    } else {
        total_successors as f64 / sampled_states as f64
    };
    let estimated_states = if queue.is_empty() {
        sampled_states
    } else {
        estimate_state_space(sampled_states, avg_branching_factor)
    };

    PilotAnalysis {
        sampled_states,
        avg_branching_factor,
        estimated_states,
        strategy: select_strategy(estimated_states.min(config.max_states()), config.workers()),
    }
}
