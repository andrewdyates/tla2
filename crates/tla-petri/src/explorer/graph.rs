// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::VecDeque;
use std::time::Instant;

use crate::marking::{pack_marking_config, unpack_marking_config};
use crate::petri_net::{PetriNet, TransitionIdx};

use super::config::{ExplorationConfig, DEADLINE_CHECK_INTERVAL};
use super::setup::ExplorationSetup;
use super::state_registry::{GraphStateRegistry, StateAdmission};

/// Reachability graph with compact integer state IDs.
///
/// Edges store `(successor_id, transition_index)` where the transition index
/// is a raw `u32` for compact storage (use `TransitionIdx(val)` to wrap).
pub(crate) struct ReachabilityGraph {
    /// Forward adjacency: `adj[state_id]` = list of `(successor_id, transition_fired)`.
    pub(crate) adj: Vec<Vec<(u32, u32)>>,
    /// Total number of reachable states discovered.
    pub(crate) num_states: u32,
    /// Whether BFS explored the full reachable state space.
    pub(crate) completed: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum GraphBuildMode {
    StructureOnly,
    WithMarkings,
}

impl GraphBuildMode {
    fn captures_markings(self) -> bool {
        matches!(self, Self::WithMarkings)
    }
}

struct GraphBuildArtifacts {
    graph: ReachabilityGraph,
    markings: Option<Vec<Vec<u64>>>,
}

fn build_graph_core(
    net: &PetriNet,
    config: &ExplorationConfig,
    mode: GraphBuildMode,
) -> GraphBuildArtifacts {
    let ExplorationSetup {
        marking_config,
        pack_capacity,
        num_places,
        num_transitions,
        initial_packed,
    } = ExplorationSetup::analyze(net);

    let mut registry = GraphStateRegistry::with_initial(&initial_packed, config.max_states());
    let mut adj: Vec<Vec<(u32, u32)>> = Vec::new();
    let mut markings = mode
        .captures_markings()
        .then(|| vec![net.initial_marking.clone()]);
    let mut queue: VecDeque<(u32, Box<[u8]>)> = VecDeque::new();

    adj.push(Vec::new());
    queue.push_back((0, initial_packed));

    let mut completed = true;
    let mut current_tokens = Vec::with_capacity(num_places);
    let mut deadline_counter: u32 = 0;
    let mut pack_buf = Vec::with_capacity(pack_capacity);

    'explore: while let Some((sid, current_packed)) = queue.pop_front() {
        deadline_counter = deadline_counter.wrapping_add(1);
        if deadline_counter.is_multiple_of(DEADLINE_CHECK_INTERVAL)
            && config
                .deadline()
                .is_some_and(|deadline| Instant::now() >= deadline)
        {
            completed = false;
            break;
        }

        unpack_marking_config(&current_packed, &marking_config, &mut current_tokens);

        let mut edges = Vec::new();
        for tidx in 0..num_transitions {
            let trans = TransitionIdx(tidx as u32);
            if !net.is_enabled(&current_tokens, trans) {
                continue;
            }
            // Delta-based firing: O(arcs) instead of O(places) copy
            net.apply_delta(&mut current_tokens, trans);
            pack_marking_config(&current_tokens, &marking_config, &mut pack_buf);
            let next_id = match registry.admit_packed(&pack_buf) {
                StateAdmission::Existing(existing) => existing,
                StateAdmission::Inserted(new_state) => {
                    adj.push(Vec::new());
                    if let Some(markings) = markings.as_mut() {
                        markings.push(current_tokens.to_vec());
                    }
                    queue.push_back((new_state.state_id, new_state.packed));
                    new_state.state_id
                }
                StateAdmission::LimitReached => {
                    completed = false;
                    net.undo_delta(&mut current_tokens, trans);
                    adj[sid as usize] = edges;
                    break 'explore;
                }
            };
            edges.push((next_id, tidx as u32));
            net.undo_delta(&mut current_tokens, trans);
        }
        adj[sid as usize] = edges;
    }

    GraphBuildArtifacts {
        graph: ReachabilityGraph {
            num_states: registry.len(),
            adj,
            completed,
        },
        markings,
    }
}

/// Build the full reachability graph via BFS.
///
/// Unlike [`super::explore`] which uses an observer pattern for early termination,
/// this function records all edges for structural analysis (SCC, liveness).
/// Uses compact marking storage and delta-based firing.
pub(crate) fn explore_and_build_graph(
    net: &PetriNet,
    config: &ExplorationConfig,
) -> ReachabilityGraph {
    build_graph_core(net, config, GraphBuildMode::StructureOnly).graph
}

/// Full reachability graph with stored markings for model checking.
///
/// Used by CTL and LTL examinations which need to evaluate state predicates
/// at each state during fixpoint/product computations.
pub(crate) struct FullReachabilityGraph {
    /// Adjacency structure and completion flag.
    pub(crate) graph: ReachabilityGraph,
    /// Marking (token vector) for each state, indexed by state ID.
    pub(crate) markings: Vec<Vec<u64>>,
}

/// Build the full reachability graph with markings via BFS.
///
/// Like [`explore_and_build_graph`] but also stores the marking for each state,
/// enabling CTL/LTL model checking which needs to evaluate predicates at every
/// state. Uses compact storage for dedup, delta-based firing, and preserves
/// full u64 markings for predicate evaluation.
pub(crate) fn explore_full(net: &PetriNet, config: &ExplorationConfig) -> FullReachabilityGraph {
    let GraphBuildArtifacts { graph, markings } =
        build_graph_core(net, config, GraphBuildMode::WithMarkings);
    FullReachabilityGraph {
        graph,
        markings: markings.expect("invariant: full graph mode captures markings"),
    }
}
