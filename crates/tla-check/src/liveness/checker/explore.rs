// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BFS exploration of the behavior graph (product of state graph × tableau).
//!
//! Contains the core BFS loop and state/successor management for building the
//! behavior graph used in liveness checking. The behavior graph is the
//! cross-product of state graph transitions and tableau automaton transitions.
//!
//! # Methods
//!
//! - `add_initial_state` — Seed the graph with initial (state, tableau) pairs
//! - `add_successors` — Expand a node's state × tableau cross-product
//! - `explore_bfs` — Full BFS with tableau consistency checking
//! - `explore_state_graph_direct` — Fast path for `tf == Bool(true)` (pure WF/SF)

use super::{BehaviorGraphNode, LivenessChecker, TirProgram};
use crate::error::{EvalError, EvalResult};
use crate::state::{Fingerprint, State};

use std::sync::Arc;
use std::time::Instant;

#[allow(dead_code)]
impl LivenessChecker {
    /// Clone a state from the behavior graph for BFS processing.
    ///
    /// Returns an error if the node is missing — this indicates a graph
    /// construction bug since BFS only enqueues nodes that were successfully
    /// added.
    pub(super) fn clone_state_for_bfs(&self, node: BehaviorGraphNode) -> EvalResult<State> {
        self.graph.get_state(&node).cloned().ok_or_else(|| {
            Self::behavior_graph_invariant_error(format!(
                "BFS queue contains node {node} that is missing from graph"
            ))
        })
    }

    /// Add an initial state to the behavior graph
    ///
    /// This checks consistency with each initial tableau node and adds
    /// (state, tableau_node) pairs for consistent combinations.
    ///
    /// # Returns
    ///
    /// Vector of newly added behavior graph nodes
    pub fn add_initial_state<F>(
        &mut self,
        state: &State,
        get_successors: &mut F,
        tir: Option<&TirProgram<'_>>,
    ) -> EvalResult<Vec<BehaviorGraphNode>>
    where
        F: FnMut(&State) -> EvalResult<Vec<State>>,
    {
        let mut added = Vec::new();

        // For each initial tableau node (indices 0..init_count), check consistency
        for tableau_idx in 0..self.tableau.init_count() {
            let consistent =
                self.check_consistency_cached(state, tableau_idx, get_successors, tir)?;
            if consistent && self.graph.try_add_init_node(state, tableau_idx)? {
                let bg_node = BehaviorGraphNode::from_state(state, tableau_idx);
                added.push(bg_node);
                self.stats.graph_nodes += 1;
            }
        }

        self.stats.states_explored += 1;
        Ok(added)
    }

    fn add_initial_state_with_fp<F>(
        &mut self,
        state: &State,
        state_fp: Fingerprint,
        get_successors: &mut F,
        tir: Option<&TirProgram<'_>>,
    ) -> EvalResult<Vec<BehaviorGraphNode>>
    where
        F: FnMut(&State) -> EvalResult<Vec<State>>,
    {
        let mut added = Vec::new();

        for tableau_idx in 0..self.tableau.init_count() {
            let consistent = self.check_consistency_cached_with_fp(
                state,
                state_fp,
                tableau_idx,
                get_successors,
                tir,
            )?;
            if consistent
                && self
                    .graph
                    .try_add_init_node_with_fp(state, state_fp, tableau_idx)?
            {
                let bg_node = BehaviorGraphNode::new(state_fp, tableau_idx);
                added.push(bg_node);
                self.stats.graph_nodes += 1;
            }
        }

        self.stats.states_explored += 1;
        Ok(added)
    }

    /// Add successor states from a behavior graph node
    ///
    /// This computes the cross-product of:
    /// - State successors (from the Next relation)
    /// - Tableau successors (from the tableau automaton)
    ///
    /// Only consistent combinations are added to the behavior graph.
    ///
    /// # Arguments
    ///
    /// * `from` - The source behavior graph node
    /// * `successors` - State successors from the Next relation
    ///
    /// # Returns
    ///
    /// Vector of newly added behavior graph nodes
    pub fn add_successors<F>(
        &mut self,
        from: BehaviorGraphNode,
        successors: &[State],
        get_successors: &mut F,
        tir: Option<&TirProgram<'_>>,
    ) -> EvalResult<Vec<BehaviorGraphNode>>
    where
        F: FnMut(&State) -> EvalResult<Vec<State>>,
    {
        let mut added = Vec::new();

        // Cache state-graph successors for ENABLED evaluation.
        self.state_successors
            .entry(from.state_fp)
            .or_insert_with(|| Arc::new(successors.to_vec()));

        let tableau_node = match self.tableau.node(from.tableau_idx) {
            Some(node) => node,
            None => {
                return Err(EvalError::Internal {
                    message: format!(
                        "missing tableau node in add_successors: \
                         tableau_idx={} for state_fp={}",
                        from.tableau_idx, from.state_fp
                    ),
                    span: None,
                });
            }
        };

        // Get successor indices before iterating
        let tableau_succ_indices: Vec<_> = tableau_node.successors().iter().copied().collect();

        // For each state successor
        for succ_state in successors {
            // NOTE: TLC KEEPS self-loops (stuttering edges) in the behavior graph.
            // TLC only treats single-node SCCs as trivial if they have NO self-loop.
            // See LiveWorker.java:539-544 (checkComponent) and 769-785 (isStuttering).
            // We must keep stuttering edges so the SCC algorithm can detect them.

            // For each tableau successor
            for &tableau_succ_idx in &tableau_succ_indices {
                // Check if successor state is consistent with successor tableau node (cached)
                let consistent = self.check_consistency_cached(
                    succ_state,
                    tableau_succ_idx,
                    get_successors,
                    tir,
                )?;
                if consistent {
                    if self
                        .graph
                        .add_successor(from, succ_state, tableau_succ_idx)?
                    {
                        let bg_node = BehaviorGraphNode::from_state(succ_state, tableau_succ_idx);
                        added.push(bg_node);
                        self.stats.graph_nodes += 1;
                    }
                    self.stats.graph_edges += 1;
                }
            }
        }

        self.stats.states_explored += successors.len();
        Ok(added)
    }

    fn add_successors_with_state_fp<F, G>(
        &mut self,
        from: BehaviorGraphNode,
        successors: &[State],
        get_successors: &mut F,
        tir: Option<&TirProgram<'_>>,
        state_fp_of: &mut G,
    ) -> EvalResult<Vec<BehaviorGraphNode>>
    where
        F: FnMut(&State) -> EvalResult<Vec<State>>,
        G: FnMut(&State) -> EvalResult<Fingerprint>,
    {
        let mut added = Vec::new();

        self.state_successors
            .entry(from.state_fp)
            .or_insert_with(|| Arc::new(successors.to_vec()));

        let tableau_node = match self.tableau.node(from.tableau_idx) {
            Some(node) => node,
            None => {
                return Err(EvalError::Internal {
                    message: format!(
                        "missing tableau node in add_successors: \
                         tableau_idx={} for state_fp={}",
                        from.tableau_idx, from.state_fp
                    ),
                    span: None,
                });
            }
        };

        let tableau_succ_indices: Vec<_> = tableau_node.successors().iter().copied().collect();

        for succ_state in successors {
            let succ_fp = state_fp_of(succ_state)?;

            for &tableau_succ_idx in &tableau_succ_indices {
                let consistent = self.check_consistency_cached_with_fp(
                    succ_state,
                    succ_fp,
                    tableau_succ_idx,
                    get_successors,
                    tir,
                )?;
                if consistent {
                    if self.graph.add_successor_with_fp(
                        from,
                        succ_state,
                        succ_fp,
                        tableau_succ_idx,
                    )? {
                        let bg_node = BehaviorGraphNode::new(succ_fp, tableau_succ_idx);
                        added.push(bg_node);
                        self.stats.graph_nodes += 1;
                    }
                    self.stats.graph_edges += 1;
                }
            }
        }

        self.stats.states_explored += successors.len();
        Ok(added)
    }

    /// Explore the behavior graph using BFS
    ///
    /// This method performs a full BFS exploration of the behavior graph,
    /// starting from all initial states that are consistent with initial
    /// tableau nodes.
    ///
    /// # Arguments
    ///
    /// * `init_states` - All initial states from the model
    /// * `get_successors` - Function to compute successor states for a given state
    ///
    /// # Returns
    ///
    /// The number of behavior graph nodes explored
    pub fn explore_bfs<F>(
        &mut self,
        init_states: &[State],
        get_successors: &mut F,
        tir: Option<&TirProgram<'_>>,
    ) -> EvalResult<usize>
    where
        F: FnMut(&State) -> EvalResult<Vec<State>>,
    {
        let mut raw_fp = |state: &State| Ok(state.fingerprint());
        self.explore_bfs_with_state_fp(init_states, get_successors, tir, &mut raw_fp)
    }

    pub fn explore_bfs_with_state_fp<F, G>(
        &mut self,
        init_states: &[State],
        get_successors: &mut F,
        tir: Option<&TirProgram<'_>>,
        state_fp_of: &mut G,
    ) -> EvalResult<usize>
    where
        F: FnMut(&State) -> EvalResult<Vec<State>>,
        G: FnMut(&State) -> EvalResult<Fingerprint>,
    {
        let mut queue: std::collections::VecDeque<BehaviorGraphNode> =
            std::collections::VecDeque::new();

        // Add all initial states (with timing)
        let init_start = Instant::now();
        for init_state in init_states {
            let init_fp = state_fp_of(init_state)?;
            let added = self.add_initial_state_with_fp(init_state, init_fp, get_successors, tir)?;
            queue.extend(added);
        }
        self.stats.init_state_time_us += init_start.elapsed().as_micros() as u64;

        // BFS exploration
        while let Some(current) = queue.pop_front() {
            // Get the state for this behavior graph node (with timing)
            let clone_start = Instant::now();
            let state = self.clone_state_for_bfs(current)?;
            self.stats.state_clone_time_us += clone_start.elapsed().as_micros() as u64;

            // Compute (and cache) state successors (with timing).
            // Arc-wrapped to avoid O(n) Vec<State> clones on every BFS cache hit.
            let get_start = Instant::now();
            let state_successors: Arc<Vec<State>> =
                if let Some(cached) = self.state_successors.get(&current.state_fp) {
                    Arc::clone(cached)
                } else {
                    let succs = Arc::new(get_successors(&state)?);
                    self.state_successors
                        .insert(current.state_fp, Arc::clone(&succs));
                    succs
                };
            self.stats.get_successors_time_us += get_start.elapsed().as_micros() as u64;

            // Add successor (state, tableau) pairs (with timing)
            let add_start = Instant::now();
            let added = self.add_successors_with_state_fp(
                current,
                &state_successors,
                get_successors,
                tir,
                state_fp_of,
            )?;
            self.stats.add_successors_time_us += add_start.elapsed().as_micros() as u64;
            queue.extend(added);
        }

        Ok(self.stats.graph_nodes)
    }

    /// Build the behavior graph directly from the state graph, without
    /// tableau cross-product or consistency checking.
    ///
    /// This is the fast path for `tf == Bool(true)` (pure WF/SF fairness specs).
    /// Every state maps to a single `BehaviorGraphNode` with `tableau_idx = 0`.
    /// Equivalent to TLC's `LiveChecker` (no-tableau) path.
    ///
    /// Part of #2768.
    pub fn explore_state_graph_direct<F>(
        &mut self,
        init_states: &[State],
        get_successors: &mut F,
    ) -> EvalResult<usize>
    where
        F: FnMut(&State) -> EvalResult<Vec<State>>,
    {
        let mut raw_fp = |state: &State| Ok(state.fingerprint());
        self.explore_state_graph_direct_with_state_fp(init_states, get_successors, &mut raw_fp)
    }

    pub fn explore_state_graph_direct_with_state_fp<F, G>(
        &mut self,
        init_states: &[State],
        get_successors: &mut F,
        state_fp_of: &mut G,
    ) -> EvalResult<usize>
    where
        F: FnMut(&State) -> EvalResult<Vec<State>>,
        G: FnMut(&State) -> EvalResult<Fingerprint>,
    {
        let mut queue: std::collections::VecDeque<BehaviorGraphNode> =
            std::collections::VecDeque::new();

        // Add all initial states with tableau_idx = 0 (no consistency check needed)
        let init_start = Instant::now();
        for init_state in init_states {
            let init_fp = state_fp_of(init_state)?;
            if self
                .graph
                .try_add_init_node_with_fp(init_state, init_fp, 0)?
            {
                let bg_node = BehaviorGraphNode::new(init_fp, 0);
                queue.push_back(bg_node);
                self.stats.graph_nodes += 1;
            }
        }
        self.stats.init_state_time_us += init_start.elapsed().as_micros() as u64;
        self.stats.states_explored += init_states.len();

        // BFS exploration — state graph only, no tableau cross-product
        while let Some(current) = queue.pop_front() {
            let clone_start = Instant::now();
            let state = self.clone_state_for_bfs(current)?;
            self.stats.state_clone_time_us += clone_start.elapsed().as_micros() as u64;

            // Compute and cache state successors
            let get_start = Instant::now();
            let state_successors: Arc<Vec<State>> =
                if let Some(cached) = self.state_successors.get(&current.state_fp) {
                    Arc::clone(cached)
                } else {
                    let succs = Arc::new(get_successors(&state)?);
                    self.state_successors
                        .insert(current.state_fp, Arc::clone(&succs));
                    succs
                };
            self.stats.get_successors_time_us += get_start.elapsed().as_micros() as u64;

            // Add successors — all with tableau_idx = 0, no consistency check
            let add_start = Instant::now();
            for succ_state in state_successors.iter() {
                let succ_fp = state_fp_of(succ_state)?;
                if self
                    .graph
                    .add_successor_with_fp(current, succ_state, succ_fp, 0)?
                {
                    let bg_node = BehaviorGraphNode::new(succ_fp, 0);
                    queue.push_back(bg_node);
                    self.stats.graph_nodes += 1;
                }
                self.stats.graph_edges += 1;
            }
            self.stats.add_successors_time_us += add_start.elapsed().as_micros() as u64;
            self.stats.states_explored += state_successors.len();
        }

        Ok(self.stats.graph_nodes)
    }

    /// Part of #3065: Fingerprint-based direct exploration — zero State cloning.
    ///
    /// Like `explore_state_graph_direct` but works entirely with fingerprints.
    /// The successor closure returns fingerprint lists instead of State objects,
    /// and the behavior graph uses a shared state cache instead of cloning states.
    ///
    /// Eliminates O(V + E) State clones during graph construction, replacing them
    /// with O(1) fingerprint copies. States are only accessed via the shared cache
    /// when needed for evaluation (in `populate_node_check_masks`).
    ///
    /// Requires `graph.set_shared_state_cache()` to be called before this method.
    pub fn explore_state_graph_direct_fp<F>(
        &mut self,
        init_fps: &[crate::state::Fingerprint],
        get_successor_fps: &mut F,
    ) -> EvalResult<usize>
    where
        F: FnMut(crate::state::Fingerprint) -> EvalResult<Vec<crate::state::Fingerprint>>,
    {
        use crate::state::Fingerprint;
        let mut queue: std::collections::VecDeque<super::BehaviorGraphNode> =
            std::collections::VecDeque::new();

        // Add all initial states with tableau_idx = 0 (no consistency check, no clone)
        let init_start = Instant::now();
        for &fp in init_fps {
            if self.graph.try_add_init_node_by_fp(fp, 0)? {
                queue.push_back(super::BehaviorGraphNode::new(fp, 0));
                self.stats.graph_nodes += 1;
            }
        }
        self.stats.init_state_time_us += init_start.elapsed().as_micros() as u64;
        self.stats.states_explored += init_fps.len();

        // BFS exploration — fingerprint-only, no State cloning
        while let Some(current) = queue.pop_front() {
            let get_start = Instant::now();
            let succ_fps: Vec<Fingerprint> = get_successor_fps(current.state_fp)?;
            self.stats.get_successors_time_us += get_start.elapsed().as_micros() as u64;

            let add_start = Instant::now();
            for succ_fp in &succ_fps {
                if self.graph.add_successor_by_fp(current, *succ_fp, 0)? {
                    queue.push_back(super::BehaviorGraphNode::new(*succ_fp, 0));
                    self.stats.graph_nodes += 1;
                }
                self.stats.graph_edges += 1;
            }
            self.stats.add_successors_time_us += add_start.elapsed().as_micros() as u64;
            self.stats.states_explored += succ_fps.len();
        }

        Ok(self.stats.graph_nodes)
    }
}
