// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Liveness checker implementation
//!
//! This module implements the product graph exploration for liveness checking.
//! The product graph is the cross-product of:
//! - The state graph (TLA+ states connected by Next relation)
//! - The tableau automaton (derived from negation of liveness property)
//!
//! A liveness violation exists iff there's an accepting cycle in this product graph.
//!
//! # TLC Reference
//!
//! This follows TLC's implementation in:
//! - `tlc2/tool/liveness/LiveCheck.java` - Main liveness checker
//! - `tlc2/tool/liveness/LiveWorker.java` - SCC detection
//!
//! # Phases
//!
//! Phase B2 (this file): Behavior graph construction
//! Phase B3: SCC detection using Tarjan's algorithm
//!
//! # Module Structure
//!
//! - `types` — Data types, type aliases, and debug flags
//! - `enabled_cache` — Thread-local ENABLED evaluation cache
//! - `subscript_cache` — Subscript expression evaluation and value cache
//! - `explore` — BFS graph construction (initial states, successors, exploration loops)
//! - `plan` — Formula decomposition into DNF clauses and PEM plans
//! - `scc_checks` — SCC constraint satisfaction, witness cycle construction, path finding
//! - `checks` — Top-level liveness checking entrypoint and counterexample construction
//! - `eval` — Expression evaluation against concrete states and transitions

mod cache_stats;
mod check_mask;
mod checks;
mod ea_bitmask_query;
mod ea_precompute;
mod ea_precompute_cache;
mod ea_precompute_enabled;
mod ea_precompute_leaf_batch;
mod ea_precompute_profile;
mod ea_precompute_subscript;
pub(crate) mod enabled_cache;
mod eval;
mod explore;
mod plan;
mod scc_checks;
mod subscript_cache;
mod types;

pub(crate) use cache_stats::log_cache_stats;
pub(crate) use check_mask::CheckMask;

pub(crate) use enabled_cache::{
    clear_enabled_cache, eval_enabled_cached, eval_enabled_cached_mut, get_enabled_cached,
    is_enabled_cached, set_enabled_cache,
};
// Part of #3100 Phase A0: array-native inline subscript caching.
pub(crate) use subscript_cache::clear_subscript_value_cache;
pub(crate) use subscript_cache::eval_subscript_changed_array_cached;
pub(crate) use types::InlineCheckResults;
#[cfg(test)]
pub use types::LivenessConstraints;
#[cfg(test)]
pub(super) use types::SccEdgeList;
#[cfg(debug_assertions)]
pub(super) use types::{debug_action_pred, debug_bindings, debug_changed};
pub(super) use types::{debug_subscript, CounterexamplePath};
pub use types::{GroupedLivenessPlan, LivenessResult, LivenessStats, PemPlan};

use super::behavior_graph::{BehaviorGraph, BehaviorGraphNode};
use super::consistency::is_state_consistent;
pub(super) use super::live_expr;
use super::live_expr::LiveExpr;
use super::tableau::Tableau;
use super::SuccessorWitnessMap;
use crate::error::{EvalError, EvalResult};
use crate::eval::{Env, EvalCtx};
use crate::state::{Fingerprint, State};
use rustc_hash::FxHashMap;
use tla_eval::tir::TirProgram;

use std::sync::Arc;

/// Soft cap for instance-local consistency cache entries. Entries are
/// lightweight bools, so keep this aligned with the ENABLED cache.
const CONSISTENCY_CACHE_SOFT_CAP: usize = 200_000;
/// Soft cap for cached state environments. These entries are heavier than the
/// bool caches, so use the smaller subscript-cache-style bound.
const STATE_ENV_CACHE_SOFT_CAP: usize = 50_000;

fn retain_half_if_needed<K, V>(map: &mut FxHashMap<K, V>, soft_cap: usize) {
    if map.len() <= soft_cap {
        return;
    }

    let target = soft_cap / 2;
    let mut kept = 0usize;
    map.retain(|_, _| {
        if kept < target {
            kept += 1;
            true
        } else {
            false
        }
    });
}

/// Liveness checker that builds and analyzes the behavior graph
///
/// The behavior graph is the product of state graph × tableau automaton.
/// Liveness checking proceeds in phases:
/// 1. Build behavior graph during state exploration
/// 2. Find strongly connected components (SCCs)
/// 3. Check each SCC for accepting cycles
pub struct LivenessChecker {
    /// The tableau automaton for the liveness property
    tableau: Tableau,
    /// The behavior graph (product of state graph × tableau)
    graph: BehaviorGraph,
    /// Base evaluation context for checking consistency
    ctx: EvalCtx,
    /// Promises (<>r) extracted from the tableau temporal formula
    promises: Vec<LiveExpr>,
    /// AE/EA constraints that must be satisfied by a counterexample cycle (test-only reader)
    #[cfg(test)]
    constraints: LivenessConstraints,
    /// Cached state graph successors (needed for ENABLED), keyed by the
    /// behavior-graph state fingerprint.
    /// Arc-wrapped to allow O(1) clones during BFS instead of cloning the full Vec<State>.
    state_successors: FxHashMap<crate::state::Fingerprint, Arc<Vec<State>>>,
    /// Cached successor fingerprints for the direct fingerprint-only graph path,
    /// keyed by the behavior-graph state fingerprint.
    ///
    /// This preserves the zero-clone behavior of `explore_state_graph_direct_fp`.
    /// ENABLED evaluation resolves states through `BehaviorGraph::shared_state_cache`
    /// on demand instead of materializing a second `Vec<State>` per source state.
    state_successor_fps: FxHashMap<crate::state::Fingerprint, Arc<Vec<Fingerprint>>>,
    /// Cached consistency check results: (behavior-graph state_fp, tableau_idx) -> is_consistent
    consistency_cache: FxHashMap<(crate::state::Fingerprint, usize), bool>,
    /// Optional mapping from representative state fingerprint -> canonical fingerprint (symmetry).
    state_fp_to_canon_fp: Option<Arc<FxHashMap<Fingerprint, Fingerprint>>>,
    /// Concrete successor witnesses keyed by canonical source fingerprint.
    ///
    /// Each entry contains `(canonical_dest_fp, successor_state)` pairs for each
    /// concrete successor generated from the representative source state.
    ///
    /// When present, this is used to evaluate ENABLED and action predicates under symmetry.
    succ_witnesses: Option<Arc<SuccessorWitnessMap>>,
    /// Statistics
    stats: LivenessStats,
    /// Cached Env representations of states, keyed by fingerprint.
    /// Avoids repeated FxHashMap construction during SCC constraint checking.
    state_env_cache: FxHashMap<Fingerprint, Arc<Env>>,
}

impl LivenessChecker {
    fn behavior_graph_invariant_error(message: String) -> EvalError {
        EvalError::Internal {
            message: format!("behavior graph invariant violated: {message}"),
            span: None,
        }
    }

    // ---- Construction ----

    /// Create a new liveness checker
    ///
    /// # Arguments
    ///
    /// * `tableau` - The tableau automaton for the liveness property
    /// * `ctx` - Base evaluation context (with operators loaded)
    // Test-only constructor; production entry points use `new_from_env` so the
    // runtime graph-storage gate can switch between in-memory and disk-backed
    // behavior graphs.
    #[cfg(test)]
    pub fn new(tableau: Tableau, ctx: EvalCtx) -> Self {
        // Collect ALL promises from the formula. Promises are <> subformulas that
        // must be fulfilled somewhere in any accepting SCC. The tableau expansion
        // and is_fulfilling check handle the fulfillment semantics correctly for
        // promises with temporal bodies (e.g., <>(P /\ []Q)).
        //
        // Previously, promises with temporal-level bodies were filtered out, but this
        // caused false positives: for <>(terminated /\ []~terminationDetected), the
        // promise was not tracked, so any SCC was considered violating.
        let promises = tableau.formula().extract_promises();

        let _ = cache_stats::take_cache_stats();

        Self {
            tableau,
            graph: BehaviorGraph::new(),
            ctx,
            promises,
            #[cfg(test)]
            constraints: LivenessConstraints::default(),
            state_successors: FxHashMap::default(),
            state_successor_fps: FxHashMap::default(),
            consistency_cache: FxHashMap::default(),
            state_fp_to_canon_fp: None,
            succ_witnesses: None,
            stats: LivenessStats::default(),
            state_env_cache: FxHashMap::default(),
        }
    }

    /// Create a new liveness checker honoring runtime graph-storage gates.
    pub fn new_from_env(tableau: Tableau, ctx: EvalCtx) -> EvalResult<Self> {
        let promises = tableau.formula().extract_promises();
        let _ = cache_stats::take_cache_stats();

        Ok(Self {
            tableau,
            graph: BehaviorGraph::new_from_env()?,
            ctx,
            promises,
            #[cfg(test)]
            constraints: LivenessConstraints::default(),
            state_successors: FxHashMap::default(),
            state_successor_fps: FxHashMap::default(),
            consistency_cache: FxHashMap::default(),
            state_fp_to_canon_fp: None,
            succ_witnesses: None,
            stats: LivenessStats::default(),
            state_env_cache: FxHashMap::default(),
        })
    }

    /// Create a new liveness checker with auto-disk detection based on an
    /// estimated behavior-graph node count.
    ///
    /// When `estimated_nodes` exceeds the auto-disk threshold (default 2M),
    /// the behavior graph is automatically disk-backed to prevent OOM on
    /// multi-property liveness specs.
    pub fn new_from_env_with_hint(
        tableau: Tableau,
        ctx: EvalCtx,
        estimated_nodes: Option<usize>,
    ) -> EvalResult<Self> {
        let promises = tableau.formula().extract_promises();
        let _ = cache_stats::take_cache_stats();

        Ok(Self {
            tableau,
            graph: BehaviorGraph::new_from_env_with_hint(estimated_nodes)?,
            ctx,
            promises,
            #[cfg(test)]
            constraints: LivenessConstraints::default(),
            state_successors: FxHashMap::default(),
            state_successor_fps: FxHashMap::default(),
            consistency_cache: FxHashMap::default(),
            state_fp_to_canon_fp: None,
            succ_witnesses: None,
            stats: LivenessStats::default(),
            state_env_cache: FxHashMap::default(),
        })
    }

    /// Create a new liveness checker with additional AE/EA constraints.
    #[cfg(test)]
    pub fn new_with_constraints(
        tableau: Tableau,
        ctx: EvalCtx,
        constraints: LivenessConstraints,
    ) -> Self {
        let promises = tableau.formula().extract_promises();
        let _ = cache_stats::take_cache_stats();

        Self {
            tableau,
            graph: BehaviorGraph::new(),
            ctx,
            promises,
            constraints,
            state_successors: FxHashMap::default(),
            state_successor_fps: FxHashMap::default(),
            consistency_cache: FxHashMap::default(),
            state_fp_to_canon_fp: None,
            succ_witnesses: None,
            stats: LivenessStats::default(),
            state_env_cache: FxHashMap::default(),
        }
    }

    /// Provide precomputed successor information for symmetry-aware liveness evaluation.
    ///
    /// When symmetry reduction is enabled, liveness checking needs access to the concrete
    /// successor states (not just canonical fingerprints) to correctly evaluate `ENABLED`
    /// and action-level predicates. TLC evaluates action checks on the concrete successor
    /// states *before* applying symmetry.
    pub fn set_successor_maps(
        &mut self,
        state_fp_to_canon_fp: Arc<FxHashMap<Fingerprint, Fingerprint>>,
        succ_witnesses: Option<Arc<SuccessorWitnessMap>>,
    ) {
        self.state_fp_to_canon_fp = Some(state_fp_to_canon_fp);
        self.succ_witnesses = succ_witnesses;
    }

    /// Part of #3065: Set a shared state cache on the behavior graph.
    /// Allows fingerprint-based exploration without cloning State objects.
    pub fn set_behavior_graph_shared_cache(&mut self, cache: Arc<FxHashMap<Fingerprint, State>>) {
        self.graph.set_shared_state_cache(cache);
    }

    /// Part of #3065: Populate successor fingerprints from the behavior graph
    /// after fingerprint-based exploration.
    ///
    /// `explore_state_graph_direct_fp` works with fingerprints only and does
    /// not populate `state_successors`. But `populate_node_check_masks` needs
    /// successor information for ENABLED evaluation. Without this call, ENABLED
    /// always returns FALSE, causing spurious liveness violations for specs
    /// with WF/SF fairness constraints.
    pub fn populate_state_successor_fps_from_graph(&mut self) -> EvalResult<()> {
        for node in self.graph.node_keys() {
            let fp = node.state_fp;
            if self.state_successors.contains_key(&fp) || self.state_successor_fps.contains_key(&fp)
            {
                continue;
            }
            let succ_fps: Vec<Fingerprint> = self
                .graph
                .try_get_node_info(&node)?
                .map(|info| info.successors.iter().map(|succ| succ.state_fp).collect())
                .unwrap_or_default();
            self.state_successor_fps.insert(fp, Arc::new(succ_fps));
        }
        Ok(())
    }

    // ---- Accessors ----

    /// Get the behavior graph
    #[cfg(test)]
    pub fn graph(&self) -> &BehaviorGraph {
        &self.graph
    }

    /// Get statistics
    pub fn stats(&self) -> &LivenessStats {
        &self.stats
    }

    /// Collect thread-local cache stats into `self.stats`.
    ///
    /// Call this once before reading stats, after liveness checking is complete.
    /// Thread-local counters are consumed (reset to 0) so this is not idempotent.
    /// Part of #4083: cache profiling.
    pub fn collect_cache_stats(&mut self) {
        let (subscript, enabled) = cache_stats::take_cache_stats();
        self.stats.subscript_cache_hits += subscript.hits;
        self.stats.subscript_cache_misses += subscript.misses;
        self.stats.subscript_cache_evictions += subscript.evictions;
        self.stats.enabled_cache_hits += enabled.hits;
        self.stats.enabled_cache_misses += enabled.misses;
        self.stats.enabled_cache_evictions += enabled.evictions;
    }

    /// Get AE/EA constraints.
    #[cfg(test)]
    pub fn constraints(&self) -> &LivenessConstraints {
        &self.constraints
    }

    // ---- State / consistency caching ----

    /// Get or create a cached Env for a state.
    ///
    /// This avoids repeated hash map construction during SCC constraint checking,
    /// which can be called thousands of times on the same states.
    fn get_cached_env(&mut self, state: &State) -> Arc<Env> {
        let fp = state.fingerprint();
        if let Some(env) = self.state_env_cache.get(&fp) {
            self.stats.state_env_cache_hits += 1;
            return Arc::clone(env);
        }
        self.stats.state_env_cache_misses += 1;

        // Build Env from state vars
        let mut env = Env::new();
        for (name, value) in state.vars() {
            env.insert(Arc::clone(name), value.clone());
        }
        let env = Arc::new(env);
        retain_half_if_needed(&mut self.state_env_cache, STATE_ENV_CACHE_SOFT_CAP);
        self.state_env_cache.insert(fp, Arc::clone(&env));
        env
    }

    fn get_cached_env_by_fp(&mut self, fp: Fingerprint) -> EvalResult<Arc<Env>> {
        if let Some(env) = self.state_env_cache.get(&fp) {
            self.stats.state_env_cache_hits += 1;
            return Ok(Arc::clone(env));
        }
        self.stats.state_env_cache_misses += 1;

        let env = {
            let state = self.graph.get_state_by_fp(fp).ok_or_else(|| {
                Self::behavior_graph_invariant_error(format!(
                    "state_env_cache: missing state for fingerprint {fp}"
                ))
            })?;
            let mut env = self.ctx.env().clone();
            for (name, value) in state.vars() {
                env.insert(Arc::clone(name), value.clone());
            }
            Arc::new(env)
        };

        retain_half_if_needed(&mut self.state_env_cache, STATE_ENV_CACHE_SOFT_CAP);
        self.state_env_cache.insert(fp, Arc::clone(&env));
        Ok(env)
    }

    fn successor_states_for_enabled(&self, fp: Fingerprint) -> Vec<State> {
        if let Some(witnesses) = self.succ_witnesses.as_ref().and_then(|map| map.get(&fp)) {
            // Part of #2661: Convert ArrayState→State lazily on the SCC ENABLED path.
            let registry = self.ctx.var_registry();
            return witnesses
                .iter()
                .map(|(_, arr)| arr.to_state(registry))
                .collect();
        }
        if let Some(succs) = self.state_successors.get(&fp) {
            return succs.as_ref().clone();
        }
        self.state_successor_fps
            .get(&fp)
            .map(|succ_fps| {
                succ_fps
                    .iter()
                    .filter_map(|succ_fp| self.graph.get_state_by_fp(*succ_fp).cloned())
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Check consistency with caching. Returns cached result if available.
    fn check_consistency_cached_with_fp<F>(
        &mut self,
        state: &State,
        state_fp: Fingerprint,
        tableau_idx: usize,
        get_successors: &mut F,
        tir: Option<&TirProgram<'_>>,
    ) -> EvalResult<bool>
    where
        F: FnMut(&State) -> EvalResult<Vec<State>>,
    {
        let cache_key = (state_fp, tableau_idx);

        // Check cache first
        if let Some(&cached) = self.consistency_cache.get(&cache_key) {
            self.stats.consistency_cache_hits += 1;
            return Ok(cached);
        }
        self.stats.consistency_cache_misses += 1;

        // Compute and cache the result
        self.stats.consistency_checks += 1;
        let tableau_node = match self.tableau.node(tableau_idx) {
            Some(n) => n,
            None => {
                return Err(EvalError::Internal {
                    message: format!(
                        "missing tableau node in check_consistency_cached: \
                         tableau_idx={tableau_idx} for state_fp={state_fp}"
                    ),
                    span: None,
                });
            }
        };

        let consistent = is_state_consistent(&self.ctx, state, tableau_node, get_successors, tir)?;
        retain_half_if_needed(&mut self.consistency_cache, CONSISTENCY_CACHE_SOFT_CAP);
        self.consistency_cache.insert(cache_key, consistent);
        Ok(consistent)
    }

    #[allow(dead_code)]
    fn check_consistency_cached<F>(
        &mut self,
        state: &State,
        tableau_idx: usize,
        get_successors: &mut F,
        tir: Option<&TirProgram<'_>>,
    ) -> EvalResult<bool>
    where
        F: FnMut(&State) -> EvalResult<Vec<State>>,
    {
        self.check_consistency_cached_with_fp(
            state,
            state.fingerprint(),
            tableau_idx,
            get_successors,
            tir,
        )
    }

    /// Find strongly connected components in the behavior graph
    ///
    /// Returns all SCCs using Tarjan's algorithm.
    pub fn find_sccs(&self) -> super::tarjan::TarjanResult {
        super::tarjan::find_sccs(&self.graph)
    }

    /// Find non-trivial cycles in the behavior graph.
    ///
    /// Returns a `TarjanResult` with SCCs filtered to actual cycles
    /// (not single nodes without self-loops). Callers should check
    /// `result.errors` for algorithm invariant violations. Part of #1817.
    #[cfg(test)]
    pub(crate) fn find_cycles(&self) -> super::tarjan::TarjanResult {
        super::tarjan::find_cycles(&self.graph)
    }
}

#[cfg(test)]
mod tests;
