// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(dead_code)]

//! On-the-fly LTL checking via product automaton maintained during BFS.
//!
//! # Overview
//!
//! Traditional liveness checking in TLA2 (and TLC) is a two-phase process:
//! 1. BFS explores the full state graph, caching successors
//! 2. Post-BFS, the product of the state graph and tableau automaton is built
//!    and checked for accepting cycles via SCC detection
//!
//! On-the-fly checking maintains the product automaton *during* BFS
//! exploration, enabling early detection of liveness violations without
//! waiting for the full state graph to be constructed. This is the approach
//! described in Vardi & Wolper (1986) and Courcoubetis et al. (1992).
//!
//! # Architecture
//!
//! The module is organized into four sub-modules:
//!
//! - [`nba`]: LTL-to-NBA (Nondeterministic Buchi Automaton) translator for
//!   common temporal patterns ([]P, <>P, []<>P, <>[]P). Produces optimally
//!   small automata for these frequent patterns, falling back to tableau
//!   construction for general formulas.
//!
//! - [`product`]: Product state types and the incrementally-maintained
//!   product graph. A product state is `(system_fingerprint, buchi_state)`.
//!   The graph supports both Tarjan SCC detection and nested DFS.
//!
//! - [`nested_dfs`]: Classic Courcoubetis-Vardi-Wolper-Yannakakis nested
//!   DFS algorithm for accepting cycle detection. Runs in O(|V|+|E|) time
//!   and produces counterexample traces with prefix + cycle decomposition.
//!
//! # Algorithm
//!
//! For each liveness property `P`, we construct the Buchi automaton for `~P`
//! (via direct NBA construction or tableau). During BFS:
//!
//! 1. **On new state:** For each Buchi/tableau node consistent with the
//!    state, add the product pair `(state_fp, buchi_idx)` to the product
//!    graph.
//!
//! 2. **On new transition `(s, s')`:** For each product node `(s, q)` and
//!    each Buchi/tableau successor `q'` of `q`, if `s'` is consistent with
//!    `q'`, add the edge `(s,q) -> (s',q')` to the product graph.
//!
//! 3. **Cycle detection:** After each state-completion batch during BFS,
//!    run nested DFS (or Tarjan SCC) to detect accepting cycles.
//!
//! An accepting cycle in the product graph corresponds to a behavior that
//! satisfies `~P`, i.e., violates the property `P`.
//!
//! # Cycle Detection Strategy
//!
//! Two strategies are available:
//!
//! - **Tarjan SCC** (default): Finds all SCCs and checks each for Buchi
//!   acceptance. More expensive per invocation but finds all violations.
//!
//! - **Nested DFS**: Classic NDFS algorithm. Linear time, produces better
//!   counterexamples (prefix + cycle), and can be parallelized (CNDFS).
//!   Selected via [`CycleDetectionStrategy::NestedDfs`].
//!
//! # Integration
//!
//! The [`OnTheFlyLtlObserver`] (in `bfs/observer.rs`) is composed into the
//! BFS observer chain via [`CompositeObserver`]. It receives
//! `on_state_completion` calls when all successors of a state have been
//! generated. See `bfs/observer.rs` for the observer implementation.
//!
//! # Configuration
//!
//! Enabled via `TLA2_ON_THE_FLY_LTL=1` environment variable. When enabled,
//! properties are checked incrementally during BFS rather than in the
//! post-BFS liveness phase.
//!
//! # References
//!
//! - Vardi, M. Y. & Wolper, P. (1986). "An automata-theoretic approach to
//!   automatic program verification."
//! - Courcoubetis, C., Vardi, M. Y., Wolper, P. & Yannakakis, M. (1992).
//!   "Memory-efficient algorithms for the verification of temporal properties."
//! - Gastin, P. & Oddoux, D. (2001). "Fast LTL to Buchi Automata Translation."
//! - TLC implementation in `tlc2/tool/liveness/LiveCheck.java`

pub(crate) mod nba;
pub(crate) mod nested_dfs;
pub(crate) mod product;

use crate::liveness::live_expr::LiveExpr;
use crate::liveness::tableau::Tableau;

// Re-export core types for backward compatibility with existing observer code.
pub(crate) use product::{
    BuchiState, CycleDetectionResult, OnTheFlyStats, ProductGraph, ProductNode,
};

/// Strategy for detecting accepting cycles in the product graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CycleDetectionStrategy {
    /// Tarjan's SCC algorithm: finds all SCCs, checks each for acceptance.
    /// Robust and works incrementally on partially explored graphs.
    TarjanScc,
    /// Nested DFS (Courcoubetis-Vardi): linear-time cycle detection with
    /// better counterexample traces (prefix + cycle decomposition).
    NestedDfs,
}

impl Default for CycleDetectionStrategy {
    fn default() -> Self {
        Self::TarjanScc
    }
}

/// Source of the Buchi automaton: either a direct NBA pattern or a tableau.
#[derive(Debug)]
enum BuchiSource {
    /// Direct NBA from pattern matching (small, efficient).
    Nba(nba::Nba),
    /// General tableau construction (handles all formulas).
    Tableau(Tableau),
}

/// On-the-fly LTL checker maintaining the product automaton during BFS.
///
/// Tracks the product of the system state graph and the Buchi automaton
/// (NBA or tableau) for a single liveness property. Product nodes and edges
/// are added incrementally as BFS discovers new states and transitions.
///
/// # Construction
///
/// Use [`OnTheFlyLtlChecker::new`] for tableau-based construction (backward
/// compatible) or [`OnTheFlyLtlChecker::from_property`] to auto-select
/// between direct NBA construction and tableau based on formula pattern.
pub(crate) struct OnTheFlyLtlChecker {
    /// The Buchi automaton source (NBA or tableau).
    buchi: BuchiSource,
    /// The property name (for diagnostics).
    property_name: String,
    /// The product graph maintained incrementally.
    graph: ProductGraph,
    /// Promises (`<>r` subformulas) extracted from the formula.
    /// Used only for tableau-based checking (NBA doesn't need promises).
    promises: Vec<LiveExpr>,
    /// Initial product nodes (for nested DFS starting points).
    initial_nodes: Vec<ProductNode>,
    /// Running statistics.
    stats: OnTheFlyStats,
    /// Cycle detection strategy.
    strategy: CycleDetectionStrategy,
}

impl OnTheFlyLtlChecker {
    /// Create a new on-the-fly LTL checker from a negated formula using tableau.
    ///
    /// The `formula` should be the negation of the property (already in
    /// positive normal form), from which the tableau is constructed.
    ///
    /// This constructor preserves backward compatibility with the existing
    /// observer code.
    pub(crate) fn new(property_name: String, formula: LiveExpr) -> Self {
        let tableau = Tableau::new(formula.clone());
        let promises = formula.extract_promises();
        Self {
            buchi: BuchiSource::Tableau(tableau),
            property_name,
            graph: ProductGraph::new(),
            promises,
            initial_nodes: Vec::new(),
            stats: OnTheFlyStats::default(),
            strategy: CycleDetectionStrategy::default(),
        }
    }

    /// Create a checker that auto-selects between NBA and tableau.
    ///
    /// For common patterns ([]P, <>P, []<>P, <>[]P), uses a directly
    /// constructed NBA (fewer states, faster checking). For general
    /// formulas, falls back to tableau construction.
    ///
    /// The `property_formula` is the *original property* (not negated).
    /// Negation is handled internally.
    pub(crate) fn from_property(property_name: String, property_formula: &LiveExpr) -> Self {
        // Try direct NBA construction first.
        if let Some(nba) = nba::build_nba_for_pattern(&property_name, property_formula) {
            return Self {
                buchi: BuchiSource::Nba(nba),
                property_name,
                graph: ProductGraph::new(),
                promises: Vec::new(),
                initial_nodes: Vec::new(),
                stats: OnTheFlyStats::default(),
                strategy: CycleDetectionStrategy::NestedDfs,
            };
        }

        // Fall back to tableau for general formulas.
        let negated = LiveExpr::not(property_formula.clone()).push_negation();
        Self::new(property_name, negated)
    }

    /// Get the property name.
    pub(crate) fn property_name(&self) -> &str {
        &self.property_name
    }

    /// Get statistics.
    pub(crate) fn stats(&self) -> &OnTheFlyStats {
        &self.stats
    }

    /// Set the cycle detection strategy.
    pub(crate) fn set_strategy(&mut self, strategy: CycleDetectionStrategy) {
        self.strategy = strategy;
    }

    /// Get the tableau (if using tableau-based checking).
    ///
    /// Returns `None` for NBA-based checkers. The observer code uses this
    /// for backward compatibility.
    pub(crate) fn tableau(&self) -> Option<&Tableau> {
        match &self.buchi {
            BuchiSource::Tableau(t) => Some(t),
            BuchiSource::Nba(_) => None,
        }
    }

    /// Number of initial Buchi states.
    ///
    /// For tableau: number of initial tableau nodes.
    /// For NBA: number of initial NBA states.
    pub(crate) fn init_buchi_count(&self) -> usize {
        match &self.buchi {
            BuchiSource::Tableau(t) => t.init_count(),
            BuchiSource::Nba(nba) => nba.initial_states.len(),
        }
    }

    /// Backward-compatible alias for `init_buchi_count`.
    pub(crate) fn init_tableau_count(&self) -> usize {
        self.init_buchi_count()
    }

    /// Total number of Buchi states.
    pub(crate) fn buchi_state_count(&self) -> usize {
        match &self.buchi {
            BuchiSource::Tableau(t) => t.len(),
            BuchiSource::Nba(nba) => nba.state_count,
        }
    }

    /// Get successor Buchi states for a given Buchi state index.
    pub(crate) fn buchi_successors(&self, state_idx: usize) -> Vec<usize> {
        match &self.buchi {
            BuchiSource::Tableau(t) => t
                .node(state_idx)
                .map(|n| n.successors().iter().copied().collect())
                .unwrap_or_default(),
            BuchiSource::Nba(nba) => nba
                .successors(BuchiState(state_idx))
                .iter()
                .map(|(bs, _)| bs.0)
                .collect(),
        }
    }

    /// Check if a Buchi state is accepting.
    fn is_accepting_buchi_state(&self, state_idx: usize) -> bool {
        match &self.buchi {
            BuchiSource::Tableau(t) => {
                // For tableau, acceptance depends on promise fulfillment.
                // When there are no promises (e.g., formula is Bool(true)),
                // every state is trivially accepting — any cycle satisfies
                // the Buchi acceptance condition. This is consistent with
                // is_accepting_scc() which returns true for empty promises.
                // When promises exist, fall back to per-node acceptance check.
                if self.promises.is_empty() {
                    return true;
                }
                t.node(state_idx).is_some_and(|n| n.is_accepting())
            }
            BuchiSource::Nba(nba) => nba.is_accepting(BuchiState(state_idx)),
        }
    }

    /// Add a product node (if not already present).
    ///
    /// Called when a system state is consistent with a Buchi/tableau node.
    /// Returns `true` if the node was newly added.
    pub(crate) fn add_product_node(&mut self, node: ProductNode) -> bool {
        if self.graph.add_node(node) {
            self.stats.product_nodes += 1;
            true
        } else {
            false
        }
    }

    /// Register a product node as an initial node (for nested DFS).
    pub(crate) fn add_initial_node(&mut self, node: ProductNode) {
        self.add_product_node(node);
        if !self.initial_nodes.contains(&node) {
            self.initial_nodes.push(node);
        }
    }

    /// Add an edge in the product graph.
    ///
    /// Called when a system transition `(s -> s')` is consistent with a
    /// Buchi/tableau transition `(q -> q')`, creating the product edge
    /// `(s,q) -> (s',q')`.
    ///
    /// Returns `true` if this is a new edge.
    pub(crate) fn add_product_edge(&mut self, from: ProductNode, to: ProductNode) -> bool {
        self.add_product_node(from);
        self.add_product_node(to);

        if self.graph.add_edge(from, to) {
            self.stats.product_edges += 1;
            true
        } else {
            false
        }
    }

    /// Check whether the product graph currently contains an accepting cycle.
    ///
    /// Dispatches to either Tarjan SCC or nested DFS based on the configured
    /// strategy. Called after each state-completion batch during BFS.
    pub(crate) fn check_for_accepting_cycle(&mut self) -> CycleDetectionResult {
        self.stats.cycle_checks += 1;

        match self.strategy {
            CycleDetectionStrategy::TarjanScc => self.check_tarjan_scc(),
            CycleDetectionStrategy::NestedDfs => self.check_nested_dfs(),
        }
    }

    /// Tarjan SCC-based cycle detection.
    fn check_tarjan_scc(&mut self) -> CycleDetectionResult {
        let sccs = self.graph.find_sccs();

        for scc in &sccs {
            if scc.len() < 2 && !self.graph.has_self_loop(&scc[0]) {
                continue;
            }

            if self.is_accepting_scc(scc) {
                self.stats.violation_found = true;
                return CycleDetectionResult::AcceptingCycle { cycle: scc.clone() };
            }
        }

        CycleDetectionResult::NoCycle
    }

    /// Nested DFS-based cycle detection.
    fn check_nested_dfs(&mut self) -> CycleDetectionResult {
        let initial = if self.initial_nodes.is_empty() {
            // If no explicit initial nodes, use all nodes as potential starts.
            self.graph.nodes.iter().copied().collect::<Vec<_>>()
        } else {
            self.initial_nodes.clone()
        };

        let result = nested_dfs::nested_dfs(&self.graph, &initial, |node| {
            self.is_accepting_buchi_state(node.tableau_idx)
        });

        if matches!(result, CycleDetectionResult::AcceptingCycle { .. }) {
            self.stats.violation_found = true;
        }

        result
    }

    /// Check whether an SCC is accepting (for tableau-based checking).
    ///
    /// An SCC is accepting if every promise `<>r` from the formula is
    /// fulfilled by some node in the SCC.
    ///
    /// For NBA-based checking, an SCC is accepting if it contains at least
    /// one node with an accepting Buchi state.
    fn is_accepting_scc(&self, scc: &[ProductNode]) -> bool {
        match &self.buchi {
            BuchiSource::Nba(nba) => {
                // For NBA: SCC is accepting if it contains any accepting Buchi state.
                scc.iter()
                    .any(|node| nba.is_accepting(BuchiState(node.tableau_idx)))
            }
            BuchiSource::Tableau(tableau) => {
                if self.promises.is_empty() {
                    return true;
                }

                for promise in &self.promises {
                    let mut fulfilled = false;
                    for node in scc {
                        if let Some(tableau_node) = tableau.node(node.tableau_idx) {
                            if tableau_node.particle().is_fulfilling(promise) {
                                fulfilled = true;
                                break;
                            }
                        }
                    }
                    if !fulfilled {
                        return false;
                    }
                }

                true
            }
        }
    }

    /// Extract a counterexample cycle path from the accepting SCC.
    ///
    /// Returns a sequence of product nodes forming a cycle within the SCC.
    /// The first and last nodes in the returned vector are the same,
    /// representing the back-edge of the cycle.
    pub(crate) fn extract_cycle_path(&self, scc: &[ProductNode]) -> Vec<ProductNode> {
        if scc.is_empty() {
            return Vec::new();
        }

        let start = scc[0];
        let scc_set: rustc_hash::FxHashSet<ProductNode> = scc.iter().copied().collect();
        let mut visited = rustc_hash::FxHashSet::default();
        let mut path = Vec::new();

        if self.dfs_find_cycle(start, &scc_set, &mut visited, &mut path) {
            path
        } else {
            let mut cycle = scc.to_vec();
            cycle.push(start);
            cycle
        }
    }

    /// DFS to find a cycle within an SCC.
    fn dfs_find_cycle(
        &self,
        node: ProductNode,
        scc_set: &rustc_hash::FxHashSet<ProductNode>,
        visited: &mut rustc_hash::FxHashSet<ProductNode>,
        path: &mut Vec<ProductNode>,
    ) -> bool {
        path.push(node);
        visited.insert(node);

        for &succ in self.graph.get_successors(&node) {
            if !scc_set.contains(&succ) {
                continue;
            }
            if succ == path[0] {
                path.push(succ);
                return true;
            }
            if !visited.contains(&succ) && self.dfs_find_cycle(succ, scc_set, visited, path) {
                return true;
            }
        }

        path.pop();
        false
    }
}

/// Check whether on-the-fly LTL checking is enabled via environment variable.
///
/// Set `TLA2_ON_THE_FLY_LTL=1` to enable incremental product automaton
/// checking during BFS exploration.
/// Cached via `OnceLock` (Part of #4114).
pub(crate) fn on_the_fly_ltl_enabled() -> bool {
    static CACHED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *CACHED.get_or_init(|| {
        std::env::var("TLA2_ON_THE_FLY_LTL")
            .ok()
            .is_some_and(|v| v == "1" || v.eq_ignore_ascii_case("true"))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::liveness::live_expr::LiveExpr;
    use crate::state::Fingerprint;

    // ---- Backward-compatible tests (from original on_the_fly.rs) ----

    #[test]
    fn test_on_the_fly_checker_empty_graph_no_cycle() {
        let formula = LiveExpr::eventually(LiveExpr::Bool(true));
        let mut checker = OnTheFlyLtlChecker::new("TestProp".to_string(), formula);

        match checker.check_for_accepting_cycle() {
            CycleDetectionResult::NoCycle => {}
            CycleDetectionResult::AcceptingCycle { .. } => {
                panic!("empty graph should have no cycles")
            }
        }

        assert_eq!(checker.stats().product_nodes, 0);
        assert_eq!(checker.stats().product_edges, 0);
    }

    #[test]
    fn test_on_the_fly_checker_single_node_no_self_loop() {
        let formula = LiveExpr::eventually(LiveExpr::Bool(true));
        let mut checker = OnTheFlyLtlChecker::new("TestProp".to_string(), formula);

        let node = ProductNode::new(Fingerprint(1), 0);
        checker.add_product_node(node);

        match checker.check_for_accepting_cycle() {
            CycleDetectionResult::NoCycle => {}
            CycleDetectionResult::AcceptingCycle { .. } => {
                panic!("single node without self-loop should have no cycles")
            }
        }
    }

    #[test]
    fn test_on_the_fly_checker_self_loop_detected() {
        let formula = LiveExpr::Bool(true);
        let mut checker = OnTheFlyLtlChecker::new("TestProp".to_string(), formula);

        let node = ProductNode::new(Fingerprint(1), 0);
        checker.add_product_edge(node, node);

        match checker.check_for_accepting_cycle() {
            CycleDetectionResult::AcceptingCycle { cycle } => {
                assert!(!cycle.is_empty(), "cycle should contain at least one node");
            }
            CycleDetectionResult::NoCycle => {
                panic!("self-loop with no promises should be an accepting cycle")
            }
        }
    }

    #[test]
    fn test_on_the_fly_checker_two_node_cycle() {
        let formula = LiveExpr::Bool(true);
        let mut checker = OnTheFlyLtlChecker::new("TestProp".to_string(), formula);

        let a = ProductNode::new(Fingerprint(1), 0);
        let b = ProductNode::new(Fingerprint(2), 0);
        checker.add_product_edge(a, b);
        checker.add_product_edge(b, a);

        match checker.check_for_accepting_cycle() {
            CycleDetectionResult::AcceptingCycle { cycle } => {
                assert!(cycle.len() >= 2, "cycle should contain at least two nodes");
            }
            CycleDetectionResult::NoCycle => {
                panic!("two-node cycle with no promises should be accepting")
            }
        }
    }

    #[test]
    fn test_on_the_fly_checker_chain_no_cycle() {
        let formula = LiveExpr::Bool(true);
        let mut checker = OnTheFlyLtlChecker::new("TestProp".to_string(), formula);

        let a = ProductNode::new(Fingerprint(1), 0);
        let b = ProductNode::new(Fingerprint(2), 0);
        let c = ProductNode::new(Fingerprint(3), 0);
        checker.add_product_edge(a, b);
        checker.add_product_edge(b, c);

        match checker.check_for_accepting_cycle() {
            CycleDetectionResult::NoCycle => {}
            CycleDetectionResult::AcceptingCycle { .. } => {
                panic!("chain without back-edge should have no cycles")
            }
        }
    }

    #[test]
    fn test_on_the_fly_checker_duplicate_edges_idempotent() {
        let formula = LiveExpr::Bool(true);
        let mut checker = OnTheFlyLtlChecker::new("TestProp".to_string(), formula);

        let a = ProductNode::new(Fingerprint(1), 0);
        let b = ProductNode::new(Fingerprint(2), 0);

        assert!(checker.add_product_edge(a, b));
        assert!(!checker.add_product_edge(a, b));

        assert_eq!(checker.stats().product_edges, 1);
    }

    #[test]
    fn test_extract_cycle_path_from_two_node_scc() {
        let formula = LiveExpr::Bool(true);
        let mut checker = OnTheFlyLtlChecker::new("TestProp".to_string(), formula);

        let a = ProductNode::new(Fingerprint(1), 0);
        let b = ProductNode::new(Fingerprint(2), 0);
        checker.add_product_edge(a, b);
        checker.add_product_edge(b, a);

        let scc = vec![a, b];
        let path = checker.extract_cycle_path(&scc);

        assert!(path.len() >= 3, "cycle path should include back-edge");
        assert_eq!(
            path.first(),
            path.last(),
            "cycle path should start and end at the same node"
        );
    }

    #[test]
    fn test_on_the_fly_stats_tracking() {
        let formula = LiveExpr::Bool(true);
        let mut checker = OnTheFlyLtlChecker::new("TestProp".to_string(), formula);

        let a = ProductNode::new(Fingerprint(1), 0);
        let b = ProductNode::new(Fingerprint(2), 0);
        checker.add_product_edge(a, b);
        checker.add_product_edge(b, a);
        checker.check_for_accepting_cycle();

        assert_eq!(checker.stats().product_nodes, 2);
        assert_eq!(checker.stats().product_edges, 2);
        assert_eq!(checker.stats().cycle_checks, 1);
        assert!(checker.stats().violation_found);
    }

    // ---- New tests for NBA and nested DFS ----

    fn dummy_state_pred(tag: u32) -> LiveExpr {
        use std::sync::Arc;
        use tla_core::ast::Expr;
        use tla_core::Spanned;
        LiveExpr::state_pred(Arc::new(Spanned::dummy(Expr::Bool(true))), tag)
    }

    #[test]
    fn test_from_property_uses_nba_for_always_p() {
        let p = dummy_state_pred(1);
        let property = LiveExpr::always(p);
        let checker = OnTheFlyLtlChecker::from_property("AlwaysP".to_string(), &property);

        assert!(
            matches!(checker.buchi, BuchiSource::Nba(_)),
            "should use NBA for []P pattern"
        );
        assert_eq!(checker.init_buchi_count(), 1);
        assert_eq!(checker.buchi_state_count(), 2);
    }

    #[test]
    fn test_from_property_uses_nba_for_eventually_p() {
        let p = dummy_state_pred(1);
        let property = LiveExpr::eventually(p);
        let checker = OnTheFlyLtlChecker::from_property("EventuallyP".to_string(), &property);

        assert!(matches!(checker.buchi, BuchiSource::Nba(_)));
        assert_eq!(checker.buchi_state_count(), 1);
    }

    #[test]
    fn test_from_property_uses_nba_for_always_eventually_p() {
        let p = dummy_state_pred(1);
        let property = LiveExpr::always(LiveExpr::eventually(p));
        let checker = OnTheFlyLtlChecker::from_property("AEP".to_string(), &property);

        assert!(matches!(checker.buchi, BuchiSource::Nba(_)));
        assert_eq!(checker.buchi_state_count(), 2);
    }

    #[test]
    fn test_from_property_falls_back_to_tableau_for_general() {
        let p = dummy_state_pred(1);
        // Plain state predicate: no known temporal pattern
        let checker = OnTheFlyLtlChecker::from_property("General".to_string(), &p);

        assert!(
            matches!(checker.buchi, BuchiSource::Tableau(_)),
            "should fall back to tableau for general formula"
        );
    }

    #[test]
    fn test_nested_dfs_strategy_detects_cycle() {
        let formula = LiveExpr::Bool(true);
        let mut checker = OnTheFlyLtlChecker::new("TestNDFS".to_string(), formula);
        checker.set_strategy(CycleDetectionStrategy::NestedDfs);

        let a = ProductNode::new(Fingerprint(1), 0);
        let b = ProductNode::new(Fingerprint(2), 0);
        checker.add_initial_node(a);
        checker.add_product_edge(a, b);
        checker.add_product_edge(b, a);

        match checker.check_for_accepting_cycle() {
            CycleDetectionResult::AcceptingCycle { cycle } => {
                assert!(!cycle.is_empty());
            }
            CycleDetectionResult::NoCycle => {
                panic!("nested DFS should detect the two-node cycle")
            }
        }
    }

    #[test]
    fn test_nested_dfs_strategy_no_false_positive() {
        let formula = LiveExpr::Bool(true);
        let mut checker = OnTheFlyLtlChecker::new("TestNDFS".to_string(), formula);
        checker.set_strategy(CycleDetectionStrategy::NestedDfs);

        let a = ProductNode::new(Fingerprint(1), 0);
        let b = ProductNode::new(Fingerprint(2), 0);
        let c = ProductNode::new(Fingerprint(3), 0);
        checker.add_initial_node(a);
        checker.add_product_edge(a, b);
        checker.add_product_edge(b, c);

        match checker.check_for_accepting_cycle() {
            CycleDetectionResult::NoCycle => {}
            CycleDetectionResult::AcceptingCycle { .. } => {
                panic!("chain without back-edge should not be a cycle")
            }
        }
    }

    #[test]
    fn test_nba_checker_with_ndfs_detects_accepting_cycle() {
        // Build a checker for property []P and show violation detection works
        // when the product graph has an accepting cycle.
        let p = dummy_state_pred(1);
        let property = LiveExpr::always(p);
        let mut checker = OnTheFlyLtlChecker::from_property("AlwaysP".to_string(), &property);

        // NBA for []P has: q0 (initial), q1 (accepting sink).
        // Construct product: state s1 at buchi q1 with self-loop.
        // This represents a state where P is violated and the system loops.
        let accepting_node = ProductNode::new(Fingerprint(1), 1);
        checker.add_initial_node(ProductNode::new(Fingerprint(1), 0));
        checker.add_product_edge(ProductNode::new(Fingerprint(1), 0), accepting_node);
        checker.add_product_edge(accepting_node, accepting_node);

        match checker.check_for_accepting_cycle() {
            CycleDetectionResult::AcceptingCycle { cycle } => {
                assert!(
                    cycle.iter().any(|n| n.tableau_idx == 1),
                    "cycle should include accepting Buchi state 1"
                );
            }
            CycleDetectionResult::NoCycle => {
                panic!("should detect accepting cycle through q1 self-loop")
            }
        }
    }

    #[test]
    fn test_buchi_successors_nba() {
        let p = dummy_state_pred(1);
        let property = LiveExpr::always(p);
        let checker = OnTheFlyLtlChecker::from_property("Test".to_string(), &property);

        // For []P NBA: q0 has transitions to q0 and q1, q1 has self-loop.
        let q0_succs = checker.buchi_successors(0);
        assert_eq!(q0_succs.len(), 2, "q0 should have 2 successors (q0, q1)");

        let q1_succs = checker.buchi_successors(1);
        assert_eq!(q1_succs.len(), 1, "q1 should have 1 successor (self-loop)");
    }

    #[test]
    fn test_buchi_successors_tableau() {
        let formula = LiveExpr::eventually(LiveExpr::Bool(true));
        let checker = OnTheFlyLtlChecker::new("TestTab".to_string(), formula);

        // Tableau for <>TRUE should have at least one node with successors.
        let succs = checker.buchi_successors(0);
        assert!(
            !succs.is_empty(),
            "tableau node 0 for <>TRUE should have at least one successor"
        );
    }
}
