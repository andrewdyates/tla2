// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(dead_code)]

//! On-the-fly LTL checking via Buchi automaton product construction.
//!
//! This module provides a self-contained API for LTL model checking using the
//! automata-theoretic approach:
//!
//! 1. Parse an LTL property into an [`LtlFormula`]
//! 2. Negate the formula and convert to a Buchi automaton via [`ltl_to_buchi`]
//! 3. Build the synchronous product of the system state graph and the Buchi automaton
//! 4. Detect accepting cycles in the product graph via [`check_product_accepting_cycle`]
//!
//! An accepting cycle in the product graph witnesses a behavior of the system
//! that violates the LTL property.
//!
//! # Supported temporal operators
//!
//! - `[]` (Always / Globally) — `LtlFormula::Always`
//! - `<>` (Eventually / Finally) — `LtlFormula::Eventually`
//! - `[]<>` (Infinitely often) — composed as `Always(Eventually(...))`
//! - `<>[]` (Eventually always / stability) — composed as `Eventually(Always(...))`
//!
//! # References
//!
//! - Vardi, M. Y. & Wolper, P. (1986). "An automata-theoretic approach to
//!   automatic program verification."
//! - Gerth, R., Peled, D., Vardi, M. Y. & Wolper, P. (1995). "Simple on-the-fly
//!   automatic verification of linear temporal logic." (GPVW / LTL2BA)
//! - Courcoubetis, C., Vardi, M. Y., Wolper, P. & Yannakakis, M. (1992).
//!   "Memory-efficient algorithms for the verification of temporal properties."
//! - TLC implementation in `tlc2/tool/liveness/LiveCheck.java`

use crate::check::Trace;
use crate::state::{Fingerprint, State};
use rustc_hash::{FxHashMap, FxHashSet};

// ---------------------------------------------------------------------------
// LTL Formula
// ---------------------------------------------------------------------------

/// An LTL formula over atomic propositions identified by `u32` tags.
///
/// Tags correspond to state predicates that can be evaluated against a
/// concrete [`State`].  The formula grammar covers propositional logic
/// plus the four core LTL temporal operators needed for TLA+ liveness:
/// `Always`, `Eventually`, and their compositions `[]<>` and `<>[]`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum LtlFormula {
    /// Boolean constant.
    Bool(bool),
    /// Atomic proposition identified by a unique tag.
    Atom(u32),
    /// Negation.
    Not(Box<LtlFormula>),
    /// Conjunction.
    And(Vec<LtlFormula>),
    /// Disjunction.
    Or(Vec<LtlFormula>),
    /// `[]P` — P holds in every state of the suffix.
    Always(Box<LtlFormula>),
    /// `<>P` — P holds in some future state.
    Eventually(Box<LtlFormula>),
}

impl LtlFormula {
    /// Negate the formula, pushing negation to atoms (positive normal form).
    ///
    /// The result only contains `Not` around `Atom` or `Bool` nodes.
    /// Temporal operators are dualized: `~[]P = <>~P`, `~<>P = []~P`.
    #[must_use]
    pub(crate) fn negate(&self) -> LtlFormula {
        match self {
            LtlFormula::Bool(b) => LtlFormula::Bool(!b),
            LtlFormula::Atom(_) => LtlFormula::Not(Box::new(self.clone())),
            LtlFormula::Not(inner) => (**inner).clone(),
            LtlFormula::And(conjuncts) => {
                LtlFormula::Or(conjuncts.iter().map(|c| c.negate()).collect())
            }
            LtlFormula::Or(disjuncts) => {
                LtlFormula::And(disjuncts.iter().map(|d| d.negate()).collect())
            }
            // De Morgan for temporal operators:
            // ~[]P  =  <>~P
            LtlFormula::Always(inner) => LtlFormula::Eventually(Box::new(inner.negate())),
            // ~<>P  =  []~P
            LtlFormula::Eventually(inner) => LtlFormula::Always(Box::new(inner.negate())),
        }
    }

    /// Check whether this formula is in positive normal form (PNF).
    ///
    /// PNF means `Not` only appears directly above `Atom` or `Bool`.
    #[must_use]
    fn is_pnf(&self) -> bool {
        match self {
            LtlFormula::Bool(_) | LtlFormula::Atom(_) => true,
            LtlFormula::Not(inner) => {
                matches!(**inner, LtlFormula::Atom(_) | LtlFormula::Bool(_))
            }
            LtlFormula::And(cs) => cs.iter().all(LtlFormula::is_pnf),
            LtlFormula::Or(ds) => ds.iter().all(LtlFormula::is_pnf),
            LtlFormula::Always(inner) | LtlFormula::Eventually(inner) => inner.is_pnf(),
        }
    }
}

// ---------------------------------------------------------------------------
// Buchi Automaton
// ---------------------------------------------------------------------------

/// Index of a state within an [`LtlAutomaton`].
pub(crate) type AutomatonStateId = usize;

/// A transition in the Buchi automaton.
///
/// The `guard` is a set of (atom_tag, polarity) pairs.  The transition is
/// enabled when every atom evaluates to the required polarity in the current
/// system state.
#[derive(Debug, Clone)]
pub(crate) struct BuchiTransition {
    /// Target automaton state.
    pub(crate) target: AutomatonStateId,
    /// Guard: vector of `(atom_tag, required_value)`.
    ///
    /// The transition fires when *every* atom evaluates to its required value.
    /// An empty guard means the transition is unconditional.
    pub(crate) guard: Vec<(u32, bool)>,
}

/// Generalized Buchi automaton (GBA) produced by [`ltl_to_buchi`].
///
/// States are indexed `0..state_count`.  `initial_states` are the entry
/// points.  `accepting_sets` contains one or more sets of accepting states;
/// an infinite run is accepting iff it visits *every* accepting set
/// infinitely often (generalized Buchi acceptance).
///
/// For simple `<>P` properties there is exactly one accepting set
/// (states where `P` holds).  For `[]<>P /\ []<>Q` there are two.
#[derive(Debug, Clone)]
pub(crate) struct LtlAutomaton {
    /// Total number of automaton states.
    pub(crate) state_count: usize,
    /// Set of initial automaton state ids.
    pub(crate) initial_states: Vec<AutomatonStateId>,
    /// Transitions keyed by source state.
    pub(crate) transitions: FxHashMap<AutomatonStateId, Vec<BuchiTransition>>,
    /// Generalized accepting sets.
    ///
    /// A run is accepting iff for *each* inner `FxHashSet` it visits some
    /// member infinitely often.
    pub(crate) accepting_sets: Vec<FxHashSet<AutomatonStateId>>,
}

impl LtlAutomaton {
    /// Get transitions from a given state (empty slice if none).
    pub(crate) fn transitions_from(&self, state: AutomatonStateId) -> &[BuchiTransition] {
        self.transitions.get(&state).map_or(&[], |v| v.as_slice())
    }

    /// Check whether a given state is accepting in *all* acceptance sets.
    ///
    /// For standard (non-generalized) Buchi, there is one set.
    #[must_use]
    pub(crate) fn is_accepting(&self, state: AutomatonStateId) -> bool {
        self.accepting_sets.iter().all(|set| set.contains(&state))
    }

    /// Return the number of acceptance sets (1 for standard Buchi).
    pub(crate) fn acceptance_set_count(&self) -> usize {
        self.accepting_sets.len()
    }
}

// ---------------------------------------------------------------------------
// LTL -> Buchi Conversion
// ---------------------------------------------------------------------------

/// Convert an LTL formula to a Buchi automaton that accepts exactly the
/// *models* (infinite words) satisfying the formula.
///
/// The construction follows a simplified GPVW (Gerth-Peled-Vardi-Wolper)
/// tableau expansion:
///
/// 1. Negate the formula and convert to positive normal form (PNF).
/// 2. Expand the PNF formula into a set of "obligation" nodes using
///    alpha/beta expansion rules (same as Manna-Pnueli tableau).
/// 3. Each fully-expanded obligation node becomes an automaton state.
/// 4. Transitions are derived from the "next" obligations of each node.
/// 5. Accepting sets are derived from `<>P` sub-formulas (promises).
///
/// # Intended usage
///
/// To check whether a system violates property `P`:
/// ```text
/// let neg = P.negate();           // ~P
/// let aut = ltl_to_buchi(&neg);   // Buchi for ~P
/// // Build product of system x aut; find accepting cycle => violation.
/// ```
///
/// Note: the caller typically passes the *negated* property so that an
/// accepting run of the automaton witnesses a violation.
#[must_use]
pub(crate) fn ltl_to_buchi(formula: &LtlFormula) -> LtlAutomaton {
    // Step 1: ensure PNF
    let pnf = if formula.is_pnf() {
        formula.clone()
    } else {
        formula.negate().negate() // double-negate forces PNF
    };

    // Step 2: expand into obligation nodes
    let mut builder = AutomatonBuilder::default();
    builder.expand(&pnf);
    builder.build()
}

/// Internal node during GPVW expansion.
#[derive(Debug, Clone)]
struct GpvwNode {
    /// Current-state obligations (atoms and their required polarity).
    current: Vec<(u32, bool)>,
    /// Next-state obligations (sub-formulas that must hold in successors).
    next: Vec<LtlFormula>,
    /// Promise obligations: indices into the builder's promise list.
    /// A node fulfills promise `i` if `promise_body[i]` is in `current`
    /// with the right polarity, or the `<>` wrapper is absent.
    fulfilled_promises: FxHashSet<usize>,
}

#[derive(Default)]
struct AutomatonBuilder {
    /// Fully expanded nodes (each becomes an automaton state).
    nodes: Vec<GpvwNode>,
    /// `<>P` sub-formulas extracted from the input.  Index = promise id.
    promises: Vec<LtlFormula>,
    /// De-duplication: canonical key -> node index.
    node_index: FxHashMap<Vec<(u32, bool)>, Vec<usize>>,
}

impl AutomatonBuilder {
    /// Top-level expansion entry point.
    fn expand(&mut self, formula: &LtlFormula) {
        // Collect promises (<> sub-formulas).
        self.collect_promises(formula);

        // Seed expansion with the formula as sole obligation.
        let init = GpvwNode {
            current: Vec::new(),
            next: Vec::new(),
            fulfilled_promises: FxHashSet::default(),
        };
        self.expand_node(init, &[formula.clone()]);
    }

    /// Recursively expand a node with remaining obligations.
    fn expand_node(&mut self, mut node: GpvwNode, obligations: &[LtlFormula]) {
        if obligations.is_empty() {
            // All obligations processed — register as a completed node.
            self.register_node(node);
            return;
        }

        let (head, rest) = obligations.split_first().expect("non-empty obligations");
        match head {
            LtlFormula::Bool(true) => {
                // TRUE is trivially satisfied; continue with rest.
                self.expand_node(node, rest);
            }
            LtlFormula::Bool(false) => {
                // FALSE kills this branch.
            }
            LtlFormula::Atom(tag) => {
                // Check for contradiction with existing current obligations.
                if node.current.iter().any(|(t, v)| *t == *tag && !v) {
                    return; // Contradiction: atom required true but already false.
                }
                if !node.current.iter().any(|(t, _)| *t == *tag) {
                    node.current.push((*tag, true));
                }
                // Check promise fulfillment.
                self.check_promise_fulfillment(&mut node, *tag, true);
                self.expand_node(node, rest);
            }
            LtlFormula::Not(inner) => match &**inner {
                LtlFormula::Atom(tag) => {
                    if node.current.iter().any(|(t, v)| *t == *tag && *v) {
                        return; // Contradiction.
                    }
                    if !node.current.iter().any(|(t, _)| *t == *tag) {
                        node.current.push((*tag, false));
                    }
                    self.check_promise_fulfillment(&mut node, *tag, false);
                    self.expand_node(node, rest);
                }
                LtlFormula::Bool(b) => {
                    // ~TRUE = FALSE, ~FALSE = TRUE
                    let synth = LtlFormula::Bool(!b);
                    let mut new_obs: Vec<LtlFormula> = vec![synth];
                    new_obs.extend_from_slice(rest);
                    self.expand_node(node, &new_obs);
                }
                _ => {
                    // Should not happen in PNF; negate and retry.
                    let negated = inner.negate();
                    let mut new_obs: Vec<LtlFormula> = vec![negated];
                    new_obs.extend_from_slice(rest);
                    self.expand_node(node, &new_obs);
                }
            },
            LtlFormula::And(conjuncts) => {
                // Alpha expansion: add all conjuncts as obligations.
                let mut new_obs: Vec<LtlFormula> = conjuncts.clone();
                new_obs.extend_from_slice(rest);
                self.expand_node(node, &new_obs);
            }
            LtlFormula::Or(disjuncts) => {
                // Beta expansion: branch on each disjunct.
                for disjunct in disjuncts {
                    let mut new_obs: Vec<LtlFormula> = vec![disjunct.clone()];
                    new_obs.extend_from_slice(rest);
                    self.expand_node(node.clone(), &new_obs);
                }
            }
            LtlFormula::Always(inner) => {
                // []P = P /\ X([]P)
                // Current obligation: P
                // Next obligation:    []P
                let mut new_obs: Vec<LtlFormula> = vec![(**inner).clone()];
                new_obs.extend_from_slice(rest);
                let mut node_clone = node;
                node_clone.next.push(head.clone());
                self.expand_node(node_clone, &new_obs);
            }
            LtlFormula::Eventually(inner) => {
                // <>P = P \/ X(<>P)
                // Beta expansion: either P holds now, or defer to next.

                // Branch 1: P holds now
                {
                    let mut new_obs: Vec<LtlFormula> = vec![(**inner).clone()];
                    new_obs.extend_from_slice(rest);
                    self.expand_node(node.clone(), &new_obs);
                }

                // Branch 2: defer — X(<>P)
                {
                    let mut deferred_node = node;
                    deferred_node.next.push(head.clone());
                    self.expand_node(deferred_node, rest);
                }
            }
        }
    }

    /// Register a fully-expanded node, deduplicating by current obligations.
    fn register_node(&mut self, node: GpvwNode) {
        let mut key = node.current.clone();
        key.sort();
        let nodes_with_key = self.node_index.entry(key).or_default();

        // Check if an equivalent node already exists.
        for &existing_idx in nodes_with_key.iter() {
            let existing = &self.nodes[existing_idx];
            if equivalent_next(&existing.next, &node.next) {
                // Merge promise fulfillment.
                let merged: FxHashSet<usize> = existing
                    .fulfilled_promises
                    .union(&node.fulfilled_promises)
                    .copied()
                    .collect();
                self.nodes[existing_idx].fulfilled_promises = merged;
                return;
            }
        }

        let idx = self.nodes.len();
        let mut key = node.current.clone();
        key.sort();
        self.node_index.entry(key).or_default().push(idx);
        self.nodes.push(node);
    }

    /// Collect `<>P` sub-formulas as promises.
    fn collect_promises(&mut self, formula: &LtlFormula) {
        match formula {
            LtlFormula::Eventually(inner) => {
                self.promises.push((**inner).clone());
                self.collect_promises(inner);
            }
            LtlFormula::Always(inner) => self.collect_promises(inner),
            LtlFormula::And(cs) => {
                for c in cs {
                    self.collect_promises(c);
                }
            }
            LtlFormula::Or(ds) => {
                for d in ds {
                    self.collect_promises(d);
                }
            }
            LtlFormula::Not(inner) => self.collect_promises(inner),
            LtlFormula::Bool(_) | LtlFormula::Atom(_) => {}
        }
    }

    /// Check whether the given atom assignment fulfills any promises.
    fn check_promise_fulfillment(&self, node: &mut GpvwNode, tag: u32, value: bool) {
        for (i, promise_body) in self.promises.iter().enumerate() {
            if let LtlFormula::Atom(ptag) = promise_body {
                if *ptag == tag && value {
                    node.fulfilled_promises.insert(i);
                }
            }
        }
    }

    /// Build the final [`LtlAutomaton`] from expanded nodes.
    fn build(self) -> LtlAutomaton {
        let state_count = self.nodes.len().max(1);

        // All nodes are initial (GPVW convention: the expansion starts from
        // the formula itself, so every node is reachable from an initial
        // configuration).
        let initial_states: Vec<AutomatonStateId> = (0..self.nodes.len()).collect();

        // Build transitions: for each node, compute successor states by
        // re-expanding the `next` obligations.
        let mut transitions: FxHashMap<AutomatonStateId, Vec<BuchiTransition>> =
            FxHashMap::default();

        for (src_idx, node) in self.nodes.iter().enumerate() {
            if node.next.is_empty() {
                // Self-loop with same guard (stuttering).
                transitions
                    .entry(src_idx)
                    .or_default()
                    .push(BuchiTransition {
                        target: src_idx,
                        guard: node.current.clone(),
                    });
            } else {
                // Successor states are nodes whose current obligations are
                // consistent with this node's next obligations.
                for (tgt_idx, tgt_node) in self.nodes.iter().enumerate() {
                    if self.next_consistent(&node.next, tgt_node) {
                        transitions
                            .entry(src_idx)
                            .or_default()
                            .push(BuchiTransition {
                                target: tgt_idx,
                                guard: tgt_node.current.clone(),
                            });
                    }
                }
            }
        }

        // Build accepting sets from promises.
        let accepting_sets = if self.promises.is_empty() {
            // No promises: every state is accepting (trivial acceptance).
            let all: FxHashSet<AutomatonStateId> = (0..self.nodes.len()).collect();
            vec![all]
        } else {
            self.promises
                .iter()
                .enumerate()
                .map(|(promise_idx, _)| {
                    self.nodes
                        .iter()
                        .enumerate()
                        .filter(|(_, n)| n.fulfilled_promises.contains(&promise_idx))
                        .map(|(idx, _)| idx)
                        .collect()
                })
                .collect()
        };

        LtlAutomaton {
            state_count,
            initial_states,
            transitions,
            accepting_sets,
        }
    }

    /// Check whether a target node's current obligations are consistent
    /// with a source node's next-state obligations.
    fn next_consistent(&self, next_obligations: &[LtlFormula], target: &GpvwNode) -> bool {
        for obligation in next_obligations {
            if !self.target_satisfies(obligation, target) {
                return false;
            }
        }
        true
    }

    /// Check whether a target node satisfies a single obligation.
    fn target_satisfies(&self, obligation: &LtlFormula, target: &GpvwNode) -> bool {
        match obligation {
            LtlFormula::Bool(b) => *b,
            LtlFormula::Atom(tag) => target.current.iter().any(|(t, v)| *t == *tag && *v),
            LtlFormula::Not(inner) => match &**inner {
                LtlFormula::Atom(tag) => target.current.iter().any(|(t, v)| *t == *tag && !v),
                _ => true, // Conservative: non-atomic negation is assumed satisfiable.
            },
            LtlFormula::And(cs) => cs.iter().all(|c| self.target_satisfies(c, target)),
            LtlFormula::Or(ds) => ds.iter().any(|d| self.target_satisfies(d, target)),
            LtlFormula::Always(_) | LtlFormula::Eventually(_) => {
                // Temporal obligations are carried in `target.next`; check that
                // the target's next obligations include this formula.
                target.next.iter().any(|n| n == obligation)
            }
        }
    }
}

/// Check structural equivalence of two next-obligation lists (order-independent).
fn equivalent_next(a: &[LtlFormula], b: &[LtlFormula]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    a.iter().all(|af| b.contains(af)) && b.iter().all(|bf| a.contains(bf))
}

// ---------------------------------------------------------------------------
// Product State
// ---------------------------------------------------------------------------

/// A state in the product of the system state graph and the Buchi automaton.
///
/// Each product state pairs a system state fingerprint with a Buchi automaton
/// state id.  The product graph is explored during BFS: for each system
/// transition `s -> s'`, and each automaton transition `q -[guard]-> q'` whose
/// guard is satisfied by `s'`, a product edge `(s,q) -> (s',q')` is added.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ProductState {
    /// Fingerprint of the system (TLA+) state.
    pub(crate) system_fp: Fingerprint,
    /// Buchi automaton state index.
    pub(crate) automaton_state: AutomatonStateId,
}

impl ProductState {
    /// Create a new product state.
    #[must_use]
    pub(crate) fn new(system_fp: Fingerprint, automaton_state: AutomatonStateId) -> Self {
        Self {
            system_fp,
            automaton_state,
        }
    }
}

// ---------------------------------------------------------------------------
// Accepting Cycle Detection
// ---------------------------------------------------------------------------

/// Check whether the product graph contains an accepting cycle.
///
/// An accepting cycle is a non-trivial SCC (strongly connected component)
/// in which every accepting set of the Buchi automaton is represented.
///
/// # Arguments
///
/// * `product_states` — All product states discovered so far.
/// * `successors` — Adjacency list: `product_state -> [successor product states]`.
/// * `automaton` — The Buchi automaton (needed to query accepting sets).
/// * `system_states` — Map from fingerprint to concrete system state
///   (used to reconstruct the counterexample [`Trace`]).
///
/// # Returns
///
/// `Some(Trace)` containing a counterexample trace if an accepting cycle is
/// found, or `None` if the product graph is cycle-free (or all cycles fail
/// the acceptance condition).
#[must_use]
pub(crate) fn check_product_accepting_cycle(
    product_states: &[ProductState],
    successors: &FxHashMap<ProductState, Vec<ProductState>>,
    automaton: &LtlAutomaton,
    system_states: &FxHashMap<Fingerprint, State>,
) -> Option<Trace> {
    let sccs = find_product_sccs(product_states, successors);

    for scc in &sccs {
        if scc.len() < 2 && !has_self_loop(&scc[0], successors) {
            continue; // Trivial SCC without self-loop.
        }

        if is_product_accepting_scc(scc, automaton) {
            return extract_counterexample(scc, successors, system_states);
        }
    }

    None
}

/// Check whether a single-node SCC has a self-loop.
fn has_self_loop(
    node: &ProductState,
    successors: &FxHashMap<ProductState, Vec<ProductState>>,
) -> bool {
    successors
        .get(node)
        .is_some_and(|succs| succs.contains(node))
}

/// Check whether an SCC is accepting under generalized Buchi acceptance.
///
/// An SCC is accepting iff for *every* accepting set in the automaton,
/// at least one node in the SCC has its automaton state in that set.
fn is_product_accepting_scc(scc: &[ProductState], automaton: &LtlAutomaton) -> bool {
    for accepting_set in &automaton.accepting_sets {
        let fulfilled = scc
            .iter()
            .any(|ps| accepting_set.contains(&ps.automaton_state));
        if !fulfilled {
            return false;
        }
    }
    true
}

/// Find all SCCs in the product graph using iterative Tarjan's algorithm.
fn find_product_sccs(
    product_states: &[ProductState],
    successors: &FxHashMap<ProductState, Vec<ProductState>>,
) -> Vec<Vec<ProductState>> {
    let mut index_counter: usize = 0;
    let mut stack: Vec<ProductState> = Vec::new();
    let mut on_stack: FxHashSet<ProductState> = FxHashSet::default();
    let mut indices: FxHashMap<ProductState, usize> = FxHashMap::default();
    let mut lowlinks: FxHashMap<ProductState, usize> = FxHashMap::default();
    let mut result: Vec<Vec<ProductState>> = Vec::new();

    for &start_node in product_states {
        if indices.contains_key(&start_node) {
            continue;
        }

        let mut work_stack: Vec<(ProductState, usize)> = vec![(start_node, 0)];
        while let Some((node, succ_pos)) = work_stack.last_mut() {
            let node = *node;

            if *succ_pos == 0 && !indices.contains_key(&node) {
                indices.insert(node, index_counter);
                lowlinks.insert(node, index_counter);
                index_counter += 1;
                stack.push(node);
                on_stack.insert(node);
            }

            let succs = successors.get(&node);
            let succ_count = succs.map_or(0, |s| s.len());

            if *succ_pos < succ_count {
                let succ = succs.expect("succ_count > 0")[*succ_pos];
                *succ_pos += 1;

                if !indices.contains_key(&succ) {
                    work_stack.push((succ, 0));
                } else if on_stack.contains(&succ) {
                    let succ_index = indices[&succ];
                    let node_lowlink = lowlinks.get_mut(&node).expect("node has lowlink");
                    if succ_index < *node_lowlink {
                        *node_lowlink = succ_index;
                    }
                }
            } else {
                let node_index = indices[&node];
                let node_lowlink = lowlinks[&node];

                if node_lowlink == node_index {
                    let mut scc = Vec::new();
                    loop {
                        let w = stack.pop().expect("stack should not be empty");
                        on_stack.remove(&w);
                        scc.push(w);
                        if w == node {
                            break;
                        }
                    }
                    result.push(scc);
                }

                work_stack.pop();
                if let Some((parent, _)) = work_stack.last() {
                    let parent = *parent;
                    let parent_lowlink = lowlinks.get_mut(&parent).expect("parent has lowlink");
                    if node_lowlink < *parent_lowlink {
                        *parent_lowlink = node_lowlink;
                    }
                }
            }
        }
    }

    result
}

/// Extract a counterexample [`Trace`] from an accepting SCC.
///
/// Finds a cycle within the SCC via DFS and maps each product state's
/// system fingerprint back to the concrete [`State`] to build the trace.
fn extract_counterexample(
    scc: &[ProductState],
    successors: &FxHashMap<ProductState, Vec<ProductState>>,
    system_states: &FxHashMap<Fingerprint, State>,
) -> Option<Trace> {
    if scc.is_empty() {
        return None;
    }

    let cycle = find_cycle_in_scc(scc, successors);
    if cycle.is_empty() {
        return None;
    }

    let states: Vec<State> = cycle
        .iter()
        .filter_map(|ps| system_states.get(&ps.system_fp).cloned())
        .collect();

    if states.is_empty() {
        return None;
    }

    Some(Trace::from_states(states))
}

/// Find a cycle within an SCC using DFS.
///
/// Returns a path `[n0, n1, ..., nk, n0]` where the first and last
/// elements are the same, forming a closed cycle.
fn find_cycle_in_scc(
    scc: &[ProductState],
    successors: &FxHashMap<ProductState, Vec<ProductState>>,
) -> Vec<ProductState> {
    if scc.is_empty() {
        return Vec::new();
    }

    let start = scc[0];
    let scc_set: FxHashSet<ProductState> = scc.iter().copied().collect();
    let mut visited: FxHashSet<ProductState> = FxHashSet::default();
    let mut path: Vec<ProductState> = Vec::new();

    if dfs_find_cycle(start, &scc_set, successors, &mut visited, &mut path) {
        path
    } else {
        // Fallback: return the SCC nodes with a back-edge.
        let mut cycle = scc.to_vec();
        cycle.push(start);
        cycle
    }
}

/// DFS helper to find a cycle back to the start node.
fn dfs_find_cycle(
    node: ProductState,
    scc_set: &FxHashSet<ProductState>,
    successors: &FxHashMap<ProductState, Vec<ProductState>>,
    visited: &mut FxHashSet<ProductState>,
    path: &mut Vec<ProductState>,
) -> bool {
    path.push(node);
    visited.insert(node);

    if let Some(succs) = successors.get(&node) {
        for &succ in succs {
            if !scc_set.contains(&succ) {
                continue;
            }
            if !path.is_empty() && succ == path[0] {
                path.push(succ);
                return true;
            }
            if !visited.contains(&succ) && dfs_find_cycle(succ, scc_set, successors, visited, path)
            {
                return true;
            }
        }
    }

    path.pop();
    false
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- LtlFormula tests --

    #[test]
    fn test_ltl_formula_negate_bool() {
        assert_eq!(LtlFormula::Bool(true).negate(), LtlFormula::Bool(false));
        assert_eq!(LtlFormula::Bool(false).negate(), LtlFormula::Bool(true));
    }

    #[test]
    fn test_ltl_formula_negate_atom_produces_not() {
        let atom = LtlFormula::Atom(42);
        let negated = atom.negate();
        assert_eq!(negated, LtlFormula::Not(Box::new(LtlFormula::Atom(42))));
    }

    #[test]
    fn test_ltl_formula_double_negation_cancels() {
        let atom = LtlFormula::Atom(1);
        let double_neg = atom.negate().negate();
        assert_eq!(double_neg, LtlFormula::Atom(1));
    }

    #[test]
    fn test_ltl_formula_negate_always_produces_eventually() {
        let always_p = LtlFormula::Always(Box::new(LtlFormula::Atom(1)));
        let negated = always_p.negate();
        // ~[]P = <>~P
        assert_eq!(
            negated,
            LtlFormula::Eventually(Box::new(LtlFormula::Not(Box::new(LtlFormula::Atom(1)))))
        );
    }

    #[test]
    fn test_ltl_formula_negate_eventually_produces_always() {
        let ev_p = LtlFormula::Eventually(Box::new(LtlFormula::Atom(1)));
        let negated = ev_p.negate();
        // ~<>P = []~P
        assert_eq!(
            negated,
            LtlFormula::Always(Box::new(LtlFormula::Not(Box::new(LtlFormula::Atom(1)))))
        );
    }

    #[test]
    fn test_ltl_formula_negate_conjunction_produces_disjunction() {
        let conj = LtlFormula::And(vec![LtlFormula::Atom(1), LtlFormula::Atom(2)]);
        let negated = conj.negate();
        assert_eq!(
            negated,
            LtlFormula::Or(vec![
                LtlFormula::Not(Box::new(LtlFormula::Atom(1))),
                LtlFormula::Not(Box::new(LtlFormula::Atom(2))),
            ])
        );
    }

    #[test]
    fn test_ltl_formula_is_pnf_atoms() {
        assert!(LtlFormula::Bool(true).is_pnf());
        assert!(LtlFormula::Atom(1).is_pnf());
        assert!(LtlFormula::Not(Box::new(LtlFormula::Atom(1))).is_pnf());
        // Not(Always(...)) is NOT in PNF
        assert!(
            !LtlFormula::Not(Box::new(LtlFormula::Always(Box::new(LtlFormula::Atom(1))))).is_pnf()
        );
    }

    // -- LtlAutomaton construction tests --

    #[test]
    fn test_ltl_to_buchi_true_produces_single_state() {
        let aut = ltl_to_buchi(&LtlFormula::Bool(true));
        assert!(aut.state_count >= 1);
        assert!(!aut.initial_states.is_empty());
    }

    #[test]
    fn test_ltl_to_buchi_false_produces_empty_automaton() {
        let aut = ltl_to_buchi(&LtlFormula::Bool(false));
        // FALSE should produce no reachable accepting states.
        assert!(aut.initial_states.is_empty() || aut.accepting_sets.iter().all(|s| s.is_empty()));
    }

    #[test]
    fn test_ltl_to_buchi_atom_produces_non_empty_automaton() {
        let aut = ltl_to_buchi(&LtlFormula::Atom(1));
        assert!(!aut.initial_states.is_empty());
        assert!(aut.state_count >= 1);
    }

    #[test]
    fn test_ltl_to_buchi_eventually_has_promise() {
        let ev_p = LtlFormula::Eventually(Box::new(LtlFormula::Atom(1)));
        let aut = ltl_to_buchi(&ev_p);
        // <>P should produce at least one accepting set (the promise for P).
        assert!(!aut.accepting_sets.is_empty());
    }

    #[test]
    fn test_ltl_to_buchi_always_eventually_structure() {
        // []<>P — infinitely often P
        let formula = LtlFormula::Always(Box::new(LtlFormula::Eventually(Box::new(
            LtlFormula::Atom(1),
        ))));
        let aut = ltl_to_buchi(&formula);
        assert!(aut.state_count >= 1);
        assert!(!aut.initial_states.is_empty());
    }

    #[test]
    fn test_ltl_to_buchi_eventually_always_structure() {
        // <>[]P — stability: eventually P holds forever
        let formula =
            LtlFormula::Eventually(Box::new(LtlFormula::Always(Box::new(LtlFormula::Atom(1)))));
        let aut = ltl_to_buchi(&formula);
        assert!(aut.state_count >= 1);
        assert!(!aut.initial_states.is_empty());
    }

    // -- LtlAutomaton API tests --

    #[test]
    fn test_automaton_transitions_from_empty() {
        let aut = LtlAutomaton {
            state_count: 1,
            initial_states: vec![0],
            transitions: FxHashMap::default(),
            accepting_sets: vec![],
        };
        assert!(aut.transitions_from(0).is_empty());
        assert!(aut.transitions_from(99).is_empty());
    }

    #[test]
    fn test_automaton_is_accepting_with_single_set() {
        let mut acc_set = FxHashSet::default();
        acc_set.insert(0);
        let aut = LtlAutomaton {
            state_count: 2,
            initial_states: vec![0],
            transitions: FxHashMap::default(),
            accepting_sets: vec![acc_set],
        };
        assert!(aut.is_accepting(0));
        assert!(!aut.is_accepting(1));
    }

    #[test]
    fn test_automaton_is_accepting_with_multiple_sets() {
        let mut set1 = FxHashSet::default();
        set1.insert(0);
        set1.insert(1);
        let mut set2 = FxHashSet::default();
        set2.insert(1);
        let aut = LtlAutomaton {
            state_count: 2,
            initial_states: vec![0],
            transitions: FxHashMap::default(),
            accepting_sets: vec![set1, set2],
        };
        // State 0 is in set1 but not set2 -> not accepting (needs all sets).
        assert!(!aut.is_accepting(0));
        // State 1 is in both sets -> accepting.
        assert!(aut.is_accepting(1));
    }

    // -- ProductState tests --

    #[test]
    fn test_product_state_equality() {
        let ps1 = ProductState::new(Fingerprint(100), 0);
        let ps2 = ProductState::new(Fingerprint(100), 0);
        let ps3 = ProductState::new(Fingerprint(100), 1);
        let ps4 = ProductState::new(Fingerprint(200), 0);

        assert_eq!(ps1, ps2);
        assert_ne!(ps1, ps3);
        assert_ne!(ps1, ps4);
    }

    // -- Accepting cycle detection tests --

    #[test]
    fn test_check_product_accepting_cycle_empty_graph() {
        let all_accepting: FxHashSet<AutomatonStateId> = [0].into_iter().collect();
        let aut = LtlAutomaton {
            state_count: 1,
            initial_states: vec![0],
            transitions: FxHashMap::default(),
            accepting_sets: vec![all_accepting],
        };

        let result =
            check_product_accepting_cycle(&[], &FxHashMap::default(), &aut, &FxHashMap::default());
        assert!(result.is_none());
    }

    #[test]
    fn test_check_product_accepting_cycle_self_loop() {
        let ps = ProductState::new(Fingerprint(1), 0);
        let mut successors: FxHashMap<ProductState, Vec<ProductState>> = FxHashMap::default();
        successors.insert(ps, vec![ps]);

        let mut acc = FxHashSet::default();
        acc.insert(0_usize);
        let aut = LtlAutomaton {
            state_count: 1,
            initial_states: vec![0],
            transitions: FxHashMap::default(),
            accepting_sets: vec![acc],
        };

        let mut system_states = FxHashMap::default();
        system_states.insert(Fingerprint(1), State::new());

        let result = check_product_accepting_cycle(&[ps], &successors, &aut, &system_states);
        assert!(
            result.is_some(),
            "self-loop on accepting state should be a violation"
        );
    }

    #[test]
    fn test_check_product_accepting_cycle_two_node_cycle() {
        let a = ProductState::new(Fingerprint(1), 0);
        let b = ProductState::new(Fingerprint(2), 0);

        let mut successors: FxHashMap<ProductState, Vec<ProductState>> = FxHashMap::default();
        successors.insert(a, vec![b]);
        successors.insert(b, vec![a]);

        let mut acc = FxHashSet::default();
        acc.insert(0_usize);
        let aut = LtlAutomaton {
            state_count: 1,
            initial_states: vec![0],
            transitions: FxHashMap::default(),
            accepting_sets: vec![acc],
        };

        let mut system_states = FxHashMap::default();
        system_states.insert(Fingerprint(1), State::new());
        system_states.insert(Fingerprint(2), State::new());

        let result = check_product_accepting_cycle(&[a, b], &successors, &aut, &system_states);
        assert!(
            result.is_some(),
            "two-node cycle through accepting state should be detected"
        );
    }

    #[test]
    fn test_check_product_accepting_cycle_chain_no_cycle() {
        let a = ProductState::new(Fingerprint(1), 0);
        let b = ProductState::new(Fingerprint(2), 0);
        let c = ProductState::new(Fingerprint(3), 0);

        let mut successors: FxHashMap<ProductState, Vec<ProductState>> = FxHashMap::default();
        successors.insert(a, vec![b]);
        successors.insert(b, vec![c]);
        // No back-edge.

        let mut acc = FxHashSet::default();
        acc.insert(0_usize);
        let aut = LtlAutomaton {
            state_count: 1,
            initial_states: vec![0],
            transitions: FxHashMap::default(),
            accepting_sets: vec![acc],
        };

        let result =
            check_product_accepting_cycle(&[a, b, c], &successors, &aut, &FxHashMap::default());
        assert!(
            result.is_none(),
            "chain without back-edge should have no cycle"
        );
    }

    #[test]
    fn test_check_product_accepting_cycle_non_accepting_scc() {
        // Cycle exists but automaton state is NOT in accepting set.
        let a = ProductState::new(Fingerprint(1), 0);
        let b = ProductState::new(Fingerprint(2), 0);

        let mut successors: FxHashMap<ProductState, Vec<ProductState>> = FxHashMap::default();
        successors.insert(a, vec![b]);
        successors.insert(b, vec![a]);

        // Accepting set only contains state 1 (not 0).
        let mut acc = FxHashSet::default();
        acc.insert(1_usize);
        let aut = LtlAutomaton {
            state_count: 2,
            initial_states: vec![0],
            transitions: FxHashMap::default(),
            accepting_sets: vec![acc],
        };

        let result =
            check_product_accepting_cycle(&[a, b], &successors, &aut, &FxHashMap::default());
        assert!(
            result.is_none(),
            "cycle through non-accepting states should not be a violation"
        );
    }

    #[test]
    fn test_check_product_accepting_cycle_generalized_buchi() {
        // Two accepting sets; cycle must visit both.
        let a = ProductState::new(Fingerprint(1), 0);
        let b = ProductState::new(Fingerprint(2), 1);

        let mut successors: FxHashMap<ProductState, Vec<ProductState>> = FxHashMap::default();
        successors.insert(a, vec![b]);
        successors.insert(b, vec![a]);

        let mut set1 = FxHashSet::default();
        set1.insert(0_usize);
        let mut set2 = FxHashSet::default();
        set2.insert(1_usize);

        let aut = LtlAutomaton {
            state_count: 2,
            initial_states: vec![0, 1],
            transitions: FxHashMap::default(),
            accepting_sets: vec![set1, set2],
        };

        let mut system_states = FxHashMap::default();
        system_states.insert(Fingerprint(1), State::new());
        system_states.insert(Fingerprint(2), State::new());

        let result = check_product_accepting_cycle(&[a, b], &successors, &aut, &system_states);
        assert!(
            result.is_some(),
            "cycle visiting both accepting sets should be detected"
        );
    }

    #[test]
    fn test_check_product_accepting_cycle_generalized_buchi_one_set_missing() {
        // Two accepting sets; cycle only covers set 1, not set 2.
        let a = ProductState::new(Fingerprint(1), 0);
        let b = ProductState::new(Fingerprint(2), 0);

        let mut successors: FxHashMap<ProductState, Vec<ProductState>> = FxHashMap::default();
        successors.insert(a, vec![b]);
        successors.insert(b, vec![a]);

        let mut set1 = FxHashSet::default();
        set1.insert(0_usize);
        let mut set2 = FxHashSet::default();
        set2.insert(1_usize); // automaton state 1 is not in the cycle

        let aut = LtlAutomaton {
            state_count: 2,
            initial_states: vec![0],
            transitions: FxHashMap::default(),
            accepting_sets: vec![set1, set2],
        };

        let result =
            check_product_accepting_cycle(&[a, b], &successors, &aut, &FxHashMap::default());
        assert!(
            result.is_none(),
            "cycle covering only one of two accepting sets should not be a violation"
        );
    }
}
