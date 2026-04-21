// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tableau graph construction for liveness checking
//!
//! This module implements the tableau construction algorithm from
//! Manna & Pnueli's "Temporal Verification of Reactive Systems: Safety"
//! (Chapter 5, pages 405-452).
//!
//! # Overview
//!
//! A tableau is a graph where:
//! - Each node represents a "particle" (set of formulas that must hold)
//! - Edges represent valid transitions (what must hold in successor states)
//! - Initial nodes are particles derived from the formula being checked
//!
//! # Algorithm
//!
//! 1. Start with the formula F (already in positive normal form)
//! 2. Compute the particle closure of {F}
//! 3. For each particle, compute implied successors
//! 4. Build graph edges based on successor particles

use super::live_expr::LiveExpr;
use rustc_hash::FxHashSet;

/// A particle is a maximal consistent set of formulas from the closure
///
/// In the tableau, each particle represents a possible "state" of the
/// formula satisfaction. A behavior satisfies a temporal formula iff
/// there's a path through the tableau whose particles are consistent
/// with the behavior states.
#[derive(Debug, Clone)]
pub(crate) struct Particle {
    /// The formulas in this particle
    formulas: Vec<LiveExpr>,
}

impl Particle {
    /// Create a new particle with a single formula
    pub(crate) fn new(formula: LiveExpr) -> Self {
        Self {
            formulas: vec![formula],
        }
    }

    /// Create a particle from multiple formulas
    pub(crate) fn from_vec(formulas: Vec<LiveExpr>) -> Self {
        Self { formulas }
    }

    /// Check if this particle is empty
    pub(crate) fn is_empty(&self) -> bool {
        self.formulas.is_empty()
    }

    /// Get the formulas in this particle
    pub(crate) fn formulas(&self) -> &[LiveExpr] {
        &self.formulas
    }

    /// Compute the implied successors for this particle
    ///
    /// For each formula in the particle:
    /// - []P implies ()[]P (always P means next state also has always P)
    /// - <>P implies P \/ ()<>P (eventually either now or later)
    /// - ()P implies P must hold in successor
    ///
    /// Returns the set of formulas that must be satisfiable in successors
    pub(crate) fn implied_successors(&self) -> Particle {
        let mut successor_formulas = Vec::new();

        for formula in &self.formulas {
            if let LiveExpr::Next(inner) = formula {
                // ()P means P must hold in successor
                successor_formulas.push((**inner).clone());
            }
        }

        Particle::from_vec(successor_formulas)
    }

    /// Check if this particle contains a formula equivalent to the given one
    fn contains_equivalent(&self, target: &LiveExpr) -> bool {
        self.formulas.iter().any(|f| f.structurally_equal(target))
    }

    /// Check if this particle contains a formula (structural equality).
    pub(crate) fn member(&self, target: &LiveExpr) -> bool {
        self.contains_equivalent(target)
    }

    /// Check if this particle fulfills a promise of the form `<>r`.
    ///
    /// A particle `A` fulfills `<>r` iff either:
    /// - `<>r ∉ A`, or
    /// - `r ∈ A`
    ///
    /// See TLC: `TBPar.isFulfilling`.
    pub(crate) fn is_fulfilling(&self, promise: &LiveExpr) -> bool {
        let LiveExpr::Eventually(body) = promise else {
            return true;
        };

        !self.member(promise) || self.member(body)
    }

    /// Extract state predicates from this particle
    ///
    /// These are the predicates that must be checked against actual states
    /// to determine if a state is consistent with this tableau node.
    pub(crate) fn state_predicates(&self) -> Vec<&LiveExpr> {
        self.formulas
            .iter()
            .filter(|f| {
                matches!(
                    f.level(),
                    super::live_expr::ExprLevel::Constant | super::live_expr::ExprLevel::State
                )
            })
            .collect()
    }

    /// Check structural equality between particles
    pub(crate) fn equals(&self, other: &Particle) -> bool {
        if self.formulas.len() != other.formulas.len() {
            return false;
        }
        // Check all formulas match (order-independent)
        self.formulas
            .iter()
            .all(|f| other.formulas.iter().any(|g| f.structurally_equal(g)))
            && other
                .formulas
                .iter()
                .all(|f| self.formulas.iter().any(|g| f.structurally_equal(g)))
    }
}

/// A node in the tableau graph
#[derive(Debug, Clone)]
pub(crate) struct TableauNode {
    /// The particle (set of formulas) for this node
    particle: Particle,
    /// Indices of successor nodes (FxHashSet for O(1) membership check)
    successors: FxHashSet<usize>,
    /// Index of this node in the tableau
    index: usize,
    /// State predicates extracted from particle for quick checking
    state_preds: Vec<LiveExpr>,
}

impl TableauNode {
    /// Create a new tableau node
    pub(crate) fn new(particle: Particle, index: usize) -> Self {
        let state_preds = particle.state_predicates().into_iter().cloned().collect();
        Self {
            particle,
            successors: FxHashSet::default(),
            index,
            state_preds,
        }
    }

    /// Get the particle
    pub(crate) fn particle(&self) -> &Particle {
        &self.particle
    }

    /// Get successor indices
    pub(crate) fn successors(&self) -> &FxHashSet<usize> {
        &self.successors
    }

    /// Add a successor (O(1) with FxHashSet)
    pub(crate) fn add_successor(&mut self, idx: usize) {
        self.successors.insert(idx);
    }

    /// Get state predicates
    pub(crate) fn state_preds(&self) -> &[LiveExpr] {
        &self.state_preds
    }

    /// Check if this is a self-loop node with empty particle (accepting)
    pub(crate) fn is_accepting(&self) -> bool {
        self.particle.is_empty()
            && self.successors.len() == 1
            && self.successors.contains(&self.index)
    }
}

/// The tableau graph for a temporal formula
#[derive(Debug, Clone)]
pub(crate) struct Tableau {
    /// The original temporal formula
    formula: LiveExpr,
    /// All nodes in the tableau
    nodes: Vec<TableauNode>,
    /// Number of initial nodes (nodes reachable from the formula)
    init_count: usize,
}

impl Tableau {
    /// Construct a tableau from a temporal formula
    ///
    /// The formula should already be in positive normal form.
    pub(crate) fn new(formula: LiveExpr) -> Self {
        // Start with the initial particle containing just the formula
        let init_particle = Particle::new(formula.clone());

        // Compute the particle closure
        let init_particles = particle_closure(init_particle);

        // Create initial nodes
        let mut nodes: Vec<TableauNode> = init_particles
            .into_iter()
            .enumerate()
            .map(|(i, p)| TableauNode::new(p, i))
            .collect();

        let init_count = nodes.len();

        // Build edges: compute successors for each node
        let mut i = 0;
        while i < nodes.len() {
            let implied = nodes[i].particle.implied_successors();
            let successor_particles = particle_closure(implied);

            for succ_particle in successor_particles {
                // Find or create node for this particle
                let succ_idx = find_or_create_node(&mut nodes, succ_particle);
                nodes[i].add_successor(succ_idx);
            }
            i += 1;
        }

        Self {
            formula,
            nodes,
            init_count,
        }
    }

    /// Get the original formula
    pub(crate) fn formula(&self) -> &LiveExpr {
        &self.formula
    }

    /// Get all nodes
    #[cfg(test)]
    pub(crate) fn nodes(&self) -> &[TableauNode] {
        &self.nodes
    }

    /// Get a specific node
    pub(crate) fn node(&self, idx: usize) -> Option<&TableauNode> {
        self.nodes.get(idx)
    }

    /// Get number of initial nodes
    pub(crate) fn init_count(&self) -> usize {
        self.init_count
    }

    /// Get the number of nodes
    pub(crate) fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Check if the tableau is empty
    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
}

/// Find an existing node with matching particle, or create a new one
fn find_or_create_node(nodes: &mut Vec<TableauNode>, particle: Particle) -> usize {
    for (i, node) in nodes.iter().enumerate() {
        if node.particle.equals(&particle) {
            return i;
        }
    }
    let idx = nodes.len();
    nodes.push(TableauNode::new(particle, idx));
    idx
}

/// Compute the particle closure of a particle
///
/// This implements the expansion rules from Manna & Pnueli (p. 452):
/// - α-formulas (conjunctions): both conjuncts must be in particle
/// - β-formulas (disjunctions): at least one disjunct in particle
/// - []P: P and ()[]P
/// - <>P: P or ()<>P
///
/// Returns all maximal consistent particles derived from the input.
fn particle_closure(initial: Particle) -> Vec<Particle> {
    let mut results = Vec::new();
    expand_particle(initial, &mut results);
    results
}

/// Expand a particle using tableau expansion rules
fn expand_particle(particle: Particle, results: &mut Vec<Particle>) {
    // Find first expandable formula
    for formula in &particle.formulas {
        match formula {
            LiveExpr::And(conjuncts) => {
                // α-rule: expand conjunction - add all conjuncts
                // KEEP the original And formula so that <>P membership checks work
                // when P is a conjunction
                let mut new_formulas = particle.formulas.clone();
                // Don't remove - just add the conjuncts that aren't already present
                let mut any_added = false;
                for conjunct in conjuncts {
                    if !particle.member(conjunct) {
                        new_formulas.push(conjunct.clone());
                        any_added = true;
                    }
                }
                if any_added {
                    expand_particle(Particle::from_vec(new_formulas), results);
                    return;
                }
                // All conjuncts already present, continue to next formula
            }

            LiveExpr::Or(disjuncts) => {
                // β-rule: expand disjunction - branch on each disjunct
                // Check if any disjunct is already present - if so, skip expansion
                let mut any_present = false;
                for disjunct in disjuncts {
                    if particle.member(disjunct) {
                        any_present = true;
                        break;
                    }
                }
                if !any_present {
                    // No disjunct present yet - branch on each
                    for disjunct in disjuncts {
                        let mut new_formulas = particle.formulas.clone();
                        new_formulas.push(disjunct.clone());
                        expand_particle(Particle::from_vec(new_formulas), results);
                    }
                    return;
                }
                // Some disjunct already present, continue to next formula
            }

            LiveExpr::Always(inner) => {
                // α-rule: []P expands to P and ()[]P, but keep []P in the particle.
                // (TLC: TBPar.particleClosure alpha expansion)
                let mut new_formulas = particle.formulas.clone();
                let p_now = (**inner).clone();
                let next_always = LiveExpr::next(LiveExpr::always((**inner).clone()));

                let mut changed = false;
                if !particle.member(&p_now) {
                    new_formulas.push(p_now);
                    changed = true;
                }
                if !particle.member(&next_always) {
                    new_formulas.push(next_always);
                    changed = true;
                }

                if changed {
                    expand_particle(Particle::from_vec(new_formulas), results);
                    return;
                }
            }

            LiveExpr::Eventually(inner) => {
                // β-rule: <>P expands to P or ()<>P, but keep <>P in the particle.
                // Only branch when neither alternative is present yet.
                // (TLC: TBPar.particleClosure beta expansion)
                let p_now = (**inner).clone();
                let next_eventually = LiveExpr::next(LiveExpr::eventually((**inner).clone()));

                if !particle.member(&p_now) && !particle.member(&next_eventually) {
                    let mut branch1 = particle.formulas.clone();
                    branch1.push(p_now);
                    expand_particle(Particle::from_vec(branch1), results);

                    let mut branch2 = particle.formulas.clone();
                    branch2.push(next_eventually);
                    expand_particle(Particle::from_vec(branch2), results);
                    return;
                }
            }

            // Atoms and Next don't expand further
            LiveExpr::Bool(_)
            | LiveExpr::StatePred { .. }
            | LiveExpr::ActionPred { .. }
            | LiveExpr::Enabled { .. }
            | LiveExpr::StateChanged { .. }
            | LiveExpr::Not(_)
            | LiveExpr::Next(_) => {}
        }
    }

    // No more expansions possible - check consistency and add to results
    if is_locally_consistent(&particle) && !particle_exists(results, &particle) {
        results.push(particle);
    }
}

/// Check if a particle is locally consistent
///
/// A particle is inconsistent if it contains both P and ~P for some atom P.
fn is_locally_consistent(particle: &Particle) -> bool {
    // Check for TRUE/FALSE contradictions
    let has_true = particle
        .formulas
        .iter()
        .any(|f| matches!(f, LiveExpr::Bool(true)));
    let has_false = particle
        .formulas
        .iter()
        .any(|f| matches!(f, LiveExpr::Bool(false)));
    if has_true && has_false {
        return false;
    }
    if has_false {
        return false; // FALSE is always inconsistent
    }

    // Check for P and ~P contradictions
    for (i, f) in particle.formulas.iter().enumerate() {
        if let LiveExpr::Not(inner) = f {
            for (j, g) in particle.formulas.iter().enumerate() {
                if i != j && inner.structurally_equal(g) {
                    return false;
                }
            }
        }
    }

    true
}

/// Check if an equivalent particle already exists in the list
fn particle_exists(particles: &[Particle], particle: &Particle) -> bool {
    particles.iter().any(|p| p.equals(particle))
}

impl std::fmt::Display for Tableau {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Tableau for: {}", self.formula)?;
        writeln!(f, "Nodes: {} (init: {})", self.nodes.len(), self.init_count)?;
        for node in &self.nodes {
            write!(f, "  Node {}", node.index)?;
            if node.index < self.init_count {
                write!(f, " (init)")?;
            }
            if node.is_accepting() {
                write!(f, " (accepting)")?;
            }
            writeln!(f, ":")?;
            for formula in node.particle.formulas() {
                writeln!(f, "    {}", formula)?;
            }
            writeln!(f, "    -> {:?}", node.successors)?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "tableau_tests.rs"]
mod tests;
