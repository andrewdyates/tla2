// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT solver extension trait for DPLL(T) integration
//!
//! This module provides the `Extension` trait which allows external theory
//! solvers to integrate with the SAT solver for DPLL(T) style solving.
//!
//! The extension is called at key points during SAT solving:
//! - After propagation (to check for theory propagations)
//! - When a literal is assigned (to update theory state)
//! - After finding a complete model (for final theory check)
//!
//! Based on Z3's sat_extension.h design.
//!
//! # Clause-Based vs Justification-Based Propagation
//!
//! This implementation uses clause-based propagation where theory lemmas are
//! converted to explicit SAT clauses. This is simpler than justification-based
//! propagation (like Z3 uses internally) but requires more clauses.
//!
//! For example, if the theory knows `a=b ∧ b=c → a=c`, it adds the clause
//! `(¬(a=b) ∨ ¬(b=c) ∨ (a=c))` to the SAT solver.

use crate::{Literal, Variable};

/// Result of extension's final check
#[derive(Debug)]
#[non_exhaustive]
pub enum ExtCheckResult {
    /// Theory accepts the model
    Sat,
    /// Theory found a conflict - the clause blocks the current assignment
    Conflict(Vec<Literal>),
    /// Theory could not determine (may need more propagation)
    Unknown,
    /// Theory needs these clauses added, then SAT should continue solving.
    ///
    /// Used for array theory lemmas (#6546): instead of returning to the
    /// outer split loop (which recreates the theory and re-solves from
    /// scratch), add the lemma clauses and continue within the same SAT
    /// invocation. This eliminates O(N) full SAT-solve round-trips.
    AddClauses(Vec<Vec<Literal>>),
}

/// Result of extension's unit propagation
#[derive(Debug, Default)]
#[non_exhaustive]
pub struct ExtPropagateResult {
    /// Clauses to add to the SAT solver (theory lemmas)
    ///
    /// Each clause is a disjunction. If the clause has one satisfied literal
    /// or one unassigned literal with all others false, SAT will propagate.
    pub clauses: Vec<Vec<Literal>>,

    /// Lightweight theory propagations (#4919).
    ///
    /// Each entry is `(reason_clause, propagated_literal)` where:
    /// - `reason_clause` contains the full clause `[propagated_lit, ¬r₁, ¬r₂, ...]`
    ///   with the propagated literal as the FIRST element
    /// - `propagated_literal` is the literal to enqueue on the trail
    ///
    /// Unlike `clauses`, these skip watch-list attachment and VSIDS bumping.
    /// The clause is stored in the arena only as a reason for conflict analysis.
    /// This matches Z3's `ctx().assign()` pattern where theory propagations
    /// go directly to the trail without creating watched clauses.
    pub propagations: Vec<(Vec<Literal>, Literal)>,

    /// Conflict clause if theory detected a conflict
    ///
    /// If set, all literals in this clause must be false under the current
    /// assignment, indicating the assignment is theory-inconsistent.
    pub conflict: Option<Vec<Literal>>,

    /// Request the SAT solver to stop immediately and return Unknown.
    ///
    /// Used when the theory needs to hand control back to an outer split
    /// loop (e.g., for expression splits or disequality splits). Without
    /// this, the SAT solver continues searching and may clear the stored
    /// split request on a subsequent propagation round (#4919).
    pub stop: bool,
}

impl ExtPropagateResult {
    /// Create an empty result (no propagation)
    pub fn none() -> Self {
        Self::default()
    }

    /// Create a result with a single clause to add
    pub fn clause(clause: Vec<Literal>) -> Self {
        Self {
            clauses: vec![clause],
            propagations: vec![],
            conflict: None,
            stop: false,
        }
    }

    /// Create a result with multiple clauses
    pub fn clauses(clauses: Vec<Vec<Literal>>) -> Self {
        Self {
            clauses,
            propagations: vec![],
            conflict: None,
            stop: false,
        }
    }

    /// Create a conflict result
    pub fn conflict(clause: Vec<Literal>) -> Self {
        Self {
            clauses: vec![],
            propagations: vec![],
            conflict: Some(clause),
            stop: false,
        }
    }

    /// Create a result with all fields specified.
    pub fn new(
        clauses: Vec<Vec<Literal>>,
        propagations: Vec<(Vec<Literal>, Literal)>,
        conflict: Option<Vec<Literal>>,
        stop: bool,
    ) -> Self {
        Self {
            clauses,
            propagations,
            conflict,
            stop,
        }
    }

    /// Set the `stop` flag on this result (builder pattern).
    pub fn with_stop(mut self, stop: bool) -> Self {
        self.stop = stop;
        self
    }
}

/// Extension instance prepared during the SAT solver's preprocessing phase.
///
/// This allows a downstream crate to:
/// 1. inspect a snapshot of the current irredundant clause set,
/// 2. decide which clauses are consumed by a theory-specific extractor, and
/// 3. freeze theory-tracked variables before SAT preprocessing continues.
///
/// The consumed clause positions refer to the exact clause snapshot passed to
/// the builder callback.
pub struct PreparedExtension<E> {
    /// The extension to activate once SAT preprocessing finishes.
    pub extension: E,
    /// Positions in the builder's clause snapshot that should be removed from
    /// the SAT clause database because the extension now owns them.
    pub consumed_clause_positions: Vec<usize>,
    /// Variables that must be frozen before destructive SAT preprocessing
    /// continues (for example, to keep BVE from eliminating XOR-tracked vars).
    pub frozen_variables: Vec<Variable>,
}

impl<E> PreparedExtension<E> {
    /// Create a prepared extension and canonicalize its metadata.
    pub fn new(
        extension: E,
        mut consumed_clause_positions: Vec<usize>,
        mut frozen_variables: Vec<Variable>,
    ) -> Self {
        consumed_clause_positions.sort_unstable();
        consumed_clause_positions.dedup();
        frozen_variables.sort_unstable_by_key(|var| var.index());
        frozen_variables.dedup_by_key(|var| var.index());
        Self {
            extension,
            consumed_clause_positions,
            frozen_variables,
        }
    }
}

/// Read-only context for observing solver state
pub trait SolverContext {
    /// Get the current value of a variable (None if unassigned)
    fn value(&self, var: Variable) -> Option<bool>;

    /// Get the current value of a literal (None if unassigned)
    fn lit_value(&self, lit: Literal) -> Option<bool> {
        self.value(lit.variable())
            .map(|v| if lit.is_positive() { v } else { !v })
    }

    /// Get the current decision level
    fn decision_level(&self) -> u32;

    /// Get the level at which a variable was assigned (None if unassigned)
    fn var_level(&self, var: Variable) -> Option<u32>;

    /// Get all currently assigned literals (the trail)
    fn trail(&self) -> &[Literal];

    /// Get literals assigned since the last extension call
    ///
    /// Returns the slice of trail from `last_trail_pos` to current.
    fn new_assignments(&self, last_trail_pos: usize) -> &[Literal] {
        let trail = self.trail();
        if last_trail_pos < trail.len() {
            &trail[last_trail_pos..]
        } else {
            &[]
        }
    }
}

/// Extension trait for DPLL(T) theory integration
///
/// Implement this trait to add theory reasoning to the SAT solver.
/// The extension is called during key phases of CDCL solving.
///
/// # Implementation Guide
///
/// 1. Track assigned literals via `asserted()` or `new_assignments()`
/// 2. In `propagate()`, check for theory implications and conflicts
/// 3. Return clauses that encode the implications
/// 4. In `check()`, do final consistency check when SAT finds a model
/// 5. In `backtrack()`, undo state for assignments above the level
pub trait Extension {
    /// Called after unit propagation completes to check for theory propagations
    ///
    /// The extension should:
    /// 1. Update its internal state based on new assignments
    /// 2. Check for theory propagations
    /// 3. Return clauses to add to SAT (propagation lemmas)
    ///
    /// Theory lemmas should have the form:
    /// `(¬reason1 ∨ ¬reason2 ∨ ... ∨ conclusion)`
    ///
    /// If all reason literals are true, SAT will propagate the conclusion.
    fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult;

    /// Called when a literal is assigned
    ///
    /// The extension can use this to incrementally update its internal state.
    /// This is called for each literal added to the trail.
    fn asserted(&mut self, _lit: Literal) {
        // Default: do nothing (use propagate() to see new assignments)
    }

    /// Called after SAT finds a complete model for final theory check
    ///
    /// The extension should check if the complete assignment is consistent
    /// with the theory. If not, it returns a conflict clause.
    ///
    /// This is called when all variables are assigned and SAT has no conflict.
    fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
        // Default: accept any model
        ExtCheckResult::Sat
    }

    /// Called when the solver backtracks
    ///
    /// The extension should undo any state changes made above the given level.
    /// `new_level` is the level we're backtracking TO (will keep assignments
    /// at this level and below).
    fn backtrack(&mut self, _new_level: u32) {
        // Default: do nothing
    }

    /// Called at the start of solving
    fn init(&mut self) {
        // Default: do nothing
    }

    /// Check if the extension can make progress
    ///
    /// Returns true if `propagate()` might return new clauses.
    /// Used to avoid calling `propagate()` unnecessarily.
    ///
    /// The context is provided so extensions can check if there are new
    /// SAT assignments since the last `propagate()` call.
    fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
        // Default: always check (suboptimal but safe)
        true
    }

    /// Suggest the next decision literal for the SAT solver.
    ///
    /// Called before the SAT solver picks a decision variable via VSIDS.
    /// If this returns `Some(lit)`, the solver decides `lit` instead of
    /// using its internal heuristic. If `None`, the solver falls back to
    /// its normal decision procedure.
    ///
    /// This enables CP-level search heuristics like:
    /// - **First-fail**: choose the variable with smallest domain
    /// - **Domain/wdeg**: smallest domain weighted by constraint failures
    /// - **Impact**: choose the variable whose assignment most reduces search space
    ///
    /// The returned literal must be unassigned; otherwise the solver ignores it.
    fn suggest_decision(&self, _ctx: &dyn SolverContext) -> Option<Literal> {
        // Default: no suggestion (use SAT solver's VSIDS heuristic)
        None
    }

    /// Suggest the polarity for a theory-relevant variable.
    ///
    /// Called after VSIDS picks a decision variable. If the variable is a
    /// theory atom, the extension can suggest a polarity consistent with
    /// the current theory model (e.g., LP solution for LRA).
    ///
    /// Returns `Some(true)` for positive, `Some(false)` for negative,
    /// or `None` to let the SAT solver use its default phase heuristic.
    ///
    /// Reference: Z3 `theory_lra::get_phase()`, `arith_solver::get_phase()`
    fn suggest_phase(&self, _var: Variable) -> Option<bool> {
        // Default: no suggestion
        None
    }

    /// Ask whether the current restart should be blocked.
    ///
    /// Called when the restart condition triggers. If the extension returns
    /// true, the restart is suppressed (the solver continues searching at
    /// the current decision level). This enables restart blocking strategies
    /// like Audemard & Simon 2012 that preserve near-solution assignments.
    fn should_block_restart(&self, _num_assigned: u32, _total_vars: u32) -> bool {
        false
    }

    /// Called after the solver performs a restart.
    ///
    /// The extension can use this to re-boost theory-relevant variable
    /// activities so they don't sink below conflict-bumped encoding variables
    /// in the VSIDS heap. Without periodic re-boosting, theory atoms get
    /// one initial bump at registration but are quickly overwhelmed by
    /// conflict-driven bumps after ~20 conflicts, causing "bound starvation"
    /// where the DPLL solver stops deciding theory atoms (#7982).
    ///
    /// Returns a list of variables whose VSIDS activity should be bumped.
    fn on_restart(&self) -> Vec<Variable> {
        Vec::new()
    }
}

#[cfg(test)]
#[path = "extension_tests.rs"]
mod tests;
