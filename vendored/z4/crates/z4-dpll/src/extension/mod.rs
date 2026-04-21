// Copyright 2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0

//! Eager DPLL(T) theory extension
//!
//! This module provides a wrapper that implements the SAT solver's `Extension`
//! trait using a `TheorySolver`. This enables eager theory propagation during
//! SAT search instead of waiting for a complete model.
//!
//! # Architecture
//!
//! The `TheoryExtension` wrapper:
//! 1. Tracks SAT assignments incrementally via `propagate()` callback
//! 2. Feeds new assignments to the theory solver
//! 3. Queries the theory for propagations
//! 4. Converts theory propagations to SAT clauses
//! 5. Handles backtracking incrementally via push/pop
//!
//! # Performance Benefit
//!
//! For benchmarks like eq_diamond where transitivity propagations are critical,
//! eager propagation can dramatically reduce the search space by pruning
//! branches early rather than waiting to discover conflicts on complete models.

use z4_core::TheorySolver;
use z4_sat::{ExtCheckResult, ExtPropagateResult, Extension, SolverContext};
use z4_sat::{Literal, Variable};

mod types;
pub(crate) use types::TheoryAxiomKey;
pub(crate) use types::TheoryExtension;
use types::{BoundRefinementHandoff, ProofContext};

impl<T: TheorySolver> Extension for TheoryExtension<'_, T> {
    fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
        self.propagate_impl(ctx)
    }

    fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
        self.check_impl()
    }

    fn backtrack(&mut self, new_level: u32) {
        if self.debug {
            safe_eprintln!(
                "[EAGER] Backtracking from theory level {} to SAT level {}",
                self.theory_level,
                new_level
            );
        }

        // Pop theory scopes to match the new SAT decision level.
        // Restore last_trail_pos from the saved stack so propagate() only
        // re-processes genuinely new assignments (#5548).
        while self.theory_level > new_level {
            let from_level = self.theory_level;
            self.theory.pop();
            self.theory_level -= 1;
            self.last_trail_pos = self.level_trail_positions.pop().unwrap_or(0);
            if let Some(diag) = self.diagnostic_trace {
                diag.emit_pop(from_level, self.theory_level);
            }
            if self.debug {
                safe_eprintln!("[EAGER] Pop to theory level {}", self.theory_level);
            }
        }
        // Reset theory-aware branching scan index on backtrack.
        // Previously decided theory atoms may have been unassigned, so we
        // must re-scan from the start to find unassigned ones.
        self.theory_decision_idx.set(0);
        self.pending_bound_refinements.clear();
        // #4919: Reset batching state on backtrack — theory state changed.
        // Preserving the streak caused false-UNSAT on sat benchmarks (sc-6,
        // sc-8, vpm2-30): the streak triggered batching that deferred theory
        // checks, allowing SAT to accept theory-inconsistent assignments.
        self.zero_propagation_streak = 0;
        self.deferred_atom_count = 0;
        // Reset can_propagate scan position — trail has shrunk.
        self.can_propagate_scan_pos.set(0);
    }

    fn init(&mut self) {
        self.theory.reset();
        // Re-register theory atoms after reset so the theory solver can rebuild
        // its atom index for bound propagation (#4919 RC2).
        for &atom in self.theory_atoms {
            self.theory.register_atom(atom);
        }
        self.last_trail_pos = 0;
        self.theory_level = 0;
        self.pending_split = None;
        self.level_trail_positions.clear();
        self.theory_decision_idx.set(0);
        self.can_propagate_scan_pos.set(0);
    }

    fn can_propagate(&self, ctx: &dyn SolverContext) -> bool {
        // Fast gate: skip propagate_impl() entirely when there is provably
        // no theory-relevant work to do. This avoids the overhead of
        // entering propagate_impl(), incrementing stats, and running the
        // theory check on BCP rounds that only propagated boolean-only
        // literals.
        //
        // Must return true when:
        // - Pending axiom clauses need injection
        // - New trail assignments include at least one theory atom
        // - Theory scope needs synchronization (push needed)
        // - First call (has_checked == false) for initial state
        // - Pending split needs the stop signal
        if !self.pending_axiom_clauses.is_empty() {
            return true;
        }
        if !self.has_checked {
            return true;
        }
        let sat_level = ctx.decision_level();
        if self.theory_level < sat_level {
            return true;
        }
        // Pending split with high repeat count needs the stop signal.
        if self.pending_split.is_some() && self.expr_split_seen_count >= 50 {
            return true;
        }
        // Check if any new trail assignment is a theory atom using the dense
        // bitset. This is the key optimization: most BCP rounds propagate
        // only boolean-only (Tseitin encoding) literals, so scanning with
        // the bitset is faster than entering propagate_impl() and doing the
        // full loop with hashmap lookups + theory solver invocation.
        //
        // can_propagate_scan_pos tracks how far we've scanned without finding
        // a theory atom. This avoids re-scanning the same boolean-only trail
        // entries on repeated calls. Scan from max(last_trail_pos, scan_pos)
        // since last_trail_pos is only updated inside propagate_impl().
        let trail = ctx.trail();
        let scan_from = self.last_trail_pos.max(self.can_propagate_scan_pos.get());
        if scan_from < trail.len() {
            for &lit in &trail[scan_from..] {
                let id = lit.variable().id() as usize;
                let word_idx = id / 64;
                if word_idx < self.theory_var_bitset.len()
                    && (self.theory_var_bitset[word_idx] >> (id % 64)) & 1 != 0
                {
                    return true;
                }
            }
            // No theory atoms found in the new trail segment. Record how
            // far we scanned so we don't re-scan on the next call.
            self.can_propagate_scan_pos.set(trail.len());
        }
        false
    }

    fn suggest_decision(&self, ctx: &dyn SolverContext) -> Option<Literal> {
        // Theory-aware branching (#4919): decide theory atoms before encoding
        // variables. This matches Z3's theory_aware_branching which ensures all
        // theory atoms are decided before Tseitin encoding variables, giving the
        // theory solver maximum information for propagation.
        // Reference: Z3 smt_case_split_queue.cpp:1170-1209.
        //
        // Only enable for theories that explicitly support it (LRA/LIA/LIRA).
        // Theories with incomplete axiom generation (Seq, String, etc.) can
        // return false SAT when search order changes (#6236).
        if !self.theory.supports_theory_aware_branching() {
            return None;
        }
        // Scan theory_atoms from theory_decision_idx for the first unassigned atom
        // where the theory has an explicit phase preference. Atoms with None phase
        // are left to VSIDS, matching Z3's behavior where only atoms registered via
        // add_theory_aware_branching_info() get priority (#6303).
        let atoms = self.theory_atoms;
        let start = self.theory_decision_idx.get();
        for (i, &atom) in atoms.iter().enumerate().skip(start) {
            if let Some(&sat_var) = self.term_to_var.get(&atom) {
                let var = Variable::new(sat_var);
                if ctx.value(var).is_none() {
                    // Only decide atoms where the theory has an explicit preference.
                    // Atoms with None phase are left to VSIDS (#6303).
                    if let Some(phase) = self.theory.suggest_phase(atom) {
                        self.theory_decision_idx.set(i + 1);
                        let lit = if phase {
                            Literal::positive(var)
                        } else {
                            Literal::negative(var)
                        };
                        return Some(lit);
                    }
                }
            }
        }
        // No atoms with explicit phase preference remain. Leave None-phase
        // atoms to VSIDS, matching Z3's behavior where only atoms registered
        // via add_theory_aware_branching_info() get priority (#6303).
        self.theory_decision_idx.set(atoms.len());
        None
    }

    fn suggest_phase(&self, var: Variable) -> Option<bool> {
        // If this is a theory atom, ask the theory solver for its
        // LP-model-consistent polarity (Z3's get_phase).
        let term = self.var_to_term.get(&var.id())?;
        self.theory.suggest_phase(*term)
    }

    fn on_restart(&self) -> Vec<Variable> {
        // #7982: Return theory atom variables for VSIDS re-boosting at restart.
        // Theory atoms get one initial VSIDS bump at registration, but after
        // ~20 conflicts the bump is overwhelmed by conflict-driven activity.
        // Re-boosting at restart time keeps theory atoms competitive in the
        // VSIDS heap, combating the "bound starvation" problem where DPLL
        // stops deciding theory atoms and the theory gets no bounds to work
        // with. This matches Z3's approach of periodically re-prioritizing
        // theory variables (theory_var_init_value, mk_diseq).
        self.theory_atoms
            .iter()
            .filter_map(|term| self.term_to_var.get(term).map(|&v| Variable::new(v)))
            .collect()
    }
}

mod check;
mod construction;
mod helpers;
mod propagate;
pub(crate) use construction::infer_bound_axiom_arith_kind;

mod phase_hint;
pub(crate) use phase_hint::PhaseHintExtension;

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
