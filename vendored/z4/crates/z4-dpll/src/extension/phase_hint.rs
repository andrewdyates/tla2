// Copyright 2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0

#[cfg(not(kani))]
use hashbrown::HashMap;
use std::cell::Cell;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::{TermId, TheorySolver};
use z4_sat::{ExtPropagateResult, Extension, SolverContext};
use z4_sat::{Literal, Variable};

/// Lightweight extension that only provides phase hints from a theory solver.
///
/// Used by `DpllT::solve_step()` (lazy theory checking mode) to pass theory
/// phase suggestions to the SAT solver without the overhead of eager theory
/// propagation. The split-loop pipeline handles theory checking externally;
/// this extension only provides `suggest_phase` guidance.
///
/// # Motivation (#6282)
///
/// Z4's SAT solver defaults to positive phase (true) for uninitialized variables.
/// For array index equality atoms `(= i j)`, this means "assume equal" — the
/// opposite of Z3's default (`m_phase_default = false` → "assume distinct").
/// This causes exponential blowup on storeinv benchmarks because the SAT solver
/// eagerly satisfies index equalities, triggering a cascade of ROW axioms.
///
/// The `PhaseHintExtension` bridges the gap: combined theory solvers (AUFLIA,
/// AUFLRA, etc.) implement `suggest_phase` to return `false` for simple index
/// equality atoms, matching Z3's behavior. This extension forwards those hints
/// to the SAT solver during lazy theory checking.
pub(crate) struct PhaseHintExtension<'a, T: TheorySolver> {
    /// The theory solver (borrowed immutably for suggest_phase)
    theory: &'a T,
    /// Mapping from SAT variables to term IDs
    var_to_term: &'a HashMap<u32, TermId>,
    /// Mapping from term IDs to SAT variables (for suggest_decision)
    term_to_var: &'a HashMap<TermId, u32>,
    /// Theory atoms in registration order (for suggest_decision)
    theory_atoms: &'a [TermId],
    /// Scan index for theory-aware branching (amortized O(1) per call).
    /// Uses Cell for interior mutability since suggest_decision takes &self.
    theory_decision_idx: Cell<usize>,
}

impl<'a, T: TheorySolver> PhaseHintExtension<'a, T> {
    pub(crate) fn new(
        theory: &'a T,
        var_to_term: &'a HashMap<u32, TermId>,
        term_to_var: &'a HashMap<TermId, u32>,
        theory_atoms: &'a [TermId],
    ) -> Self {
        Self {
            theory,
            var_to_term,
            term_to_var,
            theory_atoms,
            theory_decision_idx: Cell::new(0),
        }
    }
}

impl<T: TheorySolver> Extension for PhaseHintExtension<'_, T> {
    fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
        // No theory propagation — handled by the split-loop pipeline externally.
        ExtPropagateResult::none()
    }

    fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
        // Never propagate — avoids redundant propagate() calls in the CDCL loop.
        false
    }

    fn backtrack(&mut self, _new_level: u32) {
        // Reset theory-aware branching scan index on backtrack.
        // Previously decided theory atoms may have been unassigned, so we
        // must re-scan from the start to find unassigned ones.
        // Matches TheoryExtension::backtrack behavior (line 1184).
        self.theory_decision_idx.set(0);
    }

    fn suggest_decision(&self, ctx: &dyn SolverContext) -> Option<Literal> {
        // Theory-aware branching (#6282): decide theory atoms before Tseitin
        // encoding variables. This matches Z3's theory_aware_branching (see
        // smt_case_split_queue.cpp:1170-1209) and ensures the SAT solver
        // assigns all meaningful atoms before auxiliary Tseitin variables.
        //
        // Only enable for theories that support it.
        if !self.theory.supports_theory_aware_branching() {
            return None;
        }
        // Only decide atoms where the theory has an explicit preference (#6303).
        // Atoms with None phase are left to VSIDS, matching Z3's behavior.
        let start = self.theory_decision_idx.get();
        for (i, &atom) in self.theory_atoms.iter().enumerate().skip(start) {
            if let Some(&sat_var) = self.term_to_var.get(&atom) {
                let var = Variable::new(sat_var);
                if ctx.value(var).is_none() {
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
        self.theory_decision_idx.set(self.theory_atoms.len());
        None
    }

    fn suggest_phase(&self, var: Variable) -> Option<bool> {
        let term = self.var_to_term.get(&var.id())?;
        self.theory.suggest_phase(*term)
    }
}
