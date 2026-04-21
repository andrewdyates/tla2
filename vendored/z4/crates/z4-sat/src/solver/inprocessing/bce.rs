// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Blocked clause elimination (BCE).

use super::super::mutate::ReasonPolicy;
use super::super::*;

impl Solver {
    /// Run blocked clause elimination (wrapper: always reschedules).
    pub(in crate::solver) fn bce(&mut self) {
        self.bce_body();
        self.inproc_ctrl
            .bce
            .reschedule(self.num_conflicts, BCE_INTERVAL);
    }

    /// BCE body — early returns are safe; wrapper handles rescheduling.
    ///
    /// A clause is blocked on literal L if for every clause D containing ~L,
    /// resolving C and D on L produces a tautology. Blocked clauses can be
    /// safely removed without changing satisfiability.
    ///
    /// This must be called at decision level 0 (after a restart) for correctness.
    fn bce_body(&mut self) {
        if !self.enter_inprocessing() {
            return;
        }

        // Defense-in-depth: BCE uses reconstruction stack (push_bce), so it
        // must not fire in incremental mode even if re-enabled via set_bce_enabled.
        // Matches the guard pattern in condition() and decompose() (#3662).
        if self.cold.has_been_incremental {
            return;
        }

        // Rebuild occurrence lists
        self.inproc.bce.rebuild(&self.arena);

        // Scale BCE elimination limit with active variables.
        // CaDiCaL runs BCE fully within interleaved elim pipeline; fixed cap
        // starves on large formulas. Base: MAX_BCE_ELIMINATIONS, scale: active_vars / 100.
        let active_vars = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed());
        let bce_limit = MAX_BCE_ELIMINATIONS.max(active_vars / 100);

        // Run elimination (pass freeze_counts to skip frozen literals as blocking candidates)
        let eliminated = self.inproc.bce.run_elimination_with_marks(
            &self.arena,
            &self.cold.freeze_counts,
            bce_limit,
            &mut self.lit_marks,
        );

        // Delete the eliminated clauses and save for reconstruction
        for elim in eliminated {
            let clause_idx = elim.clause_idx;
            let blocking_literal = elim.blocking_literal;
            let _ = self.delete_clause_with_snapshot(
                clause_idx,
                ReasonPolicy::Skip,
                move |solver, clause_lits| {
                    // CaDiCaL block.cpp: blocking literal must be present in clause
                    debug_assert!(
                        clause_lits.contains(&blocking_literal),
                        "BUG: BCE blocking literal {blocking_literal:?} not in clause {clause_idx}",
                    );
                    let ext_blocking = solver.externalize(blocking_literal);
                    let ext_lits = solver.externalize_lits(&clause_lits);
                    solver
                        .inproc
                        .reconstruction
                        .push_bce(ext_blocking, ext_lits);
                },
            );
        }
    }
}
