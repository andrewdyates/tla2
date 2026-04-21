// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Transitive reduction of the binary implication graph.

use super::super::mutate::ReasonPolicy;
use super::super::*;

impl Solver {
    /// Run transitive reduction (wrapper: always reschedules).
    pub(in crate::solver) fn transred(&mut self) {
        self.transred_body();
        self.inproc_ctrl
            .transred
            .reschedule(self.num_conflicts, TRANSRED_INTERVAL);
    }

    /// Transitive reduction body — early returns are safe; wrapper handles rescheduling.
    ///
    /// A binary clause `(a -> b)` is transitive if there exists an alternate path
    /// from `a` to `b` through other binary clauses. Transitive clauses can be
    /// safely removed without affecting satisfiability.
    ///
    /// This must be called at decision level 0 (after a restart) for correctness.
    fn transred_body(&mut self) {
        if !self.enter_inprocessing() {
            return;
        }

        // Compute tick-proportional effort budget.
        // CaDiCaL transred.cpp:30-36: effort = (propagations_search - last) * permille / 1000
        // Clamped to [TRANSRED_MIN_EFFORT, TRANSRED_MAX_EFFORT], floor at 2*active_vars.
        let active_vars = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed()) as u64;
        let props_delta = self
            .num_propagations
            .saturating_sub(self.inproc.transred_engine.last_propagations());
        let effort = (props_delta * TRANSRED_EFFORT_PERMILLE / 1000)
            .clamp(TRANSRED_MIN_EFFORT, TRANSRED_MAX_EFFORT);
        let effort = effort.max(2 * active_vars);

        // Run transitive reduction
        let result = self.inproc.transred_engine.run(
            &self.arena,
            &self.watches,
            &self.vals,
            self.cold.original_clause_boundary,
            effort,
        );
        self.inproc
            .transred_engine
            .set_last_propagations(self.num_propagations);

        // Process failed literals (propagate units).
        // Transred BFS found that probing `src` reaches both `x` and `¬x`,
        // so `¬src` (the stored unit) must be true.
        //
        // For LRAT we need explicit hint chains. Transred's internal BFS
        // doesn't record reason clauses, so we re-probe through the solver's
        // BCP to collect the conflict chain — matching probe.rs's pattern.
        // For DRAT (non-LRAT), empty hints are acceptable.
        for unit in &result.failed_literals {
            if self.var_is_assigned(unit.variable().index()) {
                continue;
            }
            if self.cold.lrat_enabled {
                // Re-probe the negation of the unit through solver BCP.
                // unit = ¬src, so unit.negated() = src — the literal whose
                // implications cause a contradiction.
                let probe_lit = unit.negated();
                self.decide(probe_lit);
                if let Some(conflict_ref) = self.search_propagate() {
                    let lrat_hints = self.collect_probe_conflict_lrat_hints(
                        conflict_ref,
                        probe_lit,
                        Some(*unit),
                    );
                    self.backtrack(0);
                    if self.learn_derived_unit(*unit, &lrat_hints) {
                        // Level-0 conflict — UNSAT. Remaining failed literals
                        // and transitive deletions are irrelevant.
                        return;
                    }
                } else {
                    // BCP didn't reproduce the conflict. This can happen if
                    // a prior unit's level-0 propagation resolved intermediate
                    // clauses in the BFS chain. Skip this unit; normal probing
                    // will discover and properly certify it later.
                    self.backtrack(0);
                }
            } else {
                self.proof_emit_unit(*unit, &[], ProofAddKind::Derived);
                self.enqueue(*unit, None);
            }
        }

        // Delete transitive clauses
        for clause_ref in &result.transitive_clauses {
            self.delete_clause_checked(clause_ref.0 as usize, ReasonPolicy::Skip);
        }

        #[cfg(debug_assertions)]
        {
            // Post-condition: each failed literal from this round must now be assigned
            // (either pre-existing or enqueued above) — UNLESS LRAT mode skipped it
            // because re-probing didn't reproduce the conflict.
            if !self.cold.lrat_enabled {
                for &unit in &result.failed_literals {
                    let var_idx = unit.variable().index();
                    debug_assert!(
                        self.var_is_assigned(var_idx),
                        "BUG: transred() left failed literal {unit:?} unassigned"
                    );
                }
            }

            // Post-condition: each transitive clause is either deleted or retained
            // only because reason-clause protection blocked deletion.
            for &clause_ref in &result.transitive_clauses {
                let clause_idx = clause_ref.0 as usize;
                if clause_idx >= self.arena.len() || !self.arena.is_active(clause_idx) {
                    continue;
                }
                debug_assert!(
                    self.is_reason_clause_marked(clause_idx),
                    "BUG: transred() left transitive clause {clause_idx} active without reason protection"
                );
            }
        }

        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: transred() did not restore decision level to 0"
        );
    }
}
