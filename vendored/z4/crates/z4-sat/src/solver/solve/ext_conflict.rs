// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extension-conflict postprocessing.
//!
//! Computes the backtrack level for a theory conflict clause and applies
//! the conflict as a learned nogood.

use super::super::*;

impl Solver {
    /// Compute the backtrack level for a theory conflict clause.
    ///
    /// Returns the second-highest decision level among assigned literals.
    /// Theory conflicts can't use full 1UIP analysis because some literals
    /// may be decisions without reason clauses.
    fn ext_conflict_backtrack_level(&self, conflict: &[Literal]) -> u32 {
        // Find the two highest distinct decision levels in O(n) without allocation.
        let mut top1: u32 = 0;
        let mut top2: u32 = 0;
        let mut found_any = false;
        for lit in conflict {
            let idx = lit.variable().index();
            if idx < self.num_vars && self.var_is_assigned(idx) {
                let lev = self.var_data[idx].level;
                found_any = true;
                if lev > top1 {
                    top2 = top1;
                    top1 = lev;
                } else if lev > top2 && lev != top1 {
                    top2 = lev;
                }
            }
        }
        let bt = if top1 != top2 && found_any {
            top2
        } else if found_any {
            top1.saturating_sub(1)
        } else {
            0
        };
        debug_assert!(
            bt <= self.decision_level,
            "BUG: ext conflict backtrack_level ({bt}) > decision_level ({})",
            self.decision_level,
        );
        bt
    }

    /// Handle a non-empty theory conflict from an Extension callback.
    ///
    /// Counts the conflict, computes the backtrack level, adds the clause
    /// as a learned nogood, backtracks with extension notification, and
    /// enqueues any resulting unit literal.
    ///
    /// The caller must have already:
    /// - Checked for empty clause (returns UNSAT directly)
    /// - Emitted the TLA trace `DetectConflict` step
    pub(in crate::solver) fn handle_ext_conflict(
        &mut self,
        conflict: Vec<Literal>,
        ext: &mut dyn Extension,
    ) {
        // Theory conflict clause must be non-empty (caller checks for empty)
        debug_assert!(
            !conflict.is_empty(),
            "BUG: handle_ext_conflict called with empty conflict clause"
        );
        // All conflict literals must have variables in range
        debug_assert!(
            conflict
                .iter()
                .all(|l| l.variable().index() < self.num_vars),
            "BUG: theory conflict contains out-of-range variable"
        );
        self.conflicts_since_restart += 1;
        self.num_conflicts += 1;
        self.on_conflict_random_decision();

        let backtrack_level = self.ext_conflict_backtrack_level(&conflict);

        // DEBUG: trace theory conflict handling for #7935 investigation
        if self.cold.trace_ext_conflict {
            eprintln!(
                "[EXT_CONFLICT] dl={} bt_level={} conflict_len={} lits={:?}",
                self.decision_level,
                backtrack_level,
                conflict.len(),
                conflict
                    .iter()
                    .map(|l| (l.variable().index(), l.is_positive()))
                    .collect::<Vec<_>>()
            );
            for lit in &conflict {
                let var = lit.variable();
                let assigned = self.var_is_assigned(var.index());
                let level = if assigned {
                    self.var_data[var.index()].level
                } else {
                    u32::MAX
                };
                let val = self.var_value_from_vals(var.index());
                eprintln!(
                    "[EXT_CONFLICT]   var={} pos={} assigned={} level={} val={:?}",
                    var.index(),
                    lit.is_positive(),
                    assigned,
                    level,
                    val
                );
            }
        }

        // Backtrack BEFORE adding the theory lemma (CaDiCaL pattern).
        // Adding the lemma pre-backtrack causes three problems:
        // 1. Watches are computed for the wrong (pre-backtrack) assignment state
        // 2. add_theory_lemma may enqueue at the wrong decision level
        // 3. Requires redundant manual unit-check code after backtracking
        // After backtracking, the clause becomes unit (one asserting literal
        // unassigned), and add_theory_lemma handles watch setup and enqueue
        // at the correct level.
        ext.backtrack(backtrack_level);
        self.backtrack(backtrack_level);

        if self.cold.trace_ext_conflict {
            eprintln!(
                "[EXT_CONFLICT] after backtrack: dl={} trail_len={}",
                self.decision_level,
                self.trail.len()
            );
            for lit in &conflict {
                let var = lit.variable();
                let assigned = self.var_is_assigned(var.index());
                let val = self.var_value_from_vals(var.index());
                eprintln!(
                    "[EXT_CONFLICT]   var={} assigned={} val={:?}",
                    var.index(),
                    assigned,
                    val
                );
            }
        }

        if self.add_theory_lemma(conflict).is_some() {
            self.tla_trace_step("PROPAGATING", Some("AnalyzeAndLearn"));
            if self.stable_mode {
                self.vsids.decay();
            }
            if self.should_reduce_db() {
                self.reduce_db();
            }
        }
    }
}
