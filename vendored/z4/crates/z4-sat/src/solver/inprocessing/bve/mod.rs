// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded variable elimination (BVE).

use super::super::*;
use super::RANDOM_KSAT_MIN_CLAUSES;

/// Maximum occurrences per polarity during fastelim (preprocessing).
/// CaDiCaL `fastelimocclim=100` (elimfast.cpp:16-22) uses 100 per-polarity.
/// Kissat `eliminateocclim=2000` uses 2000 total for all elimination.
/// On BVE-dominated formulas like mp1-klieber (30K vars, Kissat eliminates
/// 86%), CaDiCaL's 100 is too restrictive. Use 500 per-polarity to allow
/// profitable eliminations while keeping the resolution product bounded
/// (500*500=250K max pairs per var, well within the FASTELIM_EFFORT budget).
const FASTELIM_OCC_LIMIT: usize = 500;

mod apply;
mod body;
mod propagate;
mod state;

impl Solver {
    /// Check if we should run BVE.
    ///
    /// Uses a growing interval (CaDiCaL pattern) so BVE runs less frequently
    /// in later phases. Dual fixed-point guard (CaDiCaL `ineliminating()`,
    /// elim.cpp:60-84): re-fire when new level-0 units have been discovered
    /// OR when irredundant clauses were modified by other inprocessing passes
    /// (subsumption, vivification, decompose).
    ///
    /// The `bve_marked` counter tracks irredundant clause modifications only.
    /// This avoids the mutual re-triggering cycle with `clause_db_changes`
    /// that previously caused infinite BVE/subsumption loops on random 3-SAT
    /// (#4051): BVE itself does not increment `bve_marked`, so its resolvents
    /// do not re-trigger subsumption→BVE cycles.
    pub(in crate::solver) fn should_bve(&self) -> bool {
        if !self.inproc_ctrl.bve.should_fire(self.num_conflicts) {
            return false;
        }
        if self.cold.last_bve_fixed == self.fixed_count
            && self.cold.last_bve_marked == self.cold.bve_marked
            && !self.inproc.bve.has_dirty_candidates()
        {
            return false;
        }
        // Growth control is handled per-phase in inprocessing_schedule.rs
        // (5% active-clause growth limit per BVE phase, lines 414-425).
        // A cross-phase guard using active_clause_count() is not used because
        // it includes learned clauses, which grow during search and would
        // permanently suppress BVE after the first inprocessing phase (#7178).
        // CaDiCaL does not have a cross-phase clause-count guard either —
        // it relies on per-variable bounds (elimbound) and inter-round
        // subsumption to control growth.
        true
    }

    /// Record an irredundant clause deletion as new BVE work.
    pub(in crate::solver) fn note_irredundant_clause_removed_for_bve(
        &mut self,
        old_lits: &[Literal],
    ) {
        self.inproc.bve.mark_candidates_dirty_clause(old_lits);
        self.cold.bve_marked = self.cold.bve_marked.saturating_add(1);
    }

    /// Record an irredundant clause strengthening as new BVE work.
    pub(in crate::solver) fn note_irredundant_clause_replaced_for_bve(
        &mut self,
        old_lits: &[Literal],
        new_lits: &[Literal],
    ) {
        self.inproc.bve.mark_candidates_dirty_clause(old_lits);
        self.inproc.bve.mark_candidates_dirty_clause(new_lits);
        self.cold.bve_marked = self.cold.bve_marked.saturating_add(1);
    }

    /// Record the active clause count after a BVE phase for diagnostics.
    ///
    /// Tracks min(post-phase, pre-phase) active clause count. Informational
    /// only — growth control is per-phase in inprocessing_schedule.rs (#7178).
    pub(in crate::solver) fn update_bve_growth_guard(&mut self, clauses_before_phase: usize) {
        self.cold.last_bve_clauses = self.arena.active_clause_count().min(clauses_before_phase);
    }

    /// Detect likely-random k-SAT formulas where gate/BVE passes are
    /// typically wasted work.
    ///
    /// Heuristic (irredundant clauses only):
    /// - no binary clauses
    /// - all clauses have the same length
    /// - uniform length is at least 3
    /// - at least `RANDOM_KSAT_MIN_CLAUSES` active clauses
    ///
    /// This is intentionally conservative: false negatives are acceptable,
    /// false positives on tiny structured formulas are not.
    pub(in crate::solver) fn is_uniform_nonbinary_irredundant_formula(&mut self) -> bool {
        if let Some(cached) = self.cold.uniform_formula_cache {
            return cached;
        }
        let result = self.compute_uniform_nonbinary_irredundant_formula();
        self.cold.uniform_formula_cache = Some(result);
        result
    }

    /// Recompute the uniform formula detection (O(total_clauses)).
    /// Called only when the cache is dirty.
    fn compute_uniform_nonbinary_irredundant_formula(&self) -> bool {
        let mut clause_count = 0usize;
        let mut uniform_len: Option<usize> = None;

        for idx in self.arena.indices() {
            let off = idx;
            if self.arena.is_dead(off) || self.arena.is_learned(off) {
                continue;
            }
            let len = self.arena.len_of(off);

            // Binary/unit/empty clauses indicate structure that can benefit
            // from gate extraction and elimination.
            if len <= 2 {
                return false;
            }

            match uniform_len {
                Some(expected) if expected != len => return false,
                Some(_) => {}
                None => uniform_len = Some(len),
            }

            clause_count += 1;
        }

        clause_count >= RANDOM_KSAT_MIN_CLAUSES && uniform_len.is_some_and(|len| len >= 3)
    }

    /// Invalidate the cached uniform formula detection result.
    /// Must be called when irredundant clauses are added, deleted, or strengthened.
    #[inline]
    #[allow(dead_code)]
    pub(in crate::solver) fn invalidate_uniform_formula_cache(&mut self) {
        self.cold.uniform_formula_cache = None;
    }

    /// Run bounded variable elimination
    ///
    /// Attempts to eliminate variables by resolving clauses. For a variable x,
    /// if the total size of resolvents is bounded, we can eliminate x by:
    /// 1. Adding all resolvents
    /// 2. Removing all clauses containing x
    ///
    /// This must be called at decision level 0 (after a restart) for correctness.
    ///
    /// Returns true if UNSAT was derived (empty resolvent found).
    ///
    /// REQUIRES: decision_level == 0, last_bve_fixed != fixed_count (fixpoint guard)
    /// ENSURES: eliminated variables marked in self.var_lifecycle and removed from VSIDS,
    ///          no active learned clause contains a removed variable,
    ///          reconstruction entries pushed for all deleted clauses
    pub(in crate::solver) fn bve(&mut self) -> bool {
        // Defer the O(num_vars) stale reason scan during bulk deletions.
        // BVE deletes many clauses per variable; batching the scan reduces
        // cost from O(deleted × num_vars) to O(deleted + num_vars).
        self.defer_stale_reason_cleanup = true;
        let result = self.bve_body();
        self.defer_stale_reason_cleanup = false;
        self.clear_stale_reasons();
        // Schedule next BVE with growing interval (CaDiCaL elim.cpp:1161).
        // CaDiCaL: delta = scale(elimint * (phases + 1))
        // scale() = log2(ratio) when clause/var ratio > 2, else 1.0.
        let base = BVE_INTERVAL_BASE.saturating_mul(u64::from(self.cold.bve_phases + 1));
        let ratio = self.num_original_clauses as f64 / self.num_vars.max(1) as f64;
        // Cap at 3.0 (ratio=8 threshold): Z4's BVE is weaker than CaDiCaL's,
        // so extreme interval stretching (5.87x on stable-300's ratio=58.5)
        // starves BVE on small high-ratio formulas. CaDiCaL compensates via
        // stronger elimination cascades that Z4 doesn't yet have (#7191).
        let factor = if ratio <= 2.0 {
            1.0
        } else {
            ratio.log2().min(3.0)
        };
        let interval = (base as f64 * factor) as u64;
        self.inproc_ctrl
            .bve
            .reschedule(self.num_conflicts, interval);
        result
    }
}
