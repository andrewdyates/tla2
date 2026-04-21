// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BVE occurrence management and scheduling.

use crate::clause_arena::ClauseArena;
use crate::gates::GateExtractor;
use crate::lit_marks::LitMarks;
use crate::literal::{Literal, Variable};

use super::{BVE, ELIM_OCC_LIMIT};

impl BVE {
    /// Notify the BVE engine that a resolvent clause was added to the clause DB.
    /// Updates occurrence lists so subsequent eliminations see the new clause.
    /// (CaDiCaL equivalent: `elim_update_added_clause`.)
    ///
    /// REQUIRES: clause must be irredundant, literals does not contain eliminated variables
    /// ENSURES: each literal in the clause has clause_idx in its occ list
    pub(crate) fn notify_resolvent_added(&mut self, clause_idx: usize, literals: &[Literal]) {
        // CaDiCaL elim.cpp: resolvents added to occ lists must be non-empty.
        // An empty resolvent means UNSAT was detected during resolution and
        // should be handled before reaching occ list updates.
        debug_assert!(
            !literals.is_empty(),
            "BUG: notify_resolvent_added called with empty clause (UNSAT not handled)",
        );
        debug_assert!(
            literals
                .iter()
                .all(|l| l.variable().index() < self.num_vars),
            "BUG: resolvent literal variable index >= num_vars {}",
            self.num_vars,
        );
        debug_assert!(
            literals
                .iter()
                .all(|l| !self.eliminated[l.variable().index()]),
            "BUG: resolvent contains eliminated variable(s): {literals:?}"
        );
        self.occ.add_clause(clause_idx, literals);
        // CaDiCaL elim.cpp:90-105: update existing heap entries on addition.
        for &lit in literals {
            let var = lit.variable();
            if !self.eliminated[var.index()] && self.schedule.contains(var) {
                self.schedule
                    .update(var, &self.occ, &self.schedule_gate_pair_credit);
            }
        }
    }

    /// Notify the BVE engine that an existing clause was strengthened in-place.
    ///
    /// Removes old literal occurrences and adds the new literal occurrences so
    /// subsequent eliminations in the same round see the updated clause.
    ///
    /// REQUIRES: clause must be irredundant, new_lits does not contain eliminated variables
    pub(crate) fn notify_clause_replaced(
        &mut self,
        clause_idx: usize,
        old_lits: &[Literal],
        new_lits: &[Literal],
    ) {
        debug_assert!(
            !new_lits.is_empty(),
            "BUG: notify_clause_replaced called with empty clause",
        );
        debug_assert!(
            new_lits
                .iter()
                .all(|l| l.variable().index() < self.num_vars),
            "BUG: replacement literal variable index >= num_vars {}",
            self.num_vars,
        );
        debug_assert!(
            new_lits
                .iter()
                .all(|l| !self.eliminated[l.variable().index()]),
            "BUG: replacement clause contains eliminated variable(s): {new_lits:?}",
        );
        self.occ.remove_clause(clause_idx, old_lits);
        self.occ.add_clause(clause_idx, new_lits);
        // CaDiCaL elim_update_removed_clause: update-or-reinsert removed lits.
        for &lit in old_lits {
            let var = lit.variable();
            if self.eliminated[var.index()] {
                continue;
            }
            if self.schedule.contains(var) {
                self.schedule
                    .update(var, &self.occ, &self.schedule_gate_pair_credit);
            } else {
                self.schedule
                    .push(var, &self.occ, &self.schedule_gate_pair_credit);
            }
        }
        // CaDiCaL elim_update_added_clause: update only for added lits.
        for &lit in new_lits {
            let var = lit.variable();
            if !self.eliminated[var.index()] && self.schedule.contains(var) {
                self.schedule
                    .update(var, &self.occ, &self.schedule_gate_pair_credit);
            }
        }
    }

    /// Initialize/rebuild occurrence lists from clause database.
    ///
    /// REQUIRES: clauses contains valid clause data (headers consistent with literals)
    /// ENSURES: occ lists reflect exactly the non-deleted irredundant clauses in `clauses`,
    ///          schedule is empty (rebuilt lazily on next next_candidate call)
    #[cfg(test)]
    pub(crate) fn rebuild(&mut self, clauses: &ClauseArena) {
        self.rebuild_inner(clauses, &[]);
        // A full rebuild (no vals) resets the entire occurrence state.
        // Mark all non-eliminated variables dirty so build_schedule
        // considers every variable as a candidate (#7917).
        self.mark_all_candidates_dirty();
    }

    /// Rebuild occurrence lists, filtering out clauses satisfied at root level.
    ///
    /// CaDiCaL elimfast.cpp:302-316: before building occurrence lists, scan
    /// each irredundant clause and skip any that are satisfied by root-level
    /// assignments. Without this filter, satisfied clauses inflate occurrence
    /// counts and distort elimination decisions. Z4's 2WL propagation skips
    /// satisfied clauses at runtime but doesn't remove them from the arena,
    /// so they accumulate across probing/decompose/HTR passes.
    ///
    /// `vals` is the literal value array: `vals[lit.index()] > 0` means true.
    /// An empty `vals` slice disables the filter (used by `rebuild()`).
    pub(crate) fn rebuild_with_vals(&mut self, clauses: &ClauseArena, vals: &[i8]) {
        self.rebuild_inner(clauses, vals);
    }

    fn rebuild_inner(&mut self, clauses: &ClauseArena, vals: &[i8]) {
        let filter_satisfied = !vals.is_empty();

        #[cfg(debug_assertions)]
        self.debug_check_no_eliminated_in_active(clauses, vals, filter_satisfied);

        self.occ.clear();

        // CaDiCaL elim.cpp:804-805, 863-864: occurrence lists must contain
        // only irredundant (original) clauses. Including learned clauses inflates
        // bound decisions and may produce invalid reconstruction witnesses (#5019).
        for idx in clauses.indices() {
            if clauses.is_dead(idx) || clauses.is_learned(idx) {
                continue;
            }
            if filter_satisfied {
                let mut satisfied = false;
                let mut falsified = false;
                for &lit in clauses.literals(idx) {
                    let val = vals.get(lit.index()).copied().unwrap_or(0);
                    if val > 0 {
                        satisfied = true;
                        break;
                    }
                    if val < 0 {
                        falsified = true;
                    }
                }
                // CaDiCaL elimfast.cpp:315-316: skip satisfied clauses.
                if satisfied {
                    continue;
                }
                // CaDiCaL elim.cpp:804-822 marks all active literals in clauses
                // touched by root-level falsifications. These are the variables
                // whose occurrence counts changed since the last completed BVE
                // round and need to be reconsidered.
                if falsified {
                    for &lit in clauses.literals(idx) {
                        let var_idx = lit.variable().index();
                        if vals.get(lit.index()).copied().unwrap_or(0) == 0
                            && var_idx < self.candidate_dirty.len()
                            && !self.eliminated[var_idx]
                        {
                            self.candidate_dirty[var_idx] = true;
                        }
                    }
                }
            }
            self.occ.add_clause(idx, clauses.literals(idx));
        }

        // Gate pair credit is only used for gate-aware BVE scheduling.
        // Skip in fastelim mode (preprocessing) where gate extraction is
        // disabled. On shuffling-2 (138K vars), this avoids O(vars * gate)
        // work per BVE round during preprocessing.
        if !self.fastelim_mode {
            self.refresh_schedule_gate_pair_credit(clauses, vals);
        }

        // Schedule heap cleared; rebuilt lazily on next next_candidate call.
        self.schedule.clear();
        self.schedule_built = false;

        #[cfg(debug_assertions)]
        self.debug_check_occ_consistency(clauses, vals, filter_satisfied);
    }

    /// Check if a clause is satisfied by root-level assignments in `vals`.
    #[cfg(debug_assertions)]
    fn clause_satisfied(clauses: &ClauseArena, idx: usize, vals: &[i8]) -> bool {
        clauses
            .literals(idx)
            .iter()
            .any(|&lit| (lit.index()) < vals.len() && vals[lit.index()] > 0)
    }

    /// Precondition: no active irredundant clause in occ-list scope should
    /// contain a variable we've already eliminated. Satisfied clauses are
    /// excluded from occ lists and may legitimately contain eliminated variables.
    #[cfg(debug_assertions)]
    fn debug_check_no_eliminated_in_active(
        &self,
        clauses: &ClauseArena,
        vals: &[i8],
        filter_satisfied: bool,
    ) {
        for idx in clauses.indices() {
            if clauses.is_dead(idx) || clauses.is_learned(idx) {
                continue;
            }
            if filter_satisfied && Self::clause_satisfied(clauses, idx, vals) {
                continue;
            }
            for &lit in clauses.literals(idx) {
                let vi = lit.variable().index();
                debug_assert!(
                    vi >= self.eliminated.len() || !self.eliminated[vi],
                    "BUG: live irredundant clause {idx} contains eliminated variable {vi}",
                );
            }
        }
    }

    /// Post-condition: occurrence counts must be consistent with clause DB.
    #[cfg(debug_assertions)]
    fn debug_check_occ_consistency(
        &self,
        clauses: &ClauseArena,
        vals: &[i8],
        filter_satisfied: bool,
    ) {
        for idx in clauses.indices() {
            if clauses.is_dead(idx) || clauses.is_learned(idx) {
                continue;
            }
            if filter_satisfied && Self::clause_satisfied(clauses, idx, vals) {
                continue;
            }
            for &lit in clauses.literals(idx) {
                debug_assert!(
                    self.occ.get(lit).contains(&idx),
                    "BUG: rebuild() occ list for {lit:?} missing clause {idx}"
                );
            }
        }
    }

    #[inline]
    pub(super) fn candidate_occurrence_counts(
        &self,
        var_idx: usize,
        vals: &[i8],
        frozen: &[u32],
    ) -> Option<(Variable, usize, usize)> {
        debug_assert!(
            var_idx < self.num_vars,
            "BUG: candidate index {var_idx} out of bounds for num_vars {}",
            self.num_vars
        );
        if self.eliminated[var_idx] {
            return None;
        }
        if var_idx * 2 < vals.len() && vals[var_idx * 2] != 0 {
            return None;
        }
        if var_idx < frozen.len() && frozen[var_idx] > 0 {
            return None;
        }

        let var = Variable(var_idx as u32);
        let pos_count = self.occ.count(Literal::positive(var));
        let neg_count = self.occ.count(Literal::negative(var));

        // Dead variables (0 in both polarities) have no clauses to eliminate.
        // Skip these — they may be substituted or otherwise removed.
        if pos_count == 0 && neg_count == 0 {
            return None;
        }
        // Pure variables (0 in one polarity) ARE eligible for elimination.
        // Pure elimination requires zero resolvents — just delete all clauses
        // containing the variable. check_bounded_elimination_with_marks filters
        // stale occ entries inline, so stale counts here don't affect correctness.
        // Kissat resolve.c:282-289: total occurrence limit (not per-polarity).
        if pos_count + neg_count > ELIM_OCC_LIMIT {
            return None;
        }

        Some((var, pos_count, neg_count))
    }

    /// Build the elimination schedule as an indexed min-heap.
    ///
    /// REQUIRES: occ lists are up-to-date with clause DB
    /// ENSURES: schedule contains only non-eliminated, unassigned, unfrozen vars
    ///          with both-polarity occurrences, ordered by score (min-heap)
    pub(super) fn build_schedule(&mut self, vals: &[i8], frozen: &[u32]) {
        self.schedule.clear();
        let use_dirty_filter = !self.fastelim_mode;

        for var_idx in 0..self.num_vars {
            if use_dirty_filter && !self.candidate_dirty.get(var_idx).copied().unwrap_or(false) {
                continue;
            }
            let Some((var, _, _)) = self.candidate_occurrence_counts(var_idx, vals, frozen) else {
                continue;
            };

            self.schedule
                .push(var, &self.occ, &self.schedule_gate_pair_credit);
        }
    }

    /// CaDiCaL `elim_update_removed_clause` (elim.cpp:107-134): when a clause
    /// is deleted, re-insert its variables into the schedule with updated scores.
    /// The eliminated variable (`except`) is skipped.
    pub(crate) fn update_schedule_after_clause_removal(
        &mut self,
        clause_lits: &[Literal],
        except: Variable,
        vals: &[i8],
        frozen: &[u32],
    ) {
        for &lit in clause_lits {
            let var = lit.variable();
            if var == except {
                continue;
            }
            let vi = var.index();
            // Skip eliminated, assigned, or frozen variables.
            if vi < self.eliminated.len() && self.eliminated[vi] {
                continue;
            }
            if vi * 2 < vals.len() && vals[vi * 2] != 0 {
                continue;
            }
            if vi < frozen.len() && frozen[vi] != 0 {
                continue;
            }
            self.schedule
                .push_or_update(var, &self.occ, &self.schedule_gate_pair_credit);
        }
    }

    /// CaDiCaL `elim_update_added_clause` (elim.cpp:90-105): when a clause
    /// is added (resolvent), update scores only for variables already in the heap.
    /// New variables are NOT inserted — only existing entries are rescored.
    pub(crate) fn update_schedule_after_clause_addition(&mut self, clause_lits: &[Literal]) {
        for &lit in clause_lits {
            let var = lit.variable();
            if self.schedule.contains(var) {
                self.schedule
                    .update(var, &self.occ, &self.schedule_gate_pair_credit);
            }
        }
    }

    fn refresh_schedule_gate_pair_credit(&mut self, clauses: &ClauseArena, vals: &[i8]) {
        if self.schedule_gate_pair_credit.len() < self.num_vars {
            self.schedule_gate_pair_credit.resize(self.num_vars, 0);
        }
        for credit in &mut self.schedule_gate_pair_credit {
            *credit = 0;
        }

        let mut extractor = GateExtractor::new(self.num_vars);
        let mut marks = LitMarks::new(self.num_vars.max(1));

        for var_idx in 0..self.num_vars {
            let Some((var, _, _)) = self.candidate_occurrence_counts(var_idx, vals, &[]) else {
                continue;
            };
            let pos_occs = self.occ.get(Literal::positive(var));
            let neg_occs = self.occ.get(Literal::negative(var));
            let Some(gate) = extractor.find_gate_for_schedule_with_vals_and_marks(
                var, clauses, pos_occs, neg_occs, vals, &mut marks,
            ) else {
                continue;
            };

            let mut pos_gate = 0u64;
            let mut neg_gate = 0u64;
            let pos_lit = Literal::positive(var);
            let neg_lit = Literal::negative(var);
            for clause_idx in gate.defining_clauses {
                let lits = clauses.literals(clause_idx);
                if lits.contains(&pos_lit) {
                    pos_gate += 1;
                } else if lits.contains(&neg_lit) {
                    neg_gate += 1;
                }
            }
            if pos_gate > 0 && neg_gate > 0 {
                self.schedule_gate_pair_credit[var_idx] = pos_gate.saturating_mul(neg_gate);
            }
        }
    }

    /// Update occurrence lists after successful elimination.
    ///
    /// CaDiCaL equivalent: `elim_update_removed_clause` (elim.cpp:125-134)
    /// combined with `remove_occs` (backward.cpp:198). CaDiCaL keeps
    /// separate `noccs` counters that are decremented eagerly on clause
    /// deletion, giving the elimination heap accurate scores.
    ///
    /// Z4's ElimHeap scores are computed from `occ.count()` = `occ.get().len()`.
    /// Without eager removal, deleted clauses inflate occurrence counts,
    /// making variables appear more expensive to eliminate than they are.
    /// This breaks the cascading elimination pattern: a variable whose
    /// neighbor was just eliminated (reducing its occ count) should move
    /// up in priority, but stale entries prevent the score drop.
    pub(crate) fn update_occs_after_elimination(
        &mut self,
        to_delete: &[usize],
        clauses: &ClauseArena,
    ) {
        for &c_idx in to_delete {
            if c_idx >= clauses.len() || clauses.is_dead(c_idx) {
                continue;
            }
            let lits = clauses.literals(c_idx);
            self.occ.remove_clause(c_idx, lits);
        }
    }

    /// Fill `buf` with clause indices satisfied by a newly-true literal.
    ///
    /// CaDiCaL elim_propagate (elim.cpp:190-197): walks the positive occ list
    /// and marks satisfied clauses as garbage. The caller deletes them via
    /// `delete_clause_checked`, which garbage-marks the header; stale occ
    /// entries are tolerated by all iteration sites (lazy removal).
    ///
    /// Takes a reusable buffer to avoid per-call heap allocation (#5085).
    pub(crate) fn satisfied_clauses_into(
        &self,
        lit: Literal,
        clauses: &ClauseArena,
        buf: &mut Vec<usize>,
    ) {
        buf.clear();
        buf.extend(
            self.occ
                .get(lit)
                .iter()
                .copied()
                .filter(|&c_idx| c_idx < clauses.len() && !clauses.is_dead(c_idx)),
        );
    }
}
