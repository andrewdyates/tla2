// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scope management (push/pop), reset, and structural snapshots for LRA.
//!
//! Incremental push/pop with trail-based bound restoration, full/soft
//! reset, and structural snapshot export/import. Constructor, config,
//! and initialization are in `lifecycle`.

use super::*;

impl LraSolver {
    pub(crate) fn push_inner(&mut self) {
        trace!(target: "z4::lra", depth = self.scopes.len() + 1, "push");
        self.scopes
            .push((self.trail.len(), self.asserted_trail.len()));
        self.disequality_trail_scopes
            .push(self.disequality_trail.len());
        self.shared_disequality_trail_scopes
            .push(self.shared_disequality_trail.len());
        self.persistent_unsupported_scope_marks
            .push(self.persistent_unsupported_trail.len());
        self.last_simplex_feasible_scopes
            .push(self.last_simplex_feasible);
    }

    pub(crate) fn pop_inner(&mut self) {
        let Some((trail_mark, asserted_mark)) = self.scopes.pop() else {
            return;
        };
        trace!(target: "z4::lra", depth = self.scopes.len(), "pop");

        // Track which variables had bounds restored during trail replay.
        // Used for targeted touched-row marking below (#8900).
        let mut changed_vars: SmallVec<[u32; 16]> = SmallVec::new();
        while self.trail.len() > trail_mark {
            let (var, which_bound, old_value) = self.trail.pop().unwrap();
            if (var as usize) < self.vars.len() {
                changed_vars.push(var);
                match which_bound {
                    BoundType::Lower => self.vars[var as usize].lower = old_value,
                    BoundType::Upper => self.vars[var as usize].upper = old_value,
                }
            }
        }
        let mut unasserted_atoms: Vec<TermId> = Vec::new();
        while self.asserted_trail.len() > asserted_mark {
            if let Some(key) = self.asserted_trail.pop() {
                if let Some(&val) = self.asserted.get(&key) {
                    self.bound_atoms.remove(&(key, val));
                }
                self.asserted.remove(&key);
                unasserted_atoms.push(key);
            }
        }
        if let Some(diseq_mark) = self.disequality_trail_scopes.pop() {
            self.disequality_trail.truncate(diseq_mark);
        }
        if let Some(shared_diseq_mark) = self.shared_disequality_trail_scopes.pop() {
            self.shared_disequality_trail.truncate(shared_diseq_mark);
        }
        self.pending_diseq_splits.clear();
        self.propagated_equality_pairs.clear();
        self.pending_equalities.clear();
        self.fixed_term_value_table.clear();
        self.fixed_term_value_members.clear();
        self.pending_fixed_term_equalities.clear();
        self.pending_offset_equalities.clear();
        self.pending_propagations.clear();
        self.pending_bound_refinements.clear();
        self.propagated_atoms.clear();
        self.propagation_dirty_vars.clear();
        // #8003: Targeted propagation dirty marking on pop. Instead of
        // marking ALL atom_index+compound_use_index vars as dirty (O(total_vars)),
        // only mark variables whose bounds actually changed. Atoms referencing
        // unchanged variables would compute the same intervals. The DPLL layer
        // handles backtracking of previously-propagated literals.
        //
        // Fallback to full scan when many vars changed (>25% of total) to
        // avoid O(changed * neighbors) being worse than O(total).
        if changed_vars.len() * 4 >= self.vars.len() || changed_vars.is_empty() {
            self.propagation_dirty_vars
                .extend(self.atom_index.keys().copied());
            self.propagation_dirty_vars
                .extend(self.compound_use_index.keys().copied());
        } else {
            for &var in &changed_vars {
                if self.atom_index.contains_key(&var) {
                    self.propagation_dirty_vars.insert(var);
                }
                if self.compound_use_index.contains_key(&var) {
                    self.propagation_dirty_vars.insert(var);
                }
                // Also mark compound slack vars that reference this changed var,
                // since their intervals depend on it.
                if let Some(compounds) = self.compound_use_index.get(&var) {
                    for cref in compounds {
                        self.propagation_dirty_vars.insert(cref.slack);
                    }
                }
            }
        }
        self.implied_bounds.clear();
        self.var_bound_gen.clear();
        self.row_computed_gen.clear();
        self.infeasible_heap.clear();
        for b in self.in_infeasible_heap.iter_mut() {
            *b = false;
        }
        self.heap_stale = true;
        self.trivial_conflict = None;
        self.injected_to_int_axioms.clear();
        self.last_check_trail_pos = self.asserted_trail.len();
        self.bounds_tightened_since_simplex = true;
        self.direct_bounds_changed_since_implied = true;
        self.direct_bounds_changed_vars.clear();
        // #7772 F1: Reset Bland mode on pop. If Bland's rule was activated
        // during a pushed scope's simplex solve (due to basis cycling), the
        // anti-cycling flag should not persist into the outer scope where it
        // would unnecessarily slow down pivot selection. While simplex already
        // resets these at the start of solve_feasibility(), clearing them here
        // prevents stale state from affecting other code paths.
        self.bland_mode = false;
        self.basis_repeat_count = 0;
        if let Some(prev) = self.last_simplex_feasible_scopes.pop() {
            self.last_simplex_feasible = prev;
        }
        if let Some(mark) = self.persistent_unsupported_scope_marks.pop() {
            self.rewind_persistent_unsupported_atoms(mark);
        }
        self.dirty = true;
        // #8900: Targeted touched-row marking on pop.
        // Instead of marking ALL rows as touched (O(rows)), only mark rows
        // containing variables whose bounds changed. This reduces the work
        // for compute_implied_bounds() on the next check() call from
        // O(total_rows) to O(affected_rows). Cascading is handled by
        // compute_implied_bounds()'s own touched_rows seeding at the end.
        self.touched_rows.clear();
        if changed_vars.is_empty() {
            // No bounds changed — no rows to touch.
        } else if changed_vars.len() * 4 >= self.vars.len() {
            // Many variables changed — mark all rows.
            for i in 0..self.rows.len() {
                self.touched_rows.insert(i);
            }
        } else {
            for &var in &changed_vars {
                let vi = var as usize;
                if vi < self.col_index.len() {
                    for &ri in &self.col_index[vi] {
                        self.touched_rows.insert(ri);
                    }
                }
                if let Some(&ri) = self.basic_var_to_row.get(&var) {
                    self.touched_rows.insert(ri);
                }
            }
        }
        self.propagate_direct_touched_rows_pending = false;
        for atom_term in unasserted_atoms {
            if let Some(Some(info)) = self.atom_cache.get(&atom_term).cloned() {
                if !info.is_eq && !info.is_distinct {
                    for &(v, _) in &info.expr.coeffs {
                        let vi = v as usize;
                        if vi < self.unassigned_atom_count.len() {
                            self.unassigned_atom_count[vi] += 1;
                        }
                    }
                    if info.expr.coeffs.len() > 1 {
                        let mut key: Vec<_> = info
                            .expr
                            .coeffs
                            .iter()
                            .map(|(v, c)| (*v, c.clone()))
                            .collect();
                        key.sort_by_key(|(v, _)| *v);
                        let key_rat: Vec<(u32, Rational)> = key.iter().map(|(v, c)| (*v, Rational::from(c))).collect();
                        if let Some(&(slack, _)) = self.expr_to_slack.get(&key_rat) {
                            let si = slack as usize;
                            if si < self.unassigned_atom_count.len() {
                                self.unassigned_atom_count[si] += 1;
                            }
                        }
                    }
                }
            }
        }
    }

    pub(crate) fn reset_inner(&mut self) {
        if self.debug_lra_reset {
            safe_eprintln!(
                "[LRA_RESET] reset() called, clearing {} vars, term_to_var has {} entries",
                self.vars.len(),
                self.term_to_var.len()
            );
            for (i, info) in self.vars.iter().enumerate() {
                safe_eprintln!(
                    "[LRA_RESET]   var {}: lb={:?}, ub={:?}",
                    i,
                    info.lower.as_ref().map(|b| &b.value),
                    info.upper.as_ref().map(|b| &b.value)
                );
            }
        }
        self.rows.clear();
        self.vars.clear();
        self.col_index.clear();
        self.term_to_var.clear();
        self.var_to_term.clear();
        self.next_var = 0;
        self.trail.clear();
        self.scopes.clear();
        self.asserted.clear();
        self.asserted_trail.clear();
        self.atom_cache.clear();
        self.not_inner_cache.clear();
        self.const_bool_cache.clear();
        self.refinement_eligible_cache.clear();
        self.is_integer_sort_cache.clear();
        self.bound_atoms.clear();
        self.atom_slack.clear();
        self.expr_to_slack.clear();
        self.propagated_atoms.clear();
        self.propagation_dirty_vars.clear();
        self.var_to_atoms.clear();
        self.implied_bounds.clear();
        self.var_bound_gen.clear();
        self.row_computed_gen.clear();
        self.persistent_unsupported_atoms.clear();
        self.persistent_unsupported_trail.clear();
        self.persistent_unsupported_scope_marks.clear();
        self.dirty = true;
        self.last_check_trail_pos = 0;
        self.bounds_tightened_since_simplex = true;
        self.direct_bounds_changed_since_implied = true;
        self.direct_bounds_changed_vars.clear();
        self.last_simplex_feasible = false;
        self.last_simplex_feasible_scopes.clear();
        self.rows_at_check_start = 0;
        self.pending_equalities.clear();
        self.propagated_equality_pairs.clear();
        self.fixed_term_value_table.clear();
        self.fixed_term_value_members.clear();
        self.pending_fixed_term_equalities.clear();
        self.pending_offset_equalities.clear();
        self.trivial_conflict = None;
        self.to_int_terms.clear();
        self.injected_to_int_axioms.clear();
        self.basic_var_to_row.clear();
        self.touched_rows.clear();
        self.propagate_direct_touched_rows_pending = false;
        self.unassigned_atom_count.clear();
        self.registered_atoms.clear();
        self.atom_index.clear();
        self.compound_use_index.clear();
        self.pending_propagations.clear();
        self.pending_bound_refinements.clear();
        self.last_compound_propagations_queued = 0;
        self.last_compound_wake_dirty_hits = 0;
        self.last_compound_wake_candidates = 0;
        self.infeasible_heap.clear();
        self.in_infeasible_heap.clear();
        self.heap_stale = true;
        self.disequality_trail.clear();
        self.disequality_trail_scopes.clear();
        self.shared_disequality_trail.clear();
        self.shared_disequality_trail_scopes.clear();
        self.pending_diseq_splits.clear();
    }

    pub(crate) fn soft_reset_inner(&mut self) {
        self.asserted.clear();
        self.asserted_trail.clear();
        self.trail.clear();
        self.scopes.clear();
        self.propagated_equality_pairs.clear();
        self.pending_equalities.clear();
        self.fixed_term_value_table.clear();
        self.fixed_term_value_members.clear();
        self.pending_fixed_term_equalities.clear();
        self.pending_offset_equalities.clear();
        self.pending_propagations.clear();
        self.pending_bound_refinements.clear();
        self.propagated_atoms.clear();
        self.propagation_dirty_vars.clear();
        self.propagation_dirty_vars
            .extend(self.atom_index.keys().copied());
        self.propagation_dirty_vars
            .extend(self.compound_use_index.keys().copied());
        self.last_compound_propagations_queued = 0;
        self.last_compound_wake_dirty_hits = 0;
        self.last_compound_wake_candidates = 0;
        self.implied_bounds.clear();
        self.var_bound_gen.clear();
        self.row_computed_gen.clear();
        self.trivial_conflict = None;
        self.persistent_unsupported_atoms.clear();
        self.persistent_unsupported_trail.clear();
        self.persistent_unsupported_scope_marks.clear();
        self.dirty = true;
        self.last_check_trail_pos = 0;
        self.bounds_tightened_since_simplex = true;
        self.direct_bounds_changed_since_implied = true;
        self.direct_bounds_changed_vars.clear();
        self.last_simplex_feasible = false;
        self.last_simplex_feasible_scopes.clear();
        self.rows_at_check_start = 0;
        for var_info in &mut self.vars {
            var_info.lower = None;
            var_info.upper = None;
            var_info.value = InfRational::default();
        }
        for row in &self.rows {
            let basic = row.basic_var as usize;
            if basic < self.vars.len() {
                self.vars[basic].value = InfRational::from_rational(row.constant.to_big());
            }
        }
        self.bound_atoms.clear();
        self.injected_to_int_axioms.clear();
        self.touched_rows.clear();
        for i in 0..self.rows.len() {
            self.touched_rows.insert(i);
        }
        self.propagate_direct_touched_rows_pending = false;
        self.recount_unassigned_atoms();
        self.infeasible_heap.clear();
        for b in self.in_infeasible_heap.iter_mut() {
            *b = false;
        }
        self.heap_stale = true;
        self.disequality_trail.clear();
        self.disequality_trail_scopes.clear();
        self.shared_disequality_trail.clear();
        self.shared_disequality_trail_scopes.clear();
        self.pending_diseq_splits.clear();
    }

    pub(crate) fn restore_from_structural_snapshot_inner(
        terms: &TermStore,
        snapshot: Box<dyn std::any::Any>,
    ) -> Result<Self, Box<dyn std::any::Any>> {
        Self::try_from_snapshot(terms, snapshot)
    }

    pub(crate) fn export_structural_snapshot_inner(&self) -> Option<Box<dyn std::any::Any>> {
        if self.registered_atoms.is_empty() {
            return None;
        }
        Some(Box::new(LraStructuralSnapshot {
            rows: self.rows.clone(),
            vars: self.vars.clone(),
            term_to_var: self.term_to_var.clone(),
            var_to_term: self.var_to_term.clone(),
            next_var: self.next_var,
            atom_cache: self.atom_cache.clone(),
            registered_atoms: self.registered_atoms.clone(),
            atom_index: self.atom_index.clone(),
            compound_use_index: self.compound_use_index.clone(),
            var_to_atoms: self.var_to_atoms.clone(),
            atom_slack: self.atom_slack.clone(),
            expr_to_slack: self.expr_to_slack.clone(),
            slack_var_set: self.slack_var_set.clone(),
            basic_var_to_row: self.basic_var_to_row.clone(),
            col_index: self.col_index.clone(),
            to_int_terms: self.to_int_terms.clone(),
            unassigned_atom_count: self.unassigned_atom_count.clone(),
            not_inner_cache: self.not_inner_cache.clone(),
            const_bool_cache: self.const_bool_cache.clone(),
            refinement_eligible_cache: self.refinement_eligible_cache.clone(),
            is_integer_sort_cache: self.is_integer_sort_cache.clone(),
        }))
    }

    pub(crate) fn import_structural_snapshot_inner(&mut self, snapshot: Box<dyn std::any::Any>) {
        let Ok(snap) = snapshot.downcast::<LraStructuralSnapshot>() else {
            return;
        };
        self.rows = snap.rows;
        self.vars = snap.vars;
        self.term_to_var = snap.term_to_var;
        self.var_to_term = snap.var_to_term;
        self.next_var = snap.next_var;
        self.atom_cache = snap.atom_cache;
        self.registered_atoms = snap.registered_atoms;
        self.atom_index = snap.atom_index;
        self.compound_use_index = snap.compound_use_index;
        self.var_to_atoms = snap.var_to_atoms;
        self.atom_slack = snap.atom_slack;
        self.expr_to_slack = snap.expr_to_slack;
        self.slack_var_set = snap.slack_var_set;
        self.basic_var_to_row = snap.basic_var_to_row;
        self.col_index = snap.col_index;
        self.to_int_terms = snap.to_int_terms;
        self.unassigned_atom_count = snap.unassigned_atom_count;
        self.not_inner_cache = snap.not_inner_cache;
        self.const_bool_cache = snap.const_bool_cache;
        self.refinement_eligible_cache = snap.refinement_eligible_cache;
        self.is_integer_sort_cache = snap.is_integer_sort_cache;
        self.persistent_unsupported_atoms.clear();
        self.persistent_unsupported_trail.clear();
        self.persistent_unsupported_scope_marks.clear();
        for var_info in &mut self.vars {
            var_info.lower = None;
            var_info.upper = None;
            var_info.value = InfRational::default();
        }
        for row in &self.rows {
            let basic = row.basic_var as usize;
            if basic < self.vars.len() {
                self.vars[basic].value = InfRational::from_rational(row.constant.to_big());
            }
        }
        self.touched_rows.clear();
        for i in 0..self.rows.len() {
            self.touched_rows.insert(i);
        }
        self.propagate_direct_touched_rows_pending = false;
        self.in_infeasible_heap.resize(self.vars.len(), false);
        self.heap_stale = true;
        self.propagation_dirty_vars
            .extend(self.atom_index.keys().copied());
        self.propagation_dirty_vars
            .extend(self.compound_use_index.keys().copied());
        self.recount_unassigned_atoms();
        self.dirty = true;
        self.bounds_tightened_since_simplex = true;
        self.direct_bounds_changed_since_implied = true;
        self.direct_bounds_changed_vars.clear();
    }
}
