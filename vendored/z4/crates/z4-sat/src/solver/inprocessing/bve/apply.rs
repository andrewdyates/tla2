// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Applies one successful BVE elimination result to solver state.

use super::super::super::mutate::{AddResult, ReasonPolicy, ReplaceResult};
use super::super::super::*;
use super::state::{BveBodyScratch, BveBodyStats};
use crate::bve::EliminationResult;

impl Solver {
    pub(super) fn apply_bve_elimination_result(
        &mut self,
        result: &EliminationResult,
        scratch: &mut BveBodyScratch,
        stats: &mut BveBodyStats,
        pending_gc_indices: &mut Vec<usize>,
        derived_unsat: &mut bool,
    ) {
        let var = result.variable;
        self.inproc
            .bve
            .update_occs_after_elimination(&result.to_delete, &self.arena);
        stats.total_eliminations += 1;
        self.var_lifecycle.mark_eliminated(var.index());
        self.vsids.remove_from_heap(var);

        scratch.kept_strengthened.clear();
        for strengthening in &result.strengthened {
            let clause_idx = strengthening.clause_idx;
            if !self.arena.is_active(clause_idx) {
                continue;
            }
            scratch.old_lits_buf.clear();
            scratch
                .old_lits_buf
                .extend_from_slice(self.arena.literals(clause_idx));
            let otfs_hints: Vec<u64> = if self.cold.lrat_enabled {
                let old_clause_id = self.clause_id(ClauseRef(clause_idx as u32));
                let pid = self.clause_id(ClauseRef(strengthening.pos_ante as u32));
                let nid = self.clause_id(ClauseRef(strengthening.neg_ante as u32));
                let other_ante_id = if clause_idx == strengthening.pos_ante {
                    nid
                } else {
                    pid
                };
                let exclude: Vec<usize> = strengthening
                    .new_lits
                    .iter()
                    .map(|l| l.variable().index())
                    .collect();
                let chain = self.collect_level0_reason_chain(&strengthening.pruned_vars, &exclude);

                let mut h = Vec::with_capacity(2 + chain.len());
                h.extend_from_slice(&chain);
                if old_clause_id != 0 {
                    h.push(old_clause_id);
                }
                if other_ante_id != 0 && other_ante_id != old_clause_id {
                    h.push(other_ante_id);
                }
                h
            } else {
                vec![]
            };
            match self.replace_clause_with_final_hints(
                clause_idx,
                &strengthening.new_lits,
                &otfs_hints,
            ) {
                ReplaceResult::Replaced | ReplaceResult::Unit => {
                    scratch.new_lits_buf.clear();
                    scratch
                        .new_lits_buf
                        .extend_from_slice(self.arena.literals(clause_idx));
                    self.inproc.bve.notify_clause_replaced(
                        clause_idx,
                        &scratch.old_lits_buf,
                        &scratch.new_lits_buf,
                    );
                    pending_gc_indices.push(clause_idx);
                    let pos_lit = Literal::positive(var);
                    let neg_lit = Literal::negative(var);
                    let pivot_in_old = scratch
                        .old_lits_buf
                        .iter()
                        .find(|&&l| l == pos_lit || l == neg_lit)
                        .copied();
                    if let Some(pivot) = pivot_in_old {
                        scratch.otfs_old_clauses.push((
                            clause_idx,
                            pivot,
                            scratch.old_lits_buf.clone(),
                        ));
                    }
                    scratch.kept_strengthened.push(clause_idx);
                }
                ReplaceResult::Empty => {
                    *derived_unsat = true;
                    break;
                }
                ReplaceResult::Skipped => {}
            }
        }
        scratch.kept_strengthened.sort_unstable();

        if *derived_unsat {
            return;
        }

        if let Some(ref writer) = self.cold.diagnostic_trace {
            writer.emit_var_transition(
                var.0,
                crate::diagnostic_trace::VarState::Active,
                crate::diagnostic_trace::VarState::Eliminated,
                self.cold.diagnostic_pass,
            );
        }

        for entry in &result.witness_entries {
            let idx = entry.clause_idx;
            if scratch.kept_strengthened.binary_search(&idx).is_ok() {
                continue;
            }
            // CaDiCaL pushes ALL defining clauses onto the extension stack
            // before any deletion (external.cpp:55-69, elim.cpp:628-670).
            // Z4 must do the same: a prior variable's elim_propagate may have
            // deleted this clause, but we still need its literals for
            // reconstruction. Use literals_or_deleted() to recover literals
            // from garbage-marked arena slots (#5059).
            let lits = self.arena.literals_or_deleted(idx);
            if lits.is_empty() {
                continue;
            }
            let ext_witness = self.externalize(entry.witness);
            let ext_lits = self.externalize_lits(lits);
            self.inproc
                .reconstruction
                .push_witness_clause(vec![ext_witness], ext_lits);
        }
        // CaDiCaL (elim.cpp:628): for gated eliminations, only gate clauses
        // go on the reconstruction stack. OTFS-strengthened clauses must also
        // respect this filter — pushing non-gate old clauses causes
        // reconstruction oscillation (#dMATH/1).
        let witness_idx_set: std::collections::HashSet<usize> = result
            .witness_entries
            .iter()
            .map(|e| e.clause_idx)
            .collect();
        for &(otfs_clause_idx, pivot, ref old_lits) in &scratch.otfs_old_clauses {
            if !witness_idx_set.contains(&otfs_clause_idx) {
                continue;
            }
            let ext_witness = self.externalize(pivot);
            let ext_lits = self.externalize_lits(old_lits);
            self.inproc
                .reconstruction
                .push_witness_clause(vec![ext_witness], ext_lits);
        }
        scratch.otfs_old_clauses.clear();

        let trail_before_resolvents = self.trail.len();

        for (resolvent, pos_ante, neg_ante, pruned_vars) in &result.resolvents {
            let hints = if self.cold.lrat_enabled {
                let pos_id = self.clause_id(ClauseRef(*pos_ante as u32));
                let neg_id = self.clause_id(ClauseRef(*neg_ante as u32));
                debug_assert!(
                    pos_id != 0,
                    "BUG: BVE positive antecedent clause (arena offset {pos_ante}) has LRAT ID 0. \
                     Resolvent: {resolvent:?}, var: {var:?}",
                );
                debug_assert!(
                    neg_id != 0,
                    "BUG: BVE negative antecedent clause (arena offset {neg_ante}) has LRAT ID 0. \
                     Resolvent: {resolvent:?}, var: {var:?}",
                );
                let exclude: Vec<usize> = resolvent.iter().map(|l| l.variable().index()).collect();
                let chain_hints = self.collect_level0_reason_chain(pruned_vars, &exclude);

                let mut hints_vec: Vec<u64> = Vec::with_capacity(2 + chain_hints.len());
                hints_vec.extend_from_slice(&chain_hints);
                hints_vec.push(neg_id);
                hints_vec.push(pos_id);
                hints_vec.retain(|&h| h != 0);
                hints_vec
            } else {
                Vec::new()
            };

            if resolvent.is_empty() {
                *derived_unsat = true;
                self.mark_empty_clause_with_hints(&hints);
                continue;
            }

            debug_assert!(
                !resolvent.iter().any(|l| l.variable() == var),
                "BUG: BVE resolvent contains eliminated variable {var:?}",
            );
            debug_assert!(
                !resolvent.iter().any(|l| resolvent.contains(&l.negated())),
                "BUG: BVE resolvent is a tautology (contains l and ~l)",
            );

            if let Ok(new_id) =
                self.proof_emit_add_prechecked(resolvent, &hints, ProofAddKind::Derived)
            {
                if self.cold.lrat_enabled && new_id != 0 {
                    self.cold.next_clause_id = new_id;
                }
            }

            scratch.add_buf.clear();
            scratch.add_buf.extend_from_slice(resolvent);
            let add_result = self.add_clause_watched(&mut scratch.add_buf);

            match add_result {
                AddResult::Added(cref) | AddResult::Unit(cref) => {
                    let clause_idx = cref.0 as usize;
                    scratch.new_lits_buf.clear();
                    scratch
                        .new_lits_buf
                        .extend_from_slice(self.arena.literals(clause_idx));
                    self.inproc
                        .bve
                        .notify_resolvent_added(clause_idx, &scratch.new_lits_buf);
                    self.inproc
                        .bve
                        .update_schedule_after_clause_addition(&scratch.new_lits_buf);
                    // Keep the resolvent for a later subsume pass, but do not
                    // let fresh same-round BVE resolvents cascade into
                    // backward subsumption or strengthening (#7916).
                    self.mark_subsume_dirty_if_kept(clause_idx);
                    stats.resolvents_total += 1;
                }
                AddResult::Empty => {}
            }

            if self.has_empty_clause {
                *derived_unsat = true;
            }
        }

        for &c_idx in &result.satisfied_parents {
            scratch.old_lits_buf.clear();
            scratch
                .old_lits_buf
                .extend_from_slice(self.arena.literals(c_idx));
            self.delete_clause_checked(c_idx, ReasonPolicy::ClearLevel0);
            self.inproc.bve.update_schedule_after_clause_removal(
                &scratch.old_lits_buf,
                var,
                &self.vals,
                &self.cold.freeze_counts,
            );
        }

        for &clause_idx in &result.to_delete {
            if scratch.kept_strengthened.binary_search(&clause_idx).is_ok() {
                continue;
            }
            scratch.old_lits_buf.clear();
            scratch
                .old_lits_buf
                .extend_from_slice(self.arena.literals(clause_idx));
            self.delete_clause_checked(clause_idx, ReasonPolicy::ClearLevel0);
            self.inproc.bve.update_schedule_after_clause_removal(
                &scratch.old_lits_buf,
                var,
                &self.vals,
                &self.cold.freeze_counts,
            );
        }

        if !*derived_unsat
            && self.elim_propagate(
                trail_before_resolvents,
                var,
                &mut scratch.old_lits_buf,
                &mut scratch.sat_buf,
            )
        {
            *derived_unsat = true;
        }

        // Do not backward-subsume or strengthen with BVE resolvents inside the
        // current elimination round. A resolvent used as a subsumer here can be
        // deleted by a later variable elimination in the same round, making the
        // dropped clause needed again. This is the same soundness hazard as the
        // in-resolution resolvent subsumption removed for #7916.
    }
}
