// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause replacement helpers for inprocessing passes.
//!
//! Split from `mutate.rs` for file-size compliance (#5142).
//! Contains the public `replace_clause_*` API wrappers, `replace_clause_core`
//! (pre-computed hints), and level-0 reason cleanup. LRAT hint computation
//! (`replace_clause_impl`, `collect_level0_reason_chain`) is in
//! `mutate_replace_lrat.rs`.

use super::*;
use crate::solver::mutate::ReplaceResult;

impl Solver {
    /// Push a non-zero LRAT hint. Duplicates are tolerated at this level
    /// because `ProofManager::emit_add` deduplicates at the output boundary
    /// before writing to the LRAT file (#5248).
    #[inline]
    pub(super) fn push_lrat_hint(hints: &mut Vec<u64>, hint: u64) {
        if hint != 0 {
            hints.push(hint);
        }
    }

    /// Clear level-0 reasons invalidated by in-place clause replacement.
    ///
    /// Replacement preserves the clause slot, so variables whose assigned
    /// literal remains in the clause can keep their reason reference. If the
    /// assigned literal was removed, the old clause no longer justifies that
    /// assignment. Clear the stale reason now so a later ClearLevel0 deletion
    /// does not miss it by scanning only the replacement literals.
    pub(super) fn clear_level0_reasons_removed_by_replacement(
        &mut self,
        clause_idx: usize,
        old_lits: &[Literal],
        new_lits: &[Literal],
        old_clause_id: u64,
    ) {
        let clause_ref = ClauseRef(clause_idx as u32);
        let mut cleared_any = false;
        if self.cold.lrat_enabled && old_clause_id != 0 {
            self.materialize_level0_unit_proofs();
        }

        for &old_lit in old_lits {
            let vi = old_lit.variable().index();
            if vi >= self.num_vars
                || self.var_data[vi].reason != clause_ref.0
                || self.var_data[vi].level != 0
            {
                continue;
            }

            let Some(val) = self.var_value_from_vals(vi) else {
                continue;
            };
            let assigned_lit = if val {
                Literal::positive(Variable(vi as u32))
            } else {
                Literal::negative(Variable(vi as u32))
            };
            if new_lits.contains(&assigned_lit) {
                continue;
            }

            if self.cold.lrat_enabled && old_clause_id != 0 {
                let mut hints = Vec::new();
                for &other_lit in old_lits {
                    if other_lit.variable().index() == vi {
                        continue;
                    }
                    let ovi = other_lit.variable().index();
                    if ovi < self.num_vars {
                        if let Some(pid) = self.level0_unit_chain_proof_id(ovi) {
                            if !hints.contains(&pid) {
                                hints.push(pid);
                            }
                        }
                    }
                }
                hints.push(old_clause_id);
                let unit_id = self
                    .proof_emit_add(&[assigned_lit], &hints, ProofAddKind::Derived)
                    .unwrap_or(0);
                if unit_id != 0 {
                    self.cold.level0_proof_id[vi] = unit_id;
                } else {
                    // Fallback: emit TrustedTransform so the variable has a
                    // unit proof ID. Storing old_clause_id (a multi-literal
                    // clause) would corrupt LRAT hint chains (#7108).
                    let tt_id = self
                        .proof_emit_add(&[assigned_lit], &[], ProofAddKind::TrustedTransform)
                        .unwrap_or(0);
                    if tt_id != 0 {
                        self.cold.level0_proof_id[vi] = tt_id;
                    }
                }
            }

            self.var_data[vi].reason = NO_REASON;
            cleared_any = true;
        }

        if cleared_any {
            self.bump_reason_graph_epoch();
        }
    }

    /// Replace a clause with new (shorter) literals, handling watches and proof logging.
    ///
    /// Implements the add-before-delete proof ordering required by DRAT.
    /// After replacement, if the clause becomes a unit, the literal is enqueued.
    /// If it becomes empty, UNSAT is marked.
    ///
    /// # Arguments
    ///
    /// * `clause_idx` - Index into the clause database.
    /// * `new_lits` - New literal set (must be shorter or equal to original).
    pub(super) fn replace_clause_checked(
        &mut self,
        clause_idx: usize,
        new_lits: &[Literal],
    ) -> ReplaceResult {
        self.replace_clause_checked_with_lrat_hints(clause_idx, new_lits, &[])
    }

    /// Replace a clause while explicitly providing additional LRAT hints.
    ///
    /// `extra_lrat_hints` is used by vivification to preserve reason-clause IDs
    /// from non-level-0 probe propagation before backtracking clears reasons.
    ///
    /// When `explicit_only` is true, the LRAT hint chain is exactly
    /// `extra_lrat_hints + [original_clause_id]` — level-0 reason collection
    /// is skipped. Used by subsumption where the derivation is purely
    /// structural (subsumer + original clause) and level-0 reasons are
    /// irrelevant (#4398).
    pub(super) fn replace_clause_checked_with_lrat_hints(
        &mut self,
        clause_idx: usize,
        new_lits: &[Literal],
        extra_lrat_hints: &[u64],
    ) -> ReplaceResult {
        self.replace_clause_impl(
            clause_idx,
            new_lits,
            extra_lrat_hints,
            false,
            ProofAddKind::Derived,
        )
    }

    /// Replace a clause with explicit LRAT hints only (no auto level-0 reasons).
    pub(super) fn replace_clause_with_explicit_lrat_hints(
        &mut self,
        clause_idx: usize,
        new_lits: &[Literal],
        explicit_hints: &[u64],
    ) -> ReplaceResult {
        self.replace_clause_impl(
            clause_idx,
            new_lits,
            explicit_hints,
            true,
            ProofAddKind::Derived,
        )
    }

    /// Replace a clause using a pre-computed, complete LRAT hint chain.
    ///
    /// Unlike `replace_clause_with_explicit_lrat_hints` (which adds old_clause_id
    /// and reverses), this takes hints already in final LRAT checker processing
    /// order. Used by BVE OTFS strengthening where the hint chain order depends
    /// on whether root-level-false literals were pruned (#5026).
    pub(super) fn replace_clause_with_final_hints(
        &mut self,
        clause_idx: usize,
        new_lits: &[Literal],
        final_hints: &[u64],
    ) -> ReplaceResult {
        self.replace_clause_core(clause_idx, new_lits, final_hints, ProofAddKind::Derived)
    }

    /// Core clause replacement with pre-computed, final LRAT hints.
    ///
    /// Takes `final_hints` already in LRAT checker processing order (no reversal,
    /// no old_clause_id insertion). Performs all validation, arena mutation, watch
    /// updates, and proof emission. Used by `replace_clause_with_final_hints`.
    fn replace_clause_core(
        &mut self,
        clause_idx: usize,
        new_lits: &[Literal],
        final_hints: &[u64],
        proof_kind: ProofAddKind,
    ) -> ReplaceResult {
        assert_eq!(
            self.decision_level, 0,
            "BUG: replace_clause_core at decision level {}",
            self.decision_level,
        );
        debug_assert!(
            !new_lits.is_empty(),
            "BUG: replace_clause_core with empty new_lits (use delete instead)",
        );
        debug_assert!(
            {
                let mut vars: Vec<u32> = new_lits.iter().map(|l| l.variable().0).collect();
                vars.sort_unstable();
                vars.windows(2).all(|w| w[0] != w[1])
            },
            "BUG: replace_clause_core: duplicate variables in new_lits for clause {clause_idx}",
        );
        assert!(
            new_lits
                .iter()
                .all(|l| l.variable().index() < self.num_vars),
            "BUG: replace_clause_core: literal variable out of range (num_vars={})",
            self.num_vars,
        );
        if !self.arena.is_active(clause_idx) {
            return ReplaceResult::Skipped;
        }
        let was_irredundant = !self.arena.is_learned(clause_idx);
        assert!(
            new_lits.len() <= self.arena.len_of(clause_idx),
            "BUG: replace_clause_core: new_lits ({}) longer than original ({}) at clause {clause_idx}",
            new_lits.len(),
            self.arena.len_of(clause_idx),
        );
        // CaDiCaL has zero reason-clause protection during level-0 inprocessing
        // (congruence.cpp, decompose.cpp, subsume.cpp all replace reason clauses
        // freely). The `c->reason` flag is only checked by `reduce` at non-zero
        // levels. At level 0, replacement is in-place (same arena slot) so the
        // ClauseRef remains valid as a reason reference (#5237, R1:1113).

        let mut reordered = new_lits.to_vec();
        let watched =
            self.prepare_watched_literals(&mut reordered, WatchOrderPolicy::AssignmentScore);

        let clause_ref = ClauseRef(clause_idx as u32);
        let old_clause_id = self.clause_id(clause_ref);
        let old_lits: Vec<Literal> = self.arena.literals(clause_idx).to_vec();

        let mut replacement_clause_id = None;
        if let Ok(new_id) = self.proof_emit_add(&reordered, final_hints, proof_kind) {
            if self.cold.lrat_enabled && new_id != 0 {
                replacement_clause_id = Some(new_id);
            }
        }

        let _ = self.proof_emit_delete(&old_lits, old_clause_id);

        self.clear_level0_reasons_removed_by_replacement(
            clause_idx,
            &old_lits,
            &reordered,
            old_clause_id,
        );

        if let Some(new_clause_id) = replacement_clause_id {
            debug_assert!(new_clause_id != 0);
            debug_assert!(clause_idx < self.cold.clause_ids.len());
            self.cold.clause_ids[clause_idx] = new_clause_id;
            // Do NOT advance next_clause_id here (#5239).
            if let Some(ref mut trace) = self.cold.clause_trace {
                trace.add_clause_with_hints(
                    new_clause_id,
                    reordered.clone(),
                    false,
                    final_hints.to_vec(),
                );
            }
        }

        if let Some(ref writer) = self.cold.diagnostic_trace {
            let dimacs_lits: Vec<i64> =
                reordered.iter().map(|l| i64::from(l.to_dimacs())).collect();
            writer.emit_clause_replace(old_clause_id, &dimacs_lits, self.cold.diagnostic_pass);
        }

        // Remove old watches
        let old_len = self.arena.len_of(clause_idx);
        if old_len >= 2 {
            let (lit0, lit1) = self.arena.watched_literals(clause_idx);
            self.remove_watch(lit0, ClauseRef(clause_idx as u32));
            self.remove_watch(lit1, ClauseRef(clause_idx as u32));
        }

        // Update the clause with reordered literals
        self.drain_pending_garbage_mark(clause_idx);
        self.arena.replace(clause_idx, &reordered);
        self.arena.set_saved_pos(clause_idx, 2);
        self.cold.clause_db_changes += 1;
        if was_irredundant {
            self.mark_factor_candidates_dirty_clause(&reordered);
        }

        self.check_solution_on_replaced_clause(&reordered);

        if let Some((lit0, lit1)) = watched {
            self.attach_clause_watches(clause_ref, (lit0, lit1), reordered.len() == 2);
            ReplaceResult::Replaced
        } else if reordered.len() == 1 {
            let unit_lit = reordered[0];
            match self.lit_value(unit_lit) {
                Some(true) => {}
                Some(false) => {
                    // Replaced clause is a unit whose literal is already false
                    // at level 0. Derive empty clause with LRAT hints (#5236).
                    // Use BFS transitive closure for complete LRAT chain (#7108).
                    if self.cold.lrat_enabled {
                        let var_idx = unit_lit.variable().index();
                        let unit_pid = replacement_clause_id.unwrap_or(0);
                        let hints = self
                            .collect_empty_clause_hints_for_unit_contradiction(unit_pid, var_idx);
                        self.mark_empty_clause_with_hints(&hints);
                    } else {
                        self.mark_empty_clause();
                    }
                    return ReplaceResult::Empty;
                }
                None => {
                    // Unit clause from strengthening: reason=None (#6257).
                    // Store proof ID for LRAT and clause-trace (#6368).
                    if let Some(pid) = replacement_clause_id {
                        let vi = unit_lit.variable().index();
                        self.unit_proof_id[vi] = pid;
                    }
                    // Minimal trail rewind (#8095): record the trail position where
                    // this new unit will be enqueued.
                    if self.decision_level == 0 {
                        self.mark_trail_affected(self.trail.len());
                    }
                    self.enqueue(unit_lit, None);
                }
            }
            ReplaceResult::Unit
        } else {
            // Clause reduced to empty after replacement. The proof step
            // was already emitted at proof_emit_add above with final_hints.
            // Use the replacement's proof ID as the hint (#5236).
            if self.cold.lrat_enabled {
                let hints: Vec<u64> = replacement_clause_id.into_iter().collect();
                self.mark_empty_clause_with_hints(&hints);
            } else {
                self.mark_empty_clause();
            }
            ReplaceResult::Empty
        }
    }

    // collect_level0_reason_chain and replace_clause_impl extracted to
    // mutate_replace_lrat.rs
}
