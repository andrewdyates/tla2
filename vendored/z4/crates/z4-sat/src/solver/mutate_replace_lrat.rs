// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LRAT hint computation for clause replacement.
//!
//! Contains `replace_clause_impl` (computes LRAT hint chains from level-0
//! reason graphs) and `collect_level0_reason_chain` (BFS transitive closure
//! over level-0 variables for explicit hint construction).
//!
//! Extracted from `mutate_replace.rs` to keep each file under 500 lines.
//! The core replacement API (wrappers, `replace_clause_core`) remains in
//! `mutate_replace.rs`.

use super::*;
use crate::solver::mutate::ReplaceResult;

impl Solver {
    /// Collect transitive level-0 reason chain for LRAT hint construction.
    ///
    /// BFS through level-0 reason clauses starting from `seed_vars`, excluding
    /// variables in `exclude_vars` (which are already in the new clause). Returns
    /// proof IDs in trail-forward order (LRAT checker processing order).
    ///
    /// CaDiCaL reference: elim.cpp:303-308,349-350 (#5026).
    pub(super) fn collect_level0_reason_chain(
        &mut self,
        seed_vars: &[usize],
        exclude_vars: &[usize],
    ) -> Vec<u64> {
        if !self.cold.lrat_enabled {
            return Vec::new();
        }
        let num_vars = self.num_vars;
        debug_assert!(self.min.lrat_to_clear.is_empty());

        // Mark excluded variables (in new clause — checker already knows them).
        for &vi in exclude_vars {
            if vi < num_vars {
                self.min.minimize_flags[vi] |= LRAT_B;
            }
        }

        // Phase 1: Seed the BFS with the given variables.
        for &vi in seed_vars {
            if vi < num_vars
                && self.var_data[vi].level == 0
                && self.has_any_proof_id(vi)
                && self.min.minimize_flags[vi] & (LRAT_A | LRAT_B) == 0
            {
                self.min.minimize_flags[vi] |= LRAT_A;
                self.min.lrat_to_clear.push(vi);
            }
        }

        // Phase 2: BFS transitive closure on level-0 variables.
        let mut head = 0;
        while head < self.min.lrat_to_clear.len() {
            let vi = self.min.lrat_to_clear[head];
            head += 1;
            let Some(reason_ref) = self.var_reason(vi) else {
                continue;
            };
            let ci = reason_ref.0 as usize;
            if ci >= self.arena.len() {
                continue;
            }
            let clen = self.arena.len_of(ci);
            for li in 0..clen {
                let rl = self.arena.literal(ci, li);
                let rv = rl.variable().index();
                if rv != vi
                    && rv < num_vars
                    && self.var_data[rv].level == 0
                    && self.min.minimize_flags[rv] & (LRAT_A | LRAT_B) == 0
                    && self.has_any_proof_id(rv)
                {
                    self.min.minimize_flags[rv] |= LRAT_A;
                    self.min.lrat_to_clear.push(rv);
                }
            }
        }

        // Phase 3: Collect proof IDs in trail-forward order (LRAT checker
        // processing order). Earlier trail variables are dependencies of later
        // ones, so they must appear first in the hint chain.
        let mut hints = Vec::new();
        let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        for i in 0..level0_end {
            let lit = self.trail[i];
            let var_idx = lit.variable().index();
            if var_idx < num_vars && self.min.minimize_flags[var_idx] & LRAT_A != 0 {
                if let Some(id) = self.level0_var_proof_id(var_idx) {
                    Self::push_lrat_hint(&mut hints, id);
                }
            }
        }

        // Sparse cleanup.
        for &idx in &self.min.lrat_to_clear {
            self.min.minimize_flags[idx] &= !LRAT_A;
        }
        self.min.lrat_to_clear.clear();
        for &vi in exclude_vars {
            if vi < num_vars {
                self.min.minimize_flags[vi] &= !LRAT_B;
            }
        }

        hints
    }

    pub(super) fn replace_clause_impl(
        &mut self,
        clause_idx: usize,
        new_lits: &[Literal],
        extra_lrat_hints: &[u64],
        explicit_only: bool,
        proof_kind: ProofAddKind,
    ) -> ReplaceResult {
        // CaDiCaL clause.cpp: replacement only during inprocessing at level 0.
        // Soundness-critical: replacing at higher levels corrupts solver state (#4560).
        assert_eq!(
            self.decision_level, 0,
            "BUG: replace_clause_checked at decision level {}",
            self.decision_level,
        );
        // Replacement must produce a non-growing clause.
        // Soundness-critical: empty replacement should use delete_clause_checked (#4560).
        debug_assert!(
            !new_lits.is_empty(),
            "BUG: replace_clause_checked with empty new_lits (use delete instead)",
        );
        // No duplicate variables in the replacement (CaDiCaL subsume.cpp pattern).
        // Soundness-critical: duplicates break 2WL invariant (#4560).
        debug_assert!(
            {
                let mut vars: Vec<u32> = new_lits.iter().map(|l| l.variable().0).collect();
                vars.sort_unstable();
                vars.windows(2).all(|w| w[0] != w[1])
            },
            "BUG: replace_clause_checked: duplicate variables in new_lits for clause {clause_idx}",
        );
        // All literal variables must be in range.
        // Soundness-critical: out-of-range causes silent corruption (#4560).
        // MUST be assert!() not debug_assert!() — see #5141.
        assert!(
            new_lits
                .iter()
                .all(|l| l.variable().index() < self.num_vars),
            "BUG: replace_clause_checked: literal variable out of range (num_vars={})",
            self.num_vars,
        );
        if !self.arena.is_active(clause_idx) {
            return ReplaceResult::Skipped;
        }
        let was_irredundant = !self.arena.is_learned(clause_idx);
        // New clause must not be longer than original (CaDiCaL subsume.cpp:84).
        // Soundness-critical: growing a clause overwrites adjacent arena memory (#4560).
        // O(1) check — must be assert!() because arena overwrite is silent corruption.
        assert!(
            new_lits.len() <= self.arena.len_of(clause_idx),
            "BUG: replace_clause_checked: new_lits ({}) longer than original ({}) at clause {clause_idx}",
            new_lits.len(),
            self.arena.len_of(clause_idx),
        );

        // CaDiCaL has zero reason-clause protection during level-0 inprocessing.
        // At level 0, replacement is in-place (same arena slot) so the ClauseRef
        // remains valid as a reason reference (#5237, R1:1113).

        // Reorder literals for optimal watch placement (#3812).
        // Without this, after strengthening/BVE the first two literals may both
        // be falsified at low levels, causing BCP to miss unit propagations.
        let mut reordered = new_lits.to_vec();
        let watched =
            self.prepare_watched_literals(&mut reordered, WatchOrderPolicy::AssignmentScore);

        // Proof logging: add-before-delete ordering (DRAT/LRAT requirement)
        let clause_ref = ClauseRef(clause_idx as u32);
        let old_clause_id = self.clause_id(clause_ref);
        let old_lits: Vec<Literal> = self.arena.literals(clause_idx).to_vec();
        let proof_hints = if self.cold.lrat_enabled {
            // Materialize unit proof IDs for level-0 variables so that
            // level0_var_proof_id() (used by collect_level0_unit_chain) can
            // find them in LRAT mode (#7108).
            self.ensure_level0_unit_proof_ids();
            let mut hints = Vec::with_capacity(old_lits.len() + extra_lrat_hints.len() + 1);
            // Count how many literals were removed.  This determines where the
            // original clause goes in the hint chain (#4398):
            //
            //   removed == 1: old clause is immediately unit under RUP negation
            //     (all new-clause literals FALSE, one removed literal unassigned).
            //     Push it LAST in pre-reversal → FIRST after reversal.  This lets
            //     the checker propagate the removed variable before any hint that
            //     references it.
            //
            //   removed > 1: old clause has multiple unassigned literals.  Push it
            //     FIRST in pre-reversal → LAST after reversal.  The probe chain
            //     must establish removed-variable values first.
            let removed_count = old_lits.len().saturating_sub(reordered.len());
            let old_clause_first_in_checker = removed_count <= 1;

            if !old_clause_first_in_checker {
                Self::push_lrat_hint(&mut hints, old_clause_id);
            }
            // Include explicitly captured reason chain (vivify probe chain,
            // subsumption hints, etc.).  After reversal these appear before
            // the old clause in the checker's processing order.
            for &hint in extra_lrat_hints {
                if hint != old_clause_id {
                    Self::push_lrat_hint(&mut hints, hint);
                }
            }
            // Include transitive level-0 reason chain for removed literals (#4398).
            // When a literal is removed from a clause at level 0, the LRAT checker
            // needs the full reason chain (not just direct reasons) for those
            // variables: their reason clauses may reference other level-0 variables
            // whose own reasons must also appear in the hint chain. Without this
            // transitive closure, lrat-check fails with "multiple literals
            // unassigned in hint" because intermediate variables are unknown.
            //
            // Skipped when explicit_only=true: subsumption strengthening provides
            // the complete hint chain (subsumer + original) and level-0 reasons
            // for the removed literal are irrelevant to the derivation.
            if !explicit_only {
                let num_vars = self.num_vars;
                // Reuse solver workspace instead of per-call Vec allocations (#5075).
                // LRAT_A in minimize_flags = needed_level0, LRAT_B = in_new_clause,
                // lrat_to_clear = BFS queue + sparse cleanup list.
                debug_assert!(self.min.lrat_to_clear.is_empty());

                // Variables in the new clause are already known to the RUP checker
                // (it negates them as the starting assignment). Including their
                // reason chains would produce "hint already satisfied" errors in
                // lrat-check because their literals are always true/false from
                // the initial negation.
                for &lit in &reordered {
                    let vi = lit.variable().index();
                    if vi < num_vars {
                        self.min.minimize_flags[vi] |= LRAT_B;
                    }
                }

                // Phase 1: Mark removed-literal variables at level 0 with reasons.
                // Include ClearLevel0 victims whose reason was cleared by BVE but
                // whose proof ID is preserved in level0_proof_id (#4617, #5014).
                // Seed variables are pushed into lrat_to_clear (BFS queue).
                for &old_lit in &old_lits {
                    if reordered.contains(&old_lit) {
                        continue;
                    }
                    let var_idx = old_lit.variable().index();
                    if var_idx < num_vars
                        && self.var_data[var_idx].level == 0
                        && self.has_any_proof_id(var_idx)
                        && self.min.minimize_flags[var_idx] & LRAT_A == 0
                    {
                        self.min.minimize_flags[var_idx] |= LRAT_A;
                        self.min.lrat_to_clear.push(var_idx);
                    }
                }

                // BFS transitive closure + reverse trail scan via shared method.
                // LRAT_A (seeds) and LRAT_B (exclusions) are already set.
                // Skip old_clause_id — it is positioned separately above/below
                // based on removed_count.
                let unit_chain = self.collect_level0_unit_chain();
                for &id in &unit_chain {
                    if id != old_clause_id {
                        Self::push_lrat_hint(&mut hints, id);
                    }
                }

                // Cleanup LRAT_B (exclusion markers for new clause vars).
                for &lit in &reordered {
                    let vi = lit.variable().index();
                    if vi < num_vars {
                        self.min.minimize_flags[vi] &= !LRAT_B;
                    }
                }
            }
            // For single-removal: push old clause LAST in pre-reversal so it
            // becomes FIRST after reversal (immediately unit under RUP negation).
            // For multi-removal: old clause was already pushed first.
            if old_clause_first_in_checker {
                Self::push_lrat_hint(&mut hints, old_clause_id);
            }
            Self::lrat_reverse_hints(&hints)
        } else if old_clause_id != 0 {
            vec![old_clause_id]
        } else {
            Vec::new()
        };

        let mut replacement_clause_id = None;
        // Forward check + proof emit: add clause, then delete old (#4564).
        if let Ok(new_id) = self.proof_emit_add(&reordered, &proof_hints, proof_kind) {
            // Guard: LRAT returns Ok(0) as a no-op sentinel after I/O
            // failure (CaDiCaL-style). Do NOT update clause ID state
            // with this sentinel -- it would corrupt clause_ids and
            // next_clause_id. See #4434.
            if self.cold.lrat_enabled && new_id != 0 {
                replacement_clause_id = Some(new_id);
            }
        }
        // Fix #6270: Before deleting old_clause_id, check if any variable's
        // unit_proof_id references it. If so, re-derive the unit using the
        // replacement clause ID, preventing stale LRAT hint references.
        if self.cold.lrat_enabled && old_clause_id != 0 {
            for &lit in &old_lits {
                let vi = lit.variable().index();
                if vi < self.unit_proof_id.len()
                    && self.unit_proof_id[vi] == old_clause_id
                    && self.var_data[vi].level == 0
                {
                    // The old clause is about to be deleted. Re-derive the unit
                    // from the replacement clause (which has already been added).
                    if let Some(new_id) = replacement_clause_id {
                        let unit_id = self
                            .proof_emit_add(&[lit], &[new_id], ProofAddKind::Derived)
                            .unwrap_or(0);
                        if unit_id != 0 {
                            self.unit_proof_id[vi] = unit_id;
                        }
                    }
                }
            }
        }
        // Delete old clause unconditionally (CaDiCaL: always emit delete
        // for replaced clause regardless of add outcome).
        let _ = self.proof_emit_delete(&old_lits, old_clause_id);

        self.clear_level0_reasons_removed_by_replacement(
            clause_idx,
            &old_lits,
            &reordered,
            old_clause_id,
        );

        // Keep clause-ID mapping synchronized with LRAT writer IDs.
        if let Some(new_clause_id) = replacement_clause_id {
            debug_assert!(
                new_clause_id != 0,
                "BUG: LRAT sentinel 0 leaked into clause ID update (#4434)"
            );
            debug_assert!(
                clause_idx < self.cold.clause_ids.len(),
                "BUG: clause_idx {} missing LRAT ID slot (clause_ids len={})",
                clause_idx,
                self.cold.clause_ids.len()
            );
            self.cold.clause_ids[clause_idx] = new_clause_id;
            // Do NOT advance next_clause_id here (#5239). Replacement
            // clauses get their IDs from the proof writer. Derived clauses
            // sync next_clause_id from the writer in add_learned_clause.

            // Propagate replacement clause + resolution hints to clause_trace
            // (#4124). The proof_manager already has the LRAT step; the
            // clause_trace needs a matching entry for SMT proof reconstruction.
            if let Some(ref mut trace) = self.cold.clause_trace {
                trace.add_clause_with_hints(
                    new_clause_id,
                    reordered.clone(),
                    false,
                    proof_hints.clone(),
                );
            }
        }

        // SAT diagnostic trace: clause_replace event (Wave 2, #4211)
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
        self.cold.clause_db_changes += 1; // BVE dual-signal fixpoint guard (#3416)
        if was_irredundant {
            self.mark_factor_candidates_dirty_clause(&reordered);
        }

        // Online witness check: shrunken/replaced clauses must remain satisfied
        // by the solution witness. CaDiCaL parity: check_solution_on_shrunken_clause.
        self.check_solution_on_replaced_clause(&reordered);

        // Add new watches based on new clause size
        if let Some((lit0, lit1)) = watched {
            self.attach_clause_watches(clause_ref, (lit0, lit1), reordered.len() == 2);
            ReplaceResult::Replaced
        } else if reordered.len() == 1 {
            // Unit clause: enqueue immediately for propagation.
            let unit_lit = reordered[0];
            match self.lit_value(unit_lit) {
                Some(true) => {
                    // Already satisfied — no action needed
                }
                Some(false) => {
                    // Contradiction at decision level 0: derive empty clause
                    // from replacement clause + assignment reason (#5236 Gap 1).
                    // Use BFS transitive closure for complete LRAT chain (#7108).
                    if self.cold.lrat_enabled {
                        let cid = self.clause_id(clause_ref);
                        let var_idx = unit_lit.variable().index();
                        let hints =
                            self.collect_empty_clause_hints_for_unit_contradiction(cid, var_idx);
                        self.mark_empty_clause_with_hints(&hints);
                    } else {
                        self.mark_empty_clause();
                    }
                    return ReplaceResult::Empty;
                }
                None => {
                    // Unit clause from literal replacement: reason=None (#6257).
                    // Store proof ID for LRAT and clause-trace (#6368).
                    if let Some(pid) = replacement_clause_id {
                        let vi = unit_lit.variable().index();
                        self.unit_proof_id[vi] = pid;
                    }
                    self.enqueue(unit_lit, None);
                }
            }
            ReplaceResult::Unit
        } else {
            // Empty replacement → UNSAT. Derive empty clause with the
            // replacement clause ID as hint (#5236 Gap 1).
            if self.cold.lrat_enabled {
                let cid = self.clause_id(clause_ref);
                let hints: Vec<u64> = if cid != 0 { vec![cid] } else { Vec::new() };
                self.mark_empty_clause_with_hints(&hints);
            } else {
                self.mark_empty_clause();
            }
            ReplaceResult::Empty
        }
    }
}
