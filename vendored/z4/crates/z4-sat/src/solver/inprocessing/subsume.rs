// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Forward and self-subsumption.

use super::super::mutate::{DeleteResult, ReasonPolicy, ReplaceResult};
use super::super::*;

impl Solver {
    #[inline]
    fn schedule_next_subsume(&mut self, made_progress: bool) {
        let (growth_numer, growth_denom, max_interval) = if made_progress {
            // Progressing rounds should run again relatively soon.
            (3, 2, SUBSUME_MAX_INTERVAL)
        } else {
            // No-op rounds are frequently net-negative on structured SAT.
            // Back off more aggressively before retrying.
            (2, 1, SUBSUME_MAX_IDLE_INTERVAL)
        };
        self.inproc_ctrl.subsume.reschedule_growing(
            self.num_conflicts,
            SUBSUME_INTERVAL,
            growth_numer,
            growth_denom,
            max_interval,
        );
    }

    /// Run CaDiCaL-style one-watch forward subsumption.
    ///
    /// Uses per-variable `subsume_dirty` bits for incremental scheduling:
    /// only clauses with >= 2 dirty variables are candidates. After a
    /// complete round, dirty bits are reset. Strengthened clauses re-mark
    /// their variables for the next round (CaDiCaL `mark_added`).
    ///
    /// REQUIRES: decision_level == 0
    /// ENSURES: subsumed clauses deleted, strengthened clauses shrunk
    pub(in crate::solver) fn subsume(&mut self) {
        if !self.enter_inprocessing() {
            return;
        }

        // Compute dynamic effort limit (CaDiCaL subsume.cpp:349-362).
        let active_vars = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed()) as u64;
        let effort = (self.num_propagations as f64 * self.cold.subsume_effort_permille as f64
            / 1000.0) as u64;
        let effort = effort.clamp(SUBSUME_MIN_EFFORT, SUBSUME_MAX_EFFORT);
        let effort = effort.max(2 * active_vars);
        self.inproc.subsumer.set_check_limit(effort);

        // Run one-watch forward subsumption with dirty bits, level-0 values,
        // and dynamic keep-set thresholds from the last reduce_db() pass.
        // CaDiCaL: likely_to_be_kept_clause gates candidate selection.
        let kept = crate::subsume::KeptThresholds {
            tier2_lbd: self.tiers.tier2_lbd[0],
            kept_glue: self.tiers.kept_glue,
            kept_size: self.tiers.kept_size,
        };
        let result = self.inproc.subsumer.run_forward_subsumption(
            &mut self.arena,
            &self.cold.freeze_counts,
            &self.subsume_dirty,
            &self.vals,
            kept,
        );
        let subsume_round = self.inproc.subsumer.stats().rounds;
        let dirty_vars = self.subsume_dirty.iter().filter(|&&dirty| dirty).count();
        tracing::debug!(
            round = subsume_round,
            effort_limit = effort,
            candidates = result.candidates_scheduled,
            checks = result.checks_performed,
            subsumed = result.subsumed.len(),
            strengthened = result.strengthened.len(),
            completed = result.completed,
            dirty_vars,
            "subsume round"
        );
        let mut made_progress = false;

        // Apply strengthening (self-subsumption) BEFORE forward subsumption
        // deletions. LRAT correctness requires that subsumer clause IDs are
        // still alive when used as resolution hints. If forward subsumption
        // deletes a clause that is also used as a subsumer for self-subsumption,
        // the batched LRAT deletion is flushed before the self-subsumption add,
        // causing "ERROR: using DELETED hint clause" (#4398).
        for (clause_idx, new_lits, subsumer_idx) in &result.strengthened {
            // For LRAT, the subsuming clause is an antecedent of the strengthened
            // clause. Include its clause ID as a resolution hint so the LRAT
            // checker can verify the derivation (#4398).
            //
            // Guard: if the subsumer was replaced/deleted earlier in this loop,
            // its old LRAT ID is pending deletion. Using the stale ID as a hint
            // causes "ERROR: using DELETED hint clause" in lrat-check (#4398).
            // Re-read the subsumer's current LRAT ID (updated by earlier
            // replace_clause_impl calls) to get the replacement's ID.
            let subsumer_hints = if self.cold.lrat_enabled {
                vec![self.clause_id(ClauseRef(*subsumer_idx as u32))]
            } else {
                Vec::new()
            };
            // Read irredundant status before replace (header may be invalidated for Unit).
            let is_irredundant = !self.arena.is_learned(*clause_idx);
            // Snapshot literals before replace for BVE dirty-candidate marking (#7905).
            let old_lits = if is_irredundant {
                Some(self.arena.literals(*clause_idx).to_vec())
            } else {
                None
            };
            match self.replace_clause_with_explicit_lrat_hints(
                *clause_idx,
                new_lits,
                &subsumer_hints,
            ) {
                ReplaceResult::Empty => {
                    self.schedule_next_subsume(true);
                    debug_assert_eq!(
                        self.decision_level, 0,
                        "BUG: subsume() did not restore decision level to 0"
                    );
                    return;
                }
                ReplaceResult::Unit | ReplaceResult::Replaced => {
                    made_progress = true;
                    // Mark per-variable dirty candidates for BVE re-trigger (#7905).
                    if is_irredundant {
                        self.note_irredundant_clause_replaced_for_bve(
                            old_lits
                                .as_deref()
                                .expect("irredundant strengthened clause snapshot"),
                            new_lits,
                        );
                    }
                }
                ReplaceResult::Skipped => {}
            }
        }

        // Apply deletions (forward-subsumed clauses) AFTER self-subsumption.
        // CaDiCaL subsume.cpp:125-149: if a redundant clause subsumes an
        // irredundant clause, promote the subsumer to irredundant first.
        for &(subsumed_idx, subsumer_idx) in &result.subsumed {
            if !self.arena.is_active(subsumed_idx) {
                continue;
            }
            let subsumed_learned = self.arena.is_learned(subsumed_idx);
            // Snapshot literals before delete for BVE dirty-candidate marking (#7905).
            let subsumed_old_lits = if !subsumed_learned {
                Some(self.arena.literals(subsumed_idx).to_vec())
            } else {
                None
            };

            // Check that the subsumer is still alive (not deleted/garbage).
            // In batched forward subsumption, an earlier iteration in this loop
            // may have deleted the subsumer. If the subsumed clause is
            // irredundant and the subsumer is gone, deleting the subsumed clause
            // would lose the constraint — the formula could become equisatisfiable
            // rather than equivalent. This is unsound. (#6913)
            let subsumer_alive = subsumer_idx < self.arena.len()
                && self.arena.is_active(subsumer_idx)
                && !self.arena.is_dead(subsumer_idx);

            if !subsumed_learned && !subsumer_alive {
                // Irredundant clause whose subsumer was deleted in this batch.
                // Skip deletion to preserve soundness.
                continue;
            }

            let subsumer_learned = subsumer_alive && self.arena.is_learned(subsumer_idx);

            if !subsumed_learned && subsumer_learned {
                // Irredundant subsumed by redundant: promote subsumer first.
                self.arena.set_learned(subsumer_idx, false);
            }

            if matches!(
                self.delete_clause_checked(subsumed_idx, ReasonPolicy::Skip),
                DeleteResult::Deleted
            ) {
                made_progress = true;
                // Mark per-variable dirty candidates for BVE re-trigger (#7905).
                if !subsumed_learned {
                    self.note_irredundant_clause_removed_for_bve(
                        subsumed_old_lits
                            .as_deref()
                            .expect("irredundant subsumed clause snapshot"),
                    );
                }
            }
        }

        // Post-condition: forward-subsumed clauses should either be deleted,
        // protected as active reason clauses, or retained because their subsumer
        // died (#6913: irredundant clauses skip deletion when subsumer is dead).
        #[cfg(debug_assertions)]
        for &(subsumed_idx, subsumer_idx) in &result.subsumed {
            if subsumed_idx >= self.arena.len() || !self.arena.is_active(subsumed_idx) {
                continue;
            }
            // If the clause is irredundant and its subsumer is dead, it was
            // intentionally kept by the #6913 soundness guard above.
            let is_irredundant = !self.arena.is_learned(subsumed_idx);
            let subsumer_dead = subsumer_idx >= self.arena.len()
                || !self.arena.is_active(subsumer_idx)
                || self.arena.is_dead(subsumer_idx);
            if is_irredundant && subsumer_dead {
                continue;
            }
            debug_assert!(
                self.is_reason_clause_marked(subsumed_idx),
                "BUG: subsume() left clause {subsumed_idx} active without reason protection"
            );
        }

        // CaDiCaL subsume.cpp:590: only reset dirty bits when the round
        // completed all scheduled candidates. Incomplete rounds (effort limit
        // hit) preserve dirty state so the next round picks up where this one
        // left off. Without this, large formulas lose incremental state and
        // subsequent rounds only see newly-added clauses (#7279).
        if result.completed {
            for v in self.subsume_dirty.iter_mut() {
                *v = false;
            }
        }
        // Re-mark variables in strengthened clauses for the next round
        // (CaDiCaL subsume.cpp:593-594: mark_added for shrunken clauses).
        for (clause_idx, new_lits, _) in &result.strengthened {
            for lit in new_lits {
                let v = lit.variable().index();
                if v < self.subsume_dirty.len() {
                    self.subsume_dirty[v] = true;
                }
            }
            if *clause_idx < self.arena.len() && self.arena.is_active(*clause_idx) {
                for &lit in self.arena.literals(*clause_idx) {
                    let v = lit.variable().index();
                    if v < self.subsume_dirty.len() {
                        self.subsume_dirty[v] = true;
                    }
                }
            }
        }

        self.schedule_next_subsume(made_progress);
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: subsume() did not restore decision level to 0"
        );
    }
}
