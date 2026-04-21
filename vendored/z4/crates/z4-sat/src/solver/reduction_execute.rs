// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause database reduction execution: flush and normal reduce paths.
//!
//! Split from `reduction.rs` for file-size compliance (#5142).
//! Contains `reduce_db` and its helper functions that execute the
//! actual deletion of learned clauses.

use super::*;

impl Solver {
    /// Check if a clause is satisfied by a literal assigned at decision level 0.
    ///
    /// Level-0 satisfied clauses are trivially true and should be excluded from
    /// reduction candidates to avoid wasting the deletion budget (#3723).
    /// Reference: CaDiCaL `clause_contains_fixed_literal()` (collect.cpp:73-88).
    fn clause_satisfied_at_level0(&self, idx: usize) -> bool {
        for &lit in self.arena.literals(idx) {
            if self.lit_val(lit) > 0 && self.var_data[lit.variable().index()].level == 0 {
                return true;
            }
        }
        false
    }

    /// Pre-reduction cleanup: delete all clauses already satisfied at level 0.
    ///
    /// Matches CaDiCaL `mark_satisfied_clauses_as_garbage()` before reduction
    /// candidate planning (collect.cpp:73-88, reduce.cpp:226). These clauses are
    /// permanently true and should not remain in the clause DB. This includes
    /// both learned and irredundant (original) clauses — a level-0-satisfied
    /// original clause is redundant and can be safely garbage-collected.
    /// Proof correctness: `delete_clause_unchecked` traces deletions for both
    /// learned and irredundant clauses via `proof_emit_delete_arena`.
    fn mark_satisfied_clauses_as_garbage(&mut self) {
        debug_assert_eq!(
            self.reason_marks_synced_epoch, self.reason_graph_epoch,
            "BUG: mark_satisfied_clauses_as_garbage called with stale reason marks",
        );
        let all_indices: Vec<usize> = self.arena.indices().collect();
        for idx in all_indices {
            if !self.arena.is_active(idx) {
                continue;
            }
            if self.is_reason_clause_marked(idx) {
                continue;
            }
            if self.clause_satisfied_at_level0(idx) {
                let _ = self.delete_clause_unchecked(idx, mutate::ReasonPolicy::Skip);
            }
        }
    }

    /// Check if a clause flush is due (CaDiCaL reduce.cpp:26-30).
    ///
    /// Flush is more aggressive than normal reduce: it marks ALL unused
    /// learned clauses as garbage regardless of tier. Triggered at
    /// geometrically growing conflict intervals (default 100K x 3^n).
    #[inline]
    fn flushing(&self) -> bool {
        self.num_conflicts >= self.cold.next_flush
    }

    /// Aggressive clause flush: mark all unused learned clauses as garbage.
    ///
    /// Ports CaDiCaL `mark_clauses_to_be_flushed()` (reduce.cpp:34-58).
    /// Unlike normal reduce (which sorts candidates and deletes the worst 75%),
    /// flush evaluates each clause individually:
    /// - Core (glue <= tier1): survives if `used > 0` (any recent usage)
    /// - Tier1 (tier1 < glue <= tier2): survives if `used >= MAX_USED - 1` (very recent)
    /// - Tier2 (glue > tier2): unconditionally marked as garbage
    ///
    /// Does NOT update `kept_glue`/`kept_size` (CaDiCaL reduce.cpp:57 comment).
    fn mark_clauses_to_be_flushed(&mut self) -> Vec<usize> {
        let mut to_flush = Vec::new();

        let all_indices: Vec<usize> = self.arena.indices().collect();
        for idx in all_indices {
            if !self.arena.is_active(idx) {
                continue;
            }
            if !self.arena.is_learned(idx) {
                continue;
            }
            if self.is_reason_clause_marked(idx) {
                continue;
            }

            // CaDiCaL reduce.cpp:44-46: save pre-decrement value, then decay.
            let used = self.arena.used(idx);
            self.arena.decay_used(idx);

            // CaDiCaL reduce.cpp:47-52: hyper resolvents have one-round
            // lifetime in both flush and normal paths.
            if self.arena.is_hyper(idx) {
                debug_assert!(self.arena.len_of(idx) <= 3);
                if used == 0 {
                    to_flush.push(idx);
                }
                continue;
            }

            // Permanent protection for glue<=2 clauses during flush.
            // Same rationale as normal reduce: these are too valuable to delete.
            if self.arena.lbd(idx) <= CORE_LBD {
                continue;
            }

            match self.clause_tier(idx) {
                ClauseTier::Core => {
                    // Core clauses survive flush if they had recent usage
                    if used > 0 {
                        continue;
                    }
                }
                ClauseTier::Tier1 => {
                    // Tier1 needs very recent usage to survive flush
                    if used >= crate::clause_arena::MAX_USED - 1 {
                        continue;
                    }
                }
                ClauseTier::Tier2 => {
                    // Tier2 clauses never survive flush
                }
            }

            to_flush.push(idx);
        }
        to_flush
    }

    /// Propagate out-of-order level-0 units before reduce.
    ///
    /// After chronological backtracking, some level-0 units may be assigned
    /// at higher positions in the trail. This function detects them, backtracks
    /// to level 0, and re-propagates to derive all implied units.
    ///
    /// Reference: CaDiCaL reduce.cpp:172-192
    ///
    /// Returns true if no conflict, false if UNSAT at level 0.
    fn propagate_out_of_order_units(&mut self) -> bool {
        if self.decision_level == 0 {
            return true;
        }
        let start = if self.trail_lim.is_empty() {
            0
        } else {
            self.trail_lim[0]
        };
        let mut found_oou = false;
        for i in start..self.trail.len() {
            let lit = self.trail[i];
            if self.var_data[lit.variable().index()].level == 0 {
                found_oou = true;
                break;
            }
        }
        if !found_oou {
            return true;
        }
        self.backtrack(0);
        self.search_propagate().is_none()
    }

    /// Reduce the learned clause database using tier-based management.
    ///
    /// When a flush is due (`num_conflicts >= next_flush`), uses the aggressive
    /// flush path that marks ALL unused clauses as garbage regardless of tier
    /// (CaDiCaL reduce.cpp:34-58). Otherwise, uses the normal sort-and-delete
    /// path that removes the worst 75% of tier-2 candidates.
    ///
    /// Normal-mode three-tiered approach based on LBD:
    /// - CORE (LBD <= tier1): Protected if any recent usage (used > 0)
    /// - TIER1 (tier1 < LBD <= tier2): Protected if very recently bumped (used >= MAX_USED-1)
    /// - TIER2 (LBD > tier2): Always enters sort pool, deleted based on (glue, size) ranking
    ///
    /// Deletion scoring uses CaDiCaL's `reduce_less_useful` comparator (#5132):
    /// higher glue is deleted first, with size as tiebreak. Activity plays no
    /// role -- per Audemard & Simon (IJCAI'09), LBD alone is the best predictor
    /// of learned clause quality.
    pub(super) fn reduce_db(&mut self) {
        // CaDiCaL reduce.cpp:223: propagate out-of-order units first.
        if self.chrono_enabled && !self.propagate_out_of_order_units() {
            self.has_empty_clause = true;
            return;
        }
        self.cold.num_reductions += 1;
        self.ensure_reason_clause_marks_current();

        let flush = self.flushing();
        if flush {
            self.set_diagnostic_pass(DiagnosticPass::Flush);
            self.cold.num_flushes += 1;
        } else {
            self.set_diagnostic_pass(DiagnosticPass::Reduce);
        }

        self.mark_satisfied_clauses_as_garbage();

        if flush {
            // Aggressive flush path (CaDiCaL reduce.cpp:34-58)
            let to_flush = self.mark_clauses_to_be_flushed();

            #[cfg(debug_assertions)]
            {
                for &idx in &to_flush {
                    debug_assert!(
                        !self.is_reason_clause_marked(idx),
                        "BUG: flush candidate {idx} is a reason clause -- would corrupt trail"
                    );
                    debug_assert!(
                        self.arena.is_learned(idx),
                        "BUG: flush candidate {idx} is irredundant (not learned)"
                    );
                }
            }

            let trace_deleted_clause_ids: Vec<u64> = to_flush
                .iter()
                .map(|&idx| {
                    let clause_ref = ClauseRef(idx as u32);
                    let clause_id = self.clause_id(clause_ref);
                    if clause_id == 0 {
                        (idx as u64) + 1
                    } else {
                        clause_id
                    }
                })
                .collect();

            for &idx in &to_flush {
                let _ = self.delete_clause_unchecked(idx, mutate::ReasonPolicy::Skip);
            }
            if !trace_deleted_clause_ids.is_empty() {
                self.trace_reduce(trace_deleted_clause_ids);
            }

            // Flush does NOT update kept_glue/kept_size
            // (CaDiCaL reduce.cpp:57: "No change to 'lim.kept{size,glue}'")
        } else {
            // Normal reduce path: sort candidates and delete worst 75%

            // First pass: decay usage counters and collect deletable clause indices
            let mut tier2_clauses: Vec<usize> = Vec::new();

            let all_indices: Vec<usize> = self.arena.indices().collect();
            for idx in all_indices {
                if !self.arena.is_active(idx) {
                    continue;
                }
                if !self.arena.is_learned(idx) {
                    continue;
                }
                if self.is_reason_clause_marked(idx) {
                    continue;
                }

                // CaDiCaL reduce.cpp:109-111: save used BEFORE decrement,
                // check against pre-decrement value for tier protection.
                let used = self.arena.used(idx);
                self.arena.decay_used(idx);

                // CaDiCaL reduce.cpp:116-120: hyper resolvents (HBR/HTR)
                // have one-round lifetime. If unused, delete immediately;
                // otherwise keep but never enter the sort pool.
                if self.arena.is_hyper(idx) {
                    debug_assert!(self.arena.len_of(idx) <= 3);
                    if used == 0 {
                        let _ = self.delete_clause_unchecked(idx, mutate::ReasonPolicy::Skip);
                    }
                    continue;
                }

                // Permanent protection for glue<=2 clauses (CaDiCaL: "keep" tier).
                // These are the highest-quality learned clauses — nearly always
                // useful. CaDiCaL never deletes clauses with glue <= 2 in reduce.
                if self.arena.lbd(idx) <= CORE_LBD {
                    continue;
                }

                match self.clause_tier(idx) {
                    ClauseTier::Core => {
                        // CaDiCaL reduce.cpp:112: Core clauses with any recent
                        // usage are protected. Unused Core (used=0) become
                        // deletion candidates — prevents unbounded Core growth.
                        if used > 0 {
                            continue;
                        }
                        tier2_clauses.push(idx);
                    }
                    ClauseTier::Tier1 => {
                        // CaDiCaL reduce.cpp:114: Tier1 requires very recent
                        // usage (bumped in the current reduce interval) to
                        // survive. Less aggressive than Core (any usage).
                        if used >= crate::clause_arena::MAX_USED - 1 {
                            continue;
                        }
                        tier2_clauses.push(idx);
                    }
                    ClauseTier::Tier2 => {
                        // CaDiCaL reduce.cpp:122: Tier2 always enters the
                        // sort pool — no usage-based protection.
                        tier2_clauses.push(idx);
                    }
                }
            }

            // CaDiCaL reduce.cpp:74-82 `reduce_less_useful`: sort by (glue DESC,
            // size DESC). Higher glue = less useful = sorted first = deleted first.
            // No activity involvement -- pure structural quality metric (#5132).
            tier2_clauses.sort_by(|&a, &b| {
                let a_glue = self.arena.lbd(a);
                let b_glue = self.arena.lbd(b);
                match b_glue.cmp(&a_glue) {
                    std::cmp::Ordering::Equal => {
                        let a_size = self.arena.len_of(a) as u32;
                        let b_size = self.arena.len_of(b) as u32;
                        b_size.cmp(&a_size)
                    }
                    other => other,
                }
            });

            // CaDiCaL `reducetarget=75`: delete 75% of candidates.
            let num_to_delete =
                ((tier2_clauses.len() as u128 * REDUCE_TARGET_PERCENT as u128) / 100) as usize;

            debug_assert!(
                num_to_delete <= tier2_clauses.len(),
                "BUG: num_to_delete ({num_to_delete}) exceeds candidates ({})",
                tier2_clauses.len()
            );

            // Pre-deletion invariant: no candidate is a reason clause.
            #[cfg(debug_assertions)]
            {
                for &idx in tier2_clauses.iter().take(num_to_delete) {
                    debug_assert!(
                        !self.is_reason_clause_marked(idx),
                        "BUG: reduce_db candidate {idx} is a reason clause -- would corrupt trail"
                    );
                    debug_assert!(
                        self.arena.is_learned(idx),
                        "BUG: reduce_db candidate {idx} is irredundant (not learned)"
                    );
                }
            }

            let to_delete: Vec<usize> = tier2_clauses.iter().copied().take(num_to_delete).collect();
            let trace_deleted_clause_ids: Vec<u64> = to_delete
                .iter()
                .map(|&idx| {
                    let clause_ref = ClauseRef(idx as u32);
                    let clause_id = self.clause_id(clause_ref);
                    if clause_id == 0 {
                        (idx as u64) + 1
                    } else {
                        clause_id
                    }
                })
                .collect();

            // Mark clauses deleted. Watch entries are flushed eagerly below
            // (CaDiCaL reduce.cpp:232 garbage_collection pattern).
            for &idx in &to_delete {
                let _ = self.delete_clause_unchecked(idx, mutate::ReasonPolicy::Skip);
            }
            if !trace_deleted_clause_ids.is_empty() {
                self.trace_reduce(trace_deleted_clause_ids);
            }

            // Track maximum glue and size among kept (not deleted) candidates.
            // CaDiCaL reduce.cpp:147-157: feeds likely_to_be_kept_clause for subsumption.
            self.tiers.kept_glue = 0;
            self.tiers.kept_size = 0;
            for &idx in tier2_clauses.iter().skip(num_to_delete) {
                let glue = self.arena.lbd(idx);
                let size = self.arena.literals(idx).len() as u32;
                if glue > self.tiers.kept_glue {
                    self.tiers.kept_glue = glue;
                }
                if size > self.tiers.kept_size {
                    self.tiers.kept_size = size;
                }
            }
        }

        // Post-deletion invariant: no reason clause was deleted (shared by both paths).
        // After backtrack store elimination (#6991), unassigned variables retain
        // stale reason values. Only assigned variables have valid reason refs.
        #[cfg(debug_assertions)]
        {
            for (var_idx, vd) in self.var_data.iter().enumerate() {
                if is_clause_reason(vd.reason) && self.var_is_assigned(var_idx) {
                    let idx = vd.reason as usize;
                    debug_assert!(
                        self.arena.is_active(idx),
                        "BUG: reduce_db deleted reason clause {idx} for variable {var_idx}"
                    );
                }
            }
        }

        // CaDiCaL reduce.cpp:232 calls garbage_collection() which includes
        // flush_all_occs_and_watches(). Eagerly flush stale watch entries for
        // deleted clauses instead of letting BCP check is_dead() per watcher.
        self.flush_watches();

        // Arena locality compaction (CaDiCaL arenatype=3, #8030).
        // Reorder clauses in VMTF decision-queue order for cache locality.
        // Only fires when dead space exceeds 25% of arena size.
        if self.should_compact_arena() {
            self.compact_arena_locality();
        }

        // Schedule next reduction (CaDiCaL reduce.cpp:234-258, reduceopt=1).
        // delta = reduceint * sqrt(conflicts), with large-formula scaling.
        let factor = (self.num_conflicts as f64).sqrt().max(1.0);
        let mut delta = (REDUCE_DB_INC as f64 * factor) as u64;
        if self.num_original_clauses > 100_000 {
            let scale = (self.num_original_clauses as f64 / 1e4).log10();
            delta = (delta as f64 * scale) as u64;
        }
        delta = delta.max(1);
        self.cold.next_reduce_db = self.num_conflicts.saturating_add(delta);

        debug_assert!(
            self.cold.next_reduce_db >= self.num_conflicts,
            "BUG: reduce_db scheduled in the past: next={} < current={}",
            self.cold.next_reduce_db,
            self.num_conflicts
        );

        // Update flush schedule (CaDiCaL reduce.cpp:261-268)
        if flush {
            self.cold.flush_inc = self.cold.flush_inc.saturating_mul(FLUSH_FACTOR);
            self.cold.next_flush = self.num_conflicts.saturating_add(self.cold.flush_inc);
        }

        // Recompute dynamic tier boundaries if scheduled
        if self.num_conflicts >= self.tiers.next_recompute_tier {
            self.recompute_tier();
        }
    }
}
