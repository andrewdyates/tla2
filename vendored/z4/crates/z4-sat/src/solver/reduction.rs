// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause database reduction and activity management.

use super::*;

// Clause deletion scoring removed in favor of CaDiCaL's pure (glue, size)
// comparator (#5132). Activity plays no role in deletion decisions -- only LBD
// and clause size determine usefulness, per Audemard & Simon (IJCAI'09).
// Reference: CaDiCaL reduce.cpp:74-82 `reduce_less_useful`.

impl Solver {
    /// Classify a clause using the current dynamic tier boundaries.
    #[inline]
    pub(super) fn clause_tier(&self, clause_idx: usize) -> ClauseTier {
        let lbd = self.arena.lbd(clause_idx);
        // CaDiCaL reduce.cpp:97-98: always use focused-mode boundaries (index 0)
        // for clause tier classification, regardless of current mode.
        if lbd <= self.tiers.tier1_lbd[0] {
            ClauseTier::Core
        } else if lbd <= self.tiers.tier2_lbd[0] {
            ClauseTier::Tier1
        } else {
            ClauseTier::Tier2
        }
    }

    /// Predict whether a clause will survive the next `reduce_db`.
    ///
    /// Ports CaDiCaL `likely_to_be_kept_clause` (internal.hpp:1059-1069).
    /// Irredundant clauses are always kept. Learned clauses in tier1/tier2
    /// (glue <= tier2_lbd) are always kept. Tier3 clauses are kept only if
    /// their glue and size are within the thresholds from the last reduction.
    ///
    /// Used to gate `subsume_dirty` marking (#3727): variables in clauses
    /// that won't survive reduce_db should not trigger subsumption work.
    #[inline]
    pub(super) fn likely_to_be_kept(&self, clause_idx: usize) -> bool {
        if !self.arena.is_learned(clause_idx) {
            return true;
        }
        let lbd = self.arena.lbd(clause_idx);
        if lbd <= self.tiers.tier2_lbd[0] {
            return true;
        }
        lbd <= self.tiers.kept_glue
            && (self.arena.len_of(clause_idx) as u32) <= self.tiers.kept_size
    }

    /// Mark variables in a clause as subsume-dirty if the clause is likely to
    /// survive the next `reduce_db`.
    ///
    /// CaDiCaL clause.cpp:140: `if (likely_to_be_kept_clause(c)) mark_added(c)`.
    /// Must be called AFTER `set_lbd()` for learned clauses — the predicate
    /// depends on the actual LBD, not the arena default of 0 (#3727).
    #[inline]
    pub(super) fn mark_subsume_dirty_if_kept(&mut self, clause_idx: usize) {
        if !self.likely_to_be_kept(clause_idx) {
            return;
        }
        for &lit in self.arena.literals(clause_idx) {
            let v = lit.variable().index();
            if v < self.subsume_dirty.len() {
                self.subsume_dirty[v] = true;
            }
        }
    }

    /// Bump a clause during conflict analysis (CaDiCaL analyze.cpp:225-240).
    ///
    /// For every antecedent clause encountered during 1UIP analysis:
    /// 1. Set `used` to maximum (protects from deletion)
    /// 2. For learned clauses: recompute glue from current assignment and
    ///    promote to a higher tier if the glue decreased
    /// 3. Track per-glue usage for dynamic tier boundary recomputation
    ///
    /// Clause activity plays no role in deletion decisions (#5132) -- only LBD
    /// and clause size determine usefulness per CaDiCaL's `reduce_less_useful`.
    pub(super) fn bump_clause(&mut self, clause_ref: ClauseRef) {
        let clause_idx = clause_ref.0 as usize;

        debug_assert!(
            self.arena.is_active(clause_idx),
            "BUG: bump_clause called on inactive/deleted clause {clause_idx}"
        );

        // (1) Set used to maximum (CaDiCaL: c->used = max_used = 31)
        self.arena
            .set_used(clause_idx, crate::clause_arena::MAX_USED);

        // (2) Recompute glue and promote for learned clauses
        if !self.arena.is_learned(clause_idx) || self.arena.is_empty_clause(clause_idx) {
            return;
        }
        let old_lbd = self.arena.lbd(clause_idx);
        let new_lbd = self.recompute_glue(clause_idx);
        if new_lbd < old_lbd {
            self.arena.set_lbd(clause_idx, new_lbd);
        }

        // Stored LBD only decreases (CaDiCaL analyze.cpp:230-233).
        // If new_lbd >= old_lbd we keep old_lbd, so the invariant holds.
        debug_assert!(
            self.arena.lbd(clause_idx) <= old_lbd,
            "BUG: bump_clause increased stored LBD from {old_lbd} to {} for clause {clause_idx}",
            self.arena.lbd(clause_idx)
        );

        // (3) Track per-glue usage (CaDiCaL analyze.cpp:237-239)
        let glue = self.arena.lbd(clause_idx);
        let mode = usize::from(self.stable_mode);
        let bucket = (glue as usize).min(self.tiers.tier_usage[mode].len() - 1);
        self.tiers.tier_usage[mode][bucket] += 1;
        self.tiers.tier_bump_total[mode] += 1;
    }

    /// Recompute the glue (LBD) of a clause from the current assignment.
    ///
    /// Counts the number of distinct decision levels among the clause's
    /// assigned literals. Uses a stamp table for O(clause_size) performance
    /// with no clearing overhead (CaDiCaL analyze.cpp:206-219).
    pub(super) fn recompute_glue(&mut self, clause_idx: usize) -> u32 {
        debug_assert!(
            self.arena.is_active(clause_idx),
            "BUG: recompute_glue called on inactive clause {clause_idx}"
        );

        if self.glue_stamp_counter == u32::MAX {
            self.glue_stamp.fill(0);
            self.glue_stamp_counter = 0;
        }
        self.glue_stamp_counter += 1;
        let stamp = self.glue_stamp_counter;
        let mut count = 0u32;
        let clause_len = self.arena.len_of(clause_idx);
        for i in 0..clause_len {
            let lit = self.arena.literal(clause_idx, i);
            let var_idx = lit.variable().index();
            // CaDiCaL analyze.cpp:210: every literal must be assigned
            // during glue recomputation. An unassigned literal would
            // produce level[var] from a prior assignment, yielding a
            // wrong glue value.
            debug_assert!(
                self.var_is_assigned(var_idx),
                "BUG: recompute_glue: literal {lit:?} (var={var_idx}) in clause {clause_idx} is unassigned",
            );
            let lvl = self.var_data[var_idx].level as usize;
            // Grow stamp table if needed (can happen with added variables)
            if lvl >= self.glue_stamp.len() {
                self.glue_stamp.resize(lvl + 1, 0);
            }
            if self.glue_stamp[lvl] != stamp {
                self.glue_stamp[lvl] = stamp;
                count += 1;
            }
        }

        // LBD must be >= 1 for non-empty clauses (at least one decision level)
        // and <= clause_len (at most one distinct level per literal).
        debug_assert!(
            clause_len == 0 || (count >= 1 && count as usize <= clause_len),
            "BUG: recompute_glue returned {count} for clause {clause_idx} with {clause_len} literals"
        );

        count
    }

    /// Check if we should reduce the clause database
    pub(super) fn should_reduce_db(&self) -> bool {
        // Suppressed during backbone probing (#7929): prevent clause deletion
        // from invalidating the DRAT proof chain for backbone units.
        if self.suppress_reduce_db {
            return false;
        }
        // Regular interval-based reduction
        if self.num_conflicts >= self.cold.next_reduce_db {
            return true;
        }
        // Aggressive reduction if clause limit exceeded (#1609)
        if let Some(limit) = self.cold.max_learned_clauses {
            // clause_db.len() is an upper bound on learned clauses (includes deleted slots)
            // This is cheaper than counting non-deleted learned clauses
            if self.arena.num_clauses() > self.num_original_clauses + limit {
                return true;
            }
        }
        // Aggressive reduction if clause DB byte limit exceeded (#1609)
        if let Some(limit) = self.cold.max_clause_db_bytes {
            if self.arena.memory_bytes() > limit {
                return true;
            }
        }
        false
    }

    /// Poll the process-wide memory limit on the shared conflict cadence.
    ///
    /// This reuses the solver's interrupt path so long-running SAT search can
    /// stop cleanly with `Unknown` once the shared z4-core memory gate trips (#6552).
    #[inline]
    pub(super) fn poll_process_memory_limit(&mut self) {
        if self.cold.process_memory_interrupt {
            return;
        }
        if !self
            .num_conflicts
            .is_multiple_of(PROCESS_MEMORY_CHECK_INTERVAL)
        {
            return;
        }
        self.cold.process_memory_interrupt = z4_core::term::TermStore::global_memory_exceeded();
    }

    /// Signal that reason edges changed; next `ensure` will rebuild marks (#3518).
    ///
    /// Hot-path writes (for example from `enqueue`) can call this repeatedly
    /// before a rebuild. Once marks are already dirty (`synced != graph`), keep
    /// the epoch stable to avoid extra cache-line churn in propagation.
    #[inline]
    pub(super) fn bump_reason_graph_epoch(&mut self) {
        if self.reason_marks_synced_epoch == self.reason_graph_epoch {
            self.reason_graph_epoch = self.reason_graph_epoch.wrapping_add(1);
        }
    }

    /// Rebuild reason clause marks only if the reason graph changed (#3518).
    #[inline]
    pub(super) fn ensure_reason_clause_marks_current(&mut self) {
        if self.reason_marks_synced_epoch == self.reason_graph_epoch {
            return;
        }
        self.refresh_reason_clause_marks();
        self.reason_marks_synced_epoch = self.reason_graph_epoch;
    }
    /// Rebuild clause-indexed reason markers unconditionally. Prefer `ensure_reason_clause_marks_current()`.
    pub(super) fn refresh_reason_clause_marks(&mut self) {
        if self.reason_clause_epoch == u32::MAX {
            self.reason_clause_marks.fill(0);
            self.reason_clause_epoch = 1;
        } else {
            self.reason_clause_epoch += 1;
        }

        if self.reason_clause_marks.len() < self.arena.len() {
            self.reason_clause_marks.resize(self.arena.len(), 0);
        }

        let epoch = self.reason_clause_epoch;
        for (vi, vd) in self.var_data.iter().enumerate() {
            if is_clause_reason(vd.reason) && self.var_is_assigned(vi) {
                let idx = vd.reason as usize;
                if idx < self.reason_clause_marks.len() {
                    self.reason_clause_marks[idx] = epoch;
                }
            }
        }

        // Post-condition: every trail reason clause is marked in the current epoch.
        // A missed reason would allow reduce_db to delete a clause still needed
        // by the trail, corrupting conflict analysis.
        #[cfg(debug_assertions)]
        {
            for (vi, vd) in self.var_data.iter().enumerate() {
                if is_clause_reason(vd.reason) && self.var_is_assigned(vi) {
                    let idx = vd.reason as usize;
                    debug_assert!(
                        self.is_reason_clause_marked(idx),
                        "BUG: trail reason clause {idx} not marked after refresh_reason_clause_marks"
                    );
                }
            }
        }
    }

    /// Check whether a clause is marked as a current reason in the active epoch.
    #[inline]
    pub(super) fn is_reason_clause_marked(&self, clause_idx: usize) -> bool {
        clause_idx < self.reason_clause_marks.len()
            && self.reason_clause_marks[clause_idx] == self.reason_clause_epoch
    }

    /// Recompute dynamic tier boundaries from per-glue usage statistics.
    ///
    /// Ports CaDiCaL `recompute_tier()` (tier.cpp:7-81):
    /// - tier1 = glue where accumulated usage reaches TIER1_LIMIT_PCT% of total
    /// - tier2 = glue where accumulated usage reaches TIER2_LIMIT_PCT%
    /// - Floors: tier1 >= 1, tier2 > tier1
    /// - Exponential backoff scheduling up to 2^16 conflicts
    pub(super) fn recompute_tier(&mut self) {
        self.tiers.tier_recomputed += 1;

        // Schedule next recomputation with exponential backoff (CaDiCaL tier.cpp:12-14)
        let delta = if self.tiers.tier_recomputed >= 16 {
            1u64 << 16
        } else {
            1u64 << self.tiers.tier_recomputed
        };
        self.tiers.next_recompute_tier = self.num_conflicts.saturating_add(delta);

        let mode = usize::from(self.stable_mode);
        let total = self.tiers.tier_bump_total[mode];

        // If no usage data yet, keep defaults (CaDiCaL tier.cpp:25-30)
        if total == 0 {
            self.tiers.tier1_lbd[mode] = CORE_LBD;
            self.tiers.tier2_lbd[mode] = TIER1_LBD;
            debug_assert!(
                self.tiers.tier2_lbd[mode] > self.tiers.tier1_lbd[mode],
                "BUG: default tier constants violate ordering: CORE_LBD={CORE_LBD} >= TIER1_LBD={TIER1_LBD}"
            );
            return;
        }

        // Compute tier1 boundary: glue where accumulated usage >= tier1limit%
        let tier1_target = total * TIER1_LIMIT_PCT / 100;
        let tier2_target = total * TIER2_LIMIT_PCT / 100;

        let usage = &self.tiers.tier_usage[mode];
        let mut new_tier1 = 1u32;
        let mut new_tier2 = 1u32;
        let mut accumulated = usage[0];

        // Find tier1 boundary
        let mut glue = 1usize;
        while glue < usage.len() {
            accumulated += usage[glue];
            if accumulated >= tier1_target {
                new_tier1 = glue as u32;
                break;
            }
            glue += 1;
        }

        // Find tier2 boundary (continue from where tier1 left off).
        // CaDiCaL tier.cpp:48 also starts tier2 from the same glue value
        // as tier1 break — the double-count is intentional (overlapping
        // cumulative thresholds, not exclusive partitions).
        while glue < usage.len() {
            accumulated += usage[glue];
            if accumulated >= tier2_target {
                new_tier2 = glue as u32;
                break;
            }
            glue += 1;
        }

        // Floor enforcement: tier1 >= 1, tier2 > tier1 (CaDiCaL tier.cpp:63-74)
        if new_tier1 < 1 {
            new_tier1 = 1;
        }
        if new_tier2 < 1 {
            new_tier2 = 1;
        }
        if new_tier1 >= new_tier2 {
            new_tier2 = new_tier1 + 1;
        }

        self.tiers.tier1_lbd[mode] = new_tier1;
        self.tiers.tier2_lbd[mode] = new_tier2;

        // Post-condition: tier boundaries are well-ordered for this mode
        // (CaDiCaL tier.cpp:63-74 floor enforcement).
        debug_assert!(
            self.tiers.tier1_lbd[mode] >= 1,
            "BUG: tier1_lbd[{mode}] ({}) < 1 after recompute_tier",
            self.tiers.tier1_lbd[mode]
        );
        debug_assert!(
            self.tiers.tier2_lbd[mode] > self.tiers.tier1_lbd[mode],
            "BUG: tier2_lbd[{mode}] ({}) <= tier1_lbd[{mode}] ({}) after recompute_tier",
            self.tiers.tier2_lbd[mode],
            self.tiers.tier1_lbd[mode]
        );
    }
}
