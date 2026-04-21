// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Post-analysis variable bumping for VSIDS/VMTF activity management.
//!
//! Separated from the 1UIP analysis loop to keep the hot conflict-analysis
//! path focused on resolution, while activity updates write to VSIDS/VMTF
//! data structures in a separate cache-friendly pass.

use super::*;
use crate::literal::{Literal, Variable};

impl Solver {
    /// Update the EMA of decisions-per-conflict for bumpreason rate limiting.
    /// CaDiCaL analyze.cpp:924-929: tracks how many decisions occurred between
    /// consecutive conflicts. High decision rates mean the solver is exploring
    /// widely, and reason bumping adds VSIDS noise rather than focus.
    pub(super) fn update_bumpreason_decision_rate(&mut self) {
        let decisions_this_conflict = self
            .num_decisions
            .saturating_sub(self.cold.bumpreason_saved_decisions);
        self.cold.bumpreason_saved_decisions = self.num_decisions;
        // EMA with alpha = 2/(1e5+1) = 0.00002, matching CaDiCaL emadecisions=1e5.
        const ALPHA: f64 = 2.0 / 100_001.0;
        self.cold.bumpreason_decision_rate +=
            ALPHA * (decisions_this_conflict as f64 - self.cold.bumpreason_decision_rate);
    }

    /// Bump all analyzed variables after the analysis loop.
    ///
    /// Deferring bumps from the analysis loop to a separate pass improves
    /// cache behavior: the analysis loop reads trail/reason data, while
    /// bumping writes to VSIDS/VMTF data structures. Separating these
    /// avoids cache pollution during the latency-sensitive analysis loop.
    ///
    /// CHB score updates are only performed when the MAB selector is active
    /// (`MabUcb1`) or CHB is the fixed heuristic. In `LegacyCoupled` mode
    /// (EVSIDS+VMTF only, the default for single-thread search), CHB
    /// updates are skipped entirely to eliminate per-conflict floating-point
    /// overhead and L1 cache pollution from scattered `chb_scores` writes.
    pub(super) fn bump_analyzed_variables(&mut self) {
        let analyzed = self.conflict.analyzed_vars();

        // CHB score updates: only when the MAB or fixed-CHB mode needs them.
        // In LegacyCoupled mode (the default), CHB is never used, so updating
        // its scores on every conflict is pure overhead (#8091).
        let chb_active = matches!(
            self.cold.branch_selector_mode,
            BranchSelectorMode::MabUcb1 | BranchSelectorMode::Fixed(BranchHeuristic::Chb)
        );
        if chb_active {
            for &idx in analyzed {
                self.vsids.chb_bump(Variable(idx as u32));
            }
            self.vsids.chb_on_conflict();
        }

        match self.active_branch_heuristic {
            BranchHeuristic::Evsids => {
                for &idx in analyzed {
                    self.vsids.bump(Variable(idx as u32), &self.vals, true);
                }
            }
            BranchHeuristic::Chb => {
                // CHB is active and the heap already orders by CHB scores
                // (swapped into activities). Keep dormant EVSIDS scores warm
                // so MAB switching does not start from stale data.
                for &idx in analyzed {
                    self.vsids.bump_evsids_score_dormant(Variable(idx as u32));
                }
            }
            BranchHeuristic::Vmtf => {
                self.bump_sort_buf.clear();
                self.bump_sort_buf.extend_from_slice(analyzed);
                {
                    let vsids = &self.vsids;
                    self.bump_sort_buf
                        .sort_unstable_by_key(|&idx| vsids.bump_order(Variable(idx as u32)));
                }
                for &idx in &self.bump_sort_buf {
                    self.vsids.bump(Variable(idx as u32), &self.vals, false);
                }
            }
        }
    }

    /// Bump reason literals for improved VSIDS focus (CaDiCaL's bumpreason).
    ///
    /// This bumps variables in the reason clauses of the literals in the learned
    /// clause. The intuition is that these variables are "important" because they
    /// contributed to the conflict, even if they're not directly in the learned clause.
    ///
    /// Gated by CaDiCaL's adaptive rate-limiting (analyze.cpp:384-424):
    /// 1. Decision rate guard: skip if decisions/conflict EMA > 100
    /// 2. Adaptive delay: when bumping wastes work, delay re-enabling
    ///
    /// Parameters (from CaDiCaL):
    /// - Depth limit: 1 (focused) or 2 (stable) - how deep to recurse into reasons
    /// - Analyzed limit: 10x the number of analyzed literals - prevent blowup
    pub(super) fn bump_reason_literals(&mut self) {
        // CaDiCaL analyze.cpp:388: rate limit -- skip when decision rate is too high.
        // bumpreasonrate default = 100 (options.hpp:42).
        const BUMPREASON_RATE_LIMIT: f64 = 100.0;
        if self.cold.bumpreason_decision_rate > BUMPREASON_RATE_LIMIT {
            return;
        }

        // CaDiCaL analyze.cpp:393-398: adaptive delay -- skip while delay counter > 0.
        // Per-mode indexing matches CaDiCaL's delay[stable].bumpreasons.
        let mode = usize::from(self.stable_mode);
        if self.cold.bumpreason_delay_remaining[mode] > 0 {
            self.cold.bumpreason_delay_remaining[mode] -= 1;
            return;
        }

        // Get literals in the learned clause (including UIP)
        let uip = self.conflict.asserting_literal();
        // Use index-based access to avoid allocation from to_vec()
        let learned_count = self.conflict.learned_count();

        // CaDiCaL analyze.cpp:399-400: depth limit must be positive.
        // CaDiCaL: bumpreasondepth(1) + stable -> 1 (focused), 2 (stable).
        let depth_limit = if self.stable_mode { 2 } else { 1 };
        debug_assert!(depth_limit > 0, "BUG: bump reason depth limit is 0");

        // CaDiCaL analyze.cpp:401-402: save analyzed size before reason bumping.
        // Reason-side variables are added to the analyzed list (seen_to_clear) via
        // mark_seen(), then bumped together with all other analyzed variables in
        // bump_analyzed_variables(). We do NOT bump VSIDS directly here -- that
        // would cause double-bumping since bump_analyzed_variables iterates the
        // same seen_to_clear list.
        let saved_analyzed = self.conflict.analyzed_vars().len();
        let analyzed_limit = saved_analyzed * 10;
        let mut extra_added = 0;

        // Add reason-side variables for UIP first
        self.add_reason_literals_to_analyzed(
            uip.negated(),
            depth_limit,
            &mut extra_added,
            analyzed_limit,
        );

        // Add reason literals for each literal in the learned clause
        for i in 0..learned_count {
            if extra_added >= analyzed_limit {
                break;
            }
            let lit = self.conflict.learned_at(i);
            self.add_reason_literals_to_analyzed(
                lit.negated(),
                depth_limit,
                &mut extra_added,
                analyzed_limit,
            );
        }

        // CaDiCaL analyze.cpp:408-423: adaptive delay hysteresis + rollback.
        let limit_exceeded = extra_added >= analyzed_limit;
        if limit_exceeded {
            // Rollback: clear seen flags for all reason-side variables added
            // and truncate the analyzed list back to its saved size.
            // CaDiCaL analyze.cpp:410-417: clears f.seen and resizes analyzed.
            self.conflict
                .rollback_analyzed(saved_analyzed, &mut self.var_data);
            self.cold.bumpreason_delay_interval[mode] += 1;
        } else {
            self.cold.bumpreason_delay_interval[mode] /= 2;
        }
        self.cold.bumpreason_delay_remaining[mode] = self.cold.bumpreason_delay_interval[mode];
    }

    /// Add reason-side literals to the analyzed set for later bumping.
    ///
    /// CaDiCaL analyze.cpp:342-381 (bump_also_reason_literal + bump_also_reason_literals).
    /// Variables are marked as seen (added to analyzed_vars) but NOT bumped directly.
    /// The actual VSIDS/VMTF bump happens in bump_analyzed_variables() which processes
    /// the full analyzed list with correct sort ordering.
    pub(super) fn add_reason_literals_to_analyzed(
        &mut self,
        lit: Literal,
        depth: u32,
        extra_added: &mut usize,
        limit: usize,
    ) {
        if depth == 0 || *extra_added >= limit {
            return;
        }

        let var_idx = lit.variable().index();

        // Get the reason clause for this literal
        let Some(reason_ref) = self.var_reason(var_idx) else {
            return; // Decision or unit - no reason clause
        };

        // CaDiCaL analyze.cpp:364: literal for reason bumping must be assigned
        debug_assert!(
            self.var_is_assigned(var_idx),
            "BUG: bump_reason_literals for unassigned var {var_idx}",
        );

        // Traverse reason clause and add unseen variables to analyzed list
        let clause_idx = reason_ref.0 as usize;
        let clause_len = self.arena.len_of(clause_idx);

        // CaDiCaL analyze.cpp:370: charge one search tick per reason clause traversal
        self.search_ticks[usize::from(self.stable_mode)] += 1;

        for i in 0..clause_len {
            let reason_lit = self.arena.literal(clause_idx, i);
            if reason_lit == lit {
                continue; // Skip the propagated literal itself
            }

            // CaDiCaL analyze.cpp:344: reason literal must be assigned false
            debug_assert!(
                self.lit_val(reason_lit) < 0,
                "BUG: reason literal {reason_lit:?} for var={var_idx} is not false (val={})",
                self.lit_val(reason_lit),
            );

            let reason_var_idx = reason_lit.variable().index();

            // CaDiCaL analyze.cpp:346-351: skip if already seen or level 0
            if self.conflict.is_seen(reason_var_idx, &self.var_data) {
                continue;
            }
            if self.var_data[reason_var_idx].level == 0 {
                continue;
            }

            // Mark as seen -- adds to analyzed_vars (seen_to_clear) for later
            // bumping in bump_analyzed_variables(). No direct VSIDS bump here.
            self.conflict.mark_seen(reason_var_idx, &mut self.var_data);
            *extra_added += 1;

            // Recurse if we have depth remaining
            if depth > 1 && *extra_added < limit {
                self.add_reason_literals_to_analyzed(
                    reason_lit.negated(),
                    depth - 1,
                    extra_added,
                    limit,
                );
            }
        }
    }
}
